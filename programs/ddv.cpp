// ddv.cpp -- independent streaming checker for the Degni-Drisko property DD(p).
//
// Usage: ./ddv p threads [full|selftest]
// Checkpointing (added by the main session; check logic unchanged): if the environment variable DDV_CKPT names a
// file, each finished chunk's Summary is appended and fsync'ed there; on restart with the same p and chunk count,
// finished chunks are loaded and skipped. A torn trailing record is trimmed.
//
// D_p: nonconstant necklaces (rotation classes of p-bit words) ordered by the
// smallest t with g(t) = t ^ (t>>1) in the class.  DD(p): every two consecutive
// necklaces of D_p have words at Hamming distance 1.
//
// First-occurrence test (derived here):
//   Gray rank of a word w is the inverse Gray code b, b_i = XOR_{j>=i} w_j.
//   If r = rotl1(w) (r_i = w_{i-1}, r_0 = w_{p-1}), then for i >= 1
//     rank(r)_i = XOR_{j>=i} r_j = XOR_{j=i-1}^{p-2} w_j = b_{i-1} ^ w_{p-1},
//   and rank(r)_0 = parity(r) = parity(w) = b_0.  So the ranks of all p
//   rotations follow from b in O(1) each.  t is the first occurrence of its
//   necklace iff no rotation has a strictly smaller rank.
//   Pruning: if t >= 2^(p-1) then w = g(t) has top bit 1; unless w = 1^p, some
//   rotation of w has top bit 0 and therefore rank < 2^(p-1) <= t.  So only
//   t in [1, 2^(p-1)) can be first occurrences of nonconstant necklaces
//   (t = 0 gives 0^p).  Mode "full" scans all t anyway as a cross-check.
//
// Parallelism: the rank range is cut into chunks; each chunk produces a
// summary (count, first word, last word, internal non-adjacent pairs, an
// order-sensitive hash).  Chunks are merged in order, checking the pair
// (last of chunk k, first of the next nonempty chunk).

#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <cstring>
#include <vector>
#include <thread>
#include <atomic>
#include <unistd.h>
#include <cstdlib>
#include <mutex>
#include <chrono>
#include <algorithm>

typedef uint64_t u64;
static int P;
static u64 MASK;
static const u64 HB = 0x9E3779B97F4A7C15ULL;  // hash base (odd)

static inline u64 rotl1(u64 w) { return ((w << 1) & MASK) | (w >> (P - 1)); }

// is t the smallest Gray rank in the rotation class of g(t)?
static inline bool is_first(u64 t) {
    u64 w = t ^ (t >> 1);
    u64 b = t;
    for (int k = 1; k < P; k++) {
        u64 s = (w >> (P - 1)) & 1;
        u64 b0 = b & 1;
        b = (((b << 1) & MASK) ^ (s ? (MASK ^ 1ULL) : 0ULL)) | b0;
        w = rotl1(w);
        if (b < t) return false;
    }
    return true;
}

// some rotation of a at Hamming distance exactly 1 from b?
static inline bool adjacent(u64 a, u64 b) {
    u64 r = a;
    for (int k = 0; k < P; k++) {
        if (__builtin_popcountll(r ^ b) == 1) return true;
        r = rotl1(r);
    }
    return false;
}

struct Summary {
    u64 count = 0, first = 0, last = 0, bad = 0;
    u64 hash = 0, pw = 1;  // hash = sum w_i * HB^(n-1-i); pw = HB^n
    u64 ex_a = 0, ex_b = 0;  // first bad pair inside the chunk
    bool done = false;
};

static void add_word(Summary &S, u64 w, std::vector<std::pair<u64,u64>> *badlist) {
    if (S.count == 0) S.first = w;
    else if (!adjacent(S.last, w)) {
        if (S.bad == 0) { S.ex_a = S.last; S.ex_b = w; }
        S.bad++;
        if (badlist) badlist->push_back({S.last, w});
    }
    S.last = w;
    S.count++;
    S.hash = S.hash * HB + w;
    S.pw *= HB;
}

static void merge(Summary &A, const Summary &B, std::vector<std::pair<u64,u64>> *badlist) {
    if (B.count == 0) return;
    if (A.count == 0) { A = B; return; }
    if (!adjacent(A.last, B.first)) {
        if (A.bad == 0) { A.ex_a = A.last; A.ex_b = B.first; }
        A.bad++;
        if (badlist) badlist->push_back({A.last, B.first});
    }
    if (A.bad == 0 && B.bad > 0) { A.ex_a = B.ex_a; A.ex_b = B.ex_b; }
    A.bad += B.bad;
    A.count += B.count;
    A.last = B.last;
    A.hash = A.hash * B.pw + B.hash;
    A.pw *= B.pw;
}

static void bits(u64 w, char *buf) {
    for (int i = 0; i < P; i++) buf[i] = ((w >> (P - 1 - i)) & 1) ? '1' : '0';
    buf[P] = 0;
}

// naive reference for small p: canonical = min rotation, bitset of seen classes
static Summary naive(std::vector<std::pair<u64,u64>> *badlist) {
    Summary S;
    std::vector<uint8_t> seen((size_t)1 << P, 0);
    for (u64 t = 0; t <= MASK; t++) {
        u64 w = t ^ (t >> 1);
        if (w == 0 || w == MASK) continue;
        u64 c = w, r = w;
        for (int k = 1; k < P; k++) { r = rotl1(r); if (r < c) c = r; }
        if (seen[c]) continue;
        seen[c] = 1;
        add_word(S, w, badlist);
    }
    return S;
}

int main(int argc, char **argv) {
    if (argc < 3) { fprintf(stderr, "usage: %s p threads [full|selftest]\n", argv[0]); return 2; }
    P = atoi(argv[1]);
    int T = atoi(argv[2]);
    bool full = argc > 3 && !strcmp(argv[3], "full");
    bool selftest = argc > 3 && !strcmp(argv[3], "selftest");
    if (P < 2 || P > 62 || T < 1) { fprintf(stderr, "bad args\n"); return 2; }
    MASK = (P == 64) ? ~0ULL : ((1ULL << P) - 1);

    u64 lo = 1, hi = full ? (MASK + 1) : (1ULL << (P - 1));  // scan t in [lo, hi)
    u64 span = hi - lo;
    u64 nchunks = std::min<u64>(span, 65536);
    if (P >= 36) nchunks = 1 << 18;  // 2^(p-19) ranks per chunk
    if (nchunks > span) nchunks = span;
    std::vector<Summary> sums(nchunks);
    bool keep_bad = P <= 24;
    std::vector<std::vector<std::pair<u64,u64>>> badl(keep_bad ? nchunks : 0);

    auto t0 = std::chrono::steady_clock::now();
    printf("ddv: p=%d threads=%d scan t in [%llu, %llu) chunks=%llu%s\n", P, T,
           (unsigned long long)lo, (unsigned long long)hi, (unsigned long long)nchunks,
           full ? " (full)" : "");
    fflush(stdout);

    std::atomic<u64> next(0), finished(0);
    std::mutex mu;
    struct CkRec { uint32_t p, pad; u64 nch, c, count, first, last, bad, hash, pw, ex_a, ex_b; };
    const char *ckpath = getenv("DDV_CKPT");
    FILE *ck = nullptr;
    if (ckpath) {
        u64 loaded = 0;
        if (FILE *in = fopen(ckpath, "rb")) {
            CkRec r;
            while (fread(&r, sizeof r, 1, in) == 1) {
                if ((int)r.p != P || r.nch != nchunks || r.c >= nchunks) { fprintf(stderr, "checkpoint mismatch\n"); return 2; }
                Summary &S = sums[r.c];
                if (!S.done) ++loaded;
                S.count = r.count; S.first = r.first; S.last = r.last; S.bad = r.bad; S.hash = r.hash; S.pw = r.pw;
                S.ex_a = r.ex_a; S.ex_b = r.ex_b; S.done = true;
            }
            fseek(in, 0, SEEK_END); long sz = ftell(in); fclose(in);
            long whole = sz - sz % (long)sizeof(CkRec);
            if (whole != sz) truncate(ckpath, whole);
        }
        finished = loaded;
        printf("checkpoint %s: %llu/%llu chunks already done\n", ckpath, (unsigned long long)loaded, (unsigned long long)nchunks);
        fflush(stdout);
        ck = fopen(ckpath, "ab");
    }
    u64 report_every = std::max<u64>(1, nchunks / 64);
    auto worker = [&]() {
        for (;;) {
            u64 c = next.fetch_add(1);
            if (c >= nchunks) break;
            if (sums[c].done) continue;
            u64 a = lo + (unsigned __int128)span * c / nchunks;
            u64 b = lo + (unsigned __int128)span * (c + 1) / nchunks;
            Summary S;
            auto *bl = keep_bad ? &badl[c] : nullptr;
            for (u64 t = a; t < b; t++) {
                if (!is_first(t)) continue;
                u64 w = t ^ (t >> 1);
                if (w == 0 || w == MASK) continue;
                add_word(S, w, bl);
            }
            S.done = true;
            sums[c] = S;
            if (ck) {
                std::lock_guard<std::mutex> g(mu);
                CkRec r{(uint32_t)P, 0, nchunks, c, S.count, S.first, S.last, S.bad, S.hash, S.pw, S.ex_a, S.ex_b};
                fwrite(&r, sizeof r, 1, ck); fflush(ck); fsync(fileno(ck));
            }
            u64 f = finished.fetch_add(1) + 1;
            if (f % report_every == 0 || f == nchunks) {
                double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();
                std::lock_guard<std::mutex> g(mu);
                printf("progress %llu/%llu chunks (%.1f%%) elapsed %.1fs eta %.1fs\n",
                       (unsigned long long)f, (unsigned long long)nchunks, 100.0 * f / nchunks, el,
                       el * (double)(nchunks - f) / f);
                fflush(stdout);
            }
        }
    };
    std::vector<std::thread> th;
    for (int i = 0; i < T; i++) th.emplace_back(worker);
    for (auto &x : th) x.join();
    if (ck) fclose(ck);
    for (u64 c = 0; c < nchunks; c++) if (!sums[c].done) { printf("incomplete chunks remain\n"); return 3; }

    Summary tot;
    std::vector<std::pair<u64,u64>> allbad;
    for (u64 c = 0; c < nchunks; c++) {
        // the boundary pair is recorded via merge; chunk-internal pairs via badl
        std::vector<std::pair<u64,u64>> bnd;
        merge(tot, sums[c], keep_bad ? &bnd : nullptr);
        if (keep_bad) {
            allbad.insert(allbad.end(), bnd.begin(), bnd.end());
            allbad.insert(allbad.end(), badl[c].begin(), badl[c].end());
        }
    }
    double el = std::chrono::duration<double>(std::chrono::steady_clock::now() - t0).count();

    // expected necklace count via Burnside: (1/p) sum_{d|p} phi(d) 2^(p/d) - 2
    unsigned __int128 bs = 0;
    for (int d = 1; d <= P; d++) if (P % d == 0) {
        int ph = 0; for (int k = 1; k <= d; k++) { int a = k, b = d; while (b) { int r = a % b; a = b; b = r; } if (a == 1) ph++; }
        bs += (unsigned __int128)ph << (P / d);
    }
    u64 expect = (u64)(bs / P) - 2;

    char b1[70], b2[70];
    bits(tot.first, b1); bits(tot.last, b2);
    printf("RESULT p=%d necklaces=%llu expected=%llu %s\n", P, (unsigned long long)tot.count,
           (unsigned long long)expect, tot.count == expect ? "count-OK" : "COUNT-MISMATCH");
    printf("first necklace word %s\nlast  necklace word %s\n", b1, b2);
    printf("nonadjacent consecutive pairs: %llu\n", (unsigned long long)tot.bad);
    printf("wraparound pair (last,first) adjacent: %s\n", adjacent(tot.last, tot.first) ? "yes" : "no");
    printf("sequence hash %016llx\n", (unsigned long long)tot.hash);
    if (tot.bad) {
        if (keep_bad) {
            int shown = 0;
            for (auto &pr : allbad) { if (shown++ >= 20) break; bits(pr.first, b1); bits(pr.second, b2); printf("  bad pair %s %s\n", b1, b2); }
        } else { bits(tot.ex_a, b1); bits(tot.ex_b, b2); printf("  first bad pair %s %s\n", b1, b2); }
    }
    printf("DD(%d) %s  time %.2fs\n", P, (tot.bad == 0 && tot.count == expect) ? "HOLDS" : "FAILS", el);
    fflush(stdout);

    if (selftest) {
        if (P > 26) { printf("selftest skipped (p>26)\n"); return 0; }
        std::vector<std::pair<u64,u64>> nb;
        Summary N = naive(&nb);
        bool ok = N.count == tot.count && N.hash == tot.hash && N.first == tot.first && N.last == tot.last && N.bad == tot.bad;
        printf("selftest naive: count=%llu hash=%016llx bad=%llu -> %s\n", (unsigned long long)N.count,
               (unsigned long long)N.hash, (unsigned long long)N.bad, ok ? "MATCH" : "MISMATCH");
        if (!ok) return 1;
    }
    return 0;
}
