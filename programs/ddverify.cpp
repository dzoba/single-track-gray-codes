// Streaming check of the Degni-Drisko property DD(p): in the BRGC g(t) = t ^ (t>>1), t = 1..2^p-2, the first
// occurrences of the nonconstant necklaces (no rotation has smaller BRGC rank) form a path in the necklace flip graph:
// consecutive first occurrences are adjacent (some rotation of one is at Hamming distance 1 from the other).
// Also checks: the count is (2^p-2)/p, the first is 0..01 and the last is 01^{p-1} (Lemma 0).
// O(1) memory per thread; chunks of the rank range in parallel; boundary pairs checked after.
// Progress is printed per completed chunk to stdout (flushed) so a long run can be followed.
// Checkpointing: with a 4th argument, every finished chunk's summary is appended (and fsync'ed) to that file; on
// restart with the same p and chunk count, finished chunks are loaded and skipped. The check logic is unchanged.
// Pruning: ranks t >= 2^(p-1) give words starting with 1; such a word is never a first occurrence of a nonconstant
// necklace (some rotation starts with 0 and has rank < 2^(p-1) <= t), so those ranks are skipped.
// Usage: ddverify p threads [chunks] [checkpoint_file]
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <mutex>
#include <unistd.h>
#include <thread>
#include <vector>

typedef uint64_t u64;
static int p; static u64 MASK;
static inline u64 ginv(u64 g) { g ^= g >> 1; g ^= g >> 2; g ^= g >> 4; g ^= g >> 8; g ^= g >> 16; g ^= g >> 32; return g; }
static inline bool isFirst(u64 g, u64 t) {
    u64 x = g;
    for (int k = 1; k < p; ++k) { x = ((x << 1) | (x >> (p - 1))) & MASK; if (ginv(x) < t) return false; }
    return true;
}
static inline bool adjacent(u64 u, u64 v) {
    u64 x = v;
    for (int k = 0; k < p; ++k) { u64 y = u ^ x; if (y && !(y & (y - 1))) return true; x = ((x << 1) | (x >> (p - 1))) & MASK; }
    return false;
}
struct Res { u64 first = 0, last = 0, count = 0, bad = 0, badT = 0; bool done = false; };
int main(int argc, char** argv) {
    p = atoi(argv[1]); int T = atoi(argv[2]); int NC = argc > 3 ? atoi(argv[3]) : 4096;
    MASK = (1ULL << p) - 1;
    auto T0 = std::chrono::steady_clock::now();
    auto secs = [&]() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - T0).count(); };
    u64 lo = 1, hi = (1ULL << (p - 1)) - 1;   // see "Pruning" above
    std::vector<Res> R(NC); std::atomic<int> next(0), finished(0); std::mutex io;
    const char* ckpt = argc > 4 ? argv[4] : nullptr;
    FILE* ck = nullptr;
    struct Rec { int32_t p, nc, c, pad; u64 first, last, count, bad, badT; };
    if (ckpt) {
        int loaded = 0;
        if (FILE* in = fopen(ckpt, "rb")) {
            Rec rec;
            while (fread(&rec, sizeof rec, 1, in) == 1) {
                if (rec.p != p || rec.nc != NC || rec.c < 0 || rec.c >= NC) { fprintf(stderr, "checkpoint mismatch\n"); return 2; }
                Res& r = R[rec.c]; r.first = rec.first; r.last = rec.last; r.count = rec.count; r.bad = rec.bad; r.badT = rec.badT;
                if (!r.done) { r.done = true; ++loaded; }
            }
            fclose(in);
        }
        // drop a torn trailing record (kill during a write) so new records stay aligned
        {
            FILE* in = fopen(ckpt, "rb");
            if (in) { fseek(in, 0, SEEK_END); long sz = ftell(in); fclose(in);
                      long whole = sz - sz % (long)sizeof(Rec); if (whole != sz) truncate(ckpt, whole); }
        }
        finished = loaded;
        printf("checkpoint %s: %d/%d chunks already done\n", ckpt, loaded, NC); fflush(stdout);
        ck = fopen(ckpt, "ab");
    }
    auto work = [&]() {
        for (;;) {
            int c = next++; if (c >= NC) break;
            if (R[c].done) continue;
            u64 a = lo + (u64)((__uint128_t)(hi - lo + 1) * c / NC), z = lo + (u64)((__uint128_t)(hi - lo + 1) * (c + 1) / NC);
            Res& r = R[c]; u64 prev = 0; bool have = false;
            for (u64 t = a; t < z; ++t) {
                u64 g = t ^ (t >> 1);
                if (g == MASK || g == 0 || !isFirst(g, t)) continue;
                if (have) { if (!adjacent(prev, g)) { if (!r.bad) r.badT = t; ++r.bad; } }
                else { r.first = g; have = true; }
                prev = g; ++r.count;
            }
            r.last = prev; r.done = true;
            if (ck) {
                std::lock_guard<std::mutex> lk(io);
                Rec rec{p, NC, c, 0, r.first, r.last, r.count, r.bad, r.badT};
                fwrite(&rec, sizeof rec, 1, ck); fflush(ck); fsync(fileno(ck));
            }
            int f = ++finished;
            if (f % (NC / 64 > 0 ? NC / 64 : 1) == 0) { std::lock_guard<std::mutex> lk(io); printf("progress %d/%d chunks, %.0fs\n", f, NC, secs()); fflush(stdout); }
        }
    };
    std::vector<std::thread> th; for (int i = 0; i < T; ++i) th.emplace_back(work); for (auto& x : th) x.join();
    if (ck) fclose(ck);
    for (auto& r : R) if (!r.done) { printf("incomplete chunks remain\n"); return 3; }
    u64 L = 0, bad = 0, firstW = 0, lastW = 0, prevLast = 0; bool started = false;
    for (auto& r : R) {
        L += r.count; bad += r.bad;
        if (!r.count) continue;
        if (started) { if (!adjacent(prevLast, r.first)) ++bad; } else { firstW = r.first; started = true; }
        prevLast = r.last; lastW = r.last;
    }
    u64 expect = (MASK - 1) / p, E0 = MASK >> 1;   // 0 1^{p-1}
    bool ok = bad == 0 && L == expect && firstW == 1 && lastW == E0;
    printf("p=%d L=%llu expected=%llu nonadjacent_pairs=%llu first=0..01:%d last=01^{p-1}:%d -> DD(%d) %s  (%.0fs)\n", p,
           (unsigned long long)L, (unsigned long long)expect, (unsigned long long)bad, firstW == 1, lastW == E0, p,
           ok ? "HOLDS" : "FAILS", secs());
    return ok ? 0 : 1;
}
