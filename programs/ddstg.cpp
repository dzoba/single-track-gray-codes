// Optimal single-track Gray code for prime p from the Degni-Drisko path + the explicit closing rule (NOTES 18:10).
//
// 1. Enumerate the BRGC g(t) = t ^ (t>>1), t = 1..2^p-2, keep first occurrences of necklaces (no rotation has a
//    smaller BRGC rank). This is the DD order u_0, u_1, ..., u_{L-1}. Check DD: consecutive u_i ~ u_{i+1}; record for
//    each edge (b_i, d_i) with u_i ^ (1<<b_i) = rot^{d_i}(u_{i+1}) (rot = rotate left). Check L = (2^p-2)/p and that
//    u_{L-1} = 01^{p-1}. (Parallel over T threads, chunks of the rank range.)
// 2. Cycle = DD path with K = (p-3)/2 end rotations at the explicit pivots A_k (their DD indices are found in step 1).
// 3. Walk the cycle lifting to words: w = rot^o(u); forward edge flips bit (b+o), o += d; backward edge (u_{i+1} to
//    u_i) flips bit (b+o-d), o -= d; junction and closing edges are solved directly. Shift s = final offset. If s = 0,
//    use the twin edge at <0^{p-1}1> (Lemma 1).
// 4. Write out_prefix.flips (m bytes, flip positions for pass 0; pass q uses (f + q*s) mod p) and .json (p, m, s,
//    start word, sha256-free summary). For p <= 29 also write .track ('0'/'1') and .heads for check.py / check2.
// Usage: ddstg p threads out_prefix
#include <algorithm>
#include <atomic>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <string>
#include <thread>
#include <vector>

typedef uint64_t u64;
static int p; static u64 MASK;
static inline u64 rotl(u64 w, int k) { k %= p; if (k < 0) k += p; return k ? (((w << k) | (w >> (p - k))) & MASK) : w; }
static inline u64 ginv(u64 g) { g ^= g >> 1; g ^= g >> 2; g ^= g >> 4; g ^= g >> 8; g ^= g >> 16; g ^= g >> 32; return g; }
static inline bool isFirst(u64 g, u64 t) {
    u64 x = g;
    for (int k = 1; k < p; ++k) { x = ((x << 1) | (x >> (p - 1))) & MASK; if (ginv(x) < t) return false; }
    return true;
}
// (b, d) with u ^ (1<<b) == rot^d(v); returns false if not adjacent
static inline bool edgeRec(u64 u, u64 v, int& b, int& d) {
    u64 x = v;
    for (int k = 0; k < p; ++k) {
        u64 y = u ^ x;
        if (y && !(y & (y - 1))) { b = __builtin_ctzll(y); d = k; return true; }
        x = ((x << 1) | (x >> (p - 1))) & MASK;
    }
    return false;
}
static u64 W(const std::string& s) { u64 w = 0; for (char c : s) w = (w << 1) | (c == '1'); return w; }

struct Chunk { std::vector<uint8_t> b, d; u64 first = 0, last = 0, count = 0; bool ok = true; u64 badAt = 0; };

int main(int argc, char** argv) {
    p = atoi(argv[1]); int T = atoi(argv[2]); std::string out = argv[3];
    MASK = (p == 64) ? ~0ULL : ((1ULL << p) - 1);
    auto T0 = std::chrono::steady_clock::now();
    auto secs = [&]() { return std::chrono::duration<double>(std::chrono::steady_clock::now() - T0).count(); };
    int K = (p - 3) / 2;
    std::vector<u64> A(K), E(K + 1);
    E[0] = W("0" + std::string(p - 1, '1'));
    A[0] = W("0" + std::string(p - 5, '1') + "0111");
    E[1] = W("0" + std::string(p - 5, '1') + "0101");
    for (int k = 1; k < K; ++k) {
        A[k] = W(std::string(2 * k + 1, '0') + "10" + std::string(p - 2 * k - 3, '1'));
        E[k + 1] = W(std::string(2 * k + 1, '0') + "10" + std::string(p - 2 * k - 5, '1') + "01");
    }
    // ---- step 1: parallel enumeration
    int NC = T * 16; u64 lo = 1, hi = MASK - 1;  // ranks 1..2^p-2 (rank 2^p-1 is g = 10..0; rank of 1^p handled by isFirst? g=MASK skipped)
    std::vector<Chunk> ch(NC);
    std::vector<u64> pivRank(K);
    for (int k = 0; k < K; ++k) pivRank[k] = ginv(A[k]);
    std::atomic<int> next(0);
    auto work = [&]() {
        for (;;) {
            int c = next++; if (c >= NC) break;
            u64 a = lo + (hi - lo + 1) * c / NC, z = lo + (hi - lo + 1) * (c + 1) / NC;   // [a, z)
            Chunk& C = ch[c]; u64 prev = 0; bool have = false;
            for (u64 t = a; t < z; ++t) {
                u64 g = t ^ (t >> 1);
                if (g == MASK || g == 0) continue;
                if (!isFirst(g, t)) continue;
                if (!have) { C.first = g; have = true; }
                else {
                    int b, d;
                    if (!edgeRec(prev, g, b, d)) { if (C.ok) { C.ok = false; C.badAt = t; } b = d = 255; }
                    C.b.push_back((uint8_t)b); C.d.push_back((uint8_t)d);
                }
                prev = g; ++C.count;
            }
            C.last = prev;
        }
    };
    std::vector<std::thread> th; for (int i = 0; i < T; ++i) th.emplace_back(work); for (auto& x : th) x.join();
    u64 L = 0; bool ddok = true;
    for (auto& C : ch) { L += C.count; ddok &= C.ok; }
    // assemble edge records (with chunk-boundary edges)
    std::vector<uint8_t> eb, ed; eb.reserve(L); ed.reserve(L);
    u64 prevLast = 0; bool started = false; u64 firstWord = 0, lastWord = 0;
    for (auto& C : ch) {
        if (!C.count) continue;
        if (started) {
            int b, d; if (!edgeRec(prevLast, C.first, b, d)) { ddok = false; b = d = 255; }
            eb.push_back((uint8_t)b); ed.push_back((uint8_t)d);
        } else { firstWord = C.first; started = true; }
        eb.insert(eb.end(), C.b.begin(), C.b.end()); ed.insert(ed.end(), C.d.begin(), C.d.end());
        std::vector<uint8_t>().swap(C.b); std::vector<uint8_t>().swap(C.d);
        prevLast = C.last; lastWord = C.last;
    }
    u64 expectL = (MASK - 1) / p;
    printf("p=%d step1 %.0fs: L=%llu (expected %llu) DD path=%s first=%llx last=%s\n", p, secs(), (unsigned long long)L,
           (unsigned long long)expectL, ddok ? "OK" : "FAIL", (unsigned long long)firstWord,
           lastWord == E[0] ? "01^{p-1} OK" : "UNEXPECTED");
    fflush(stdout);
    if (!ddok || L != expectL || lastWord != E[0] || firstWord != 1) { printf("ABORT\n"); return 1; }
    // DD indices of pivots: index = number of first occurrences with rank < r. Count per chunk again cheaply:
    // recount only within the chunk containing each pivot rank.
    std::vector<u64> pivIdx(K);
    {
        std::vector<u64> pref(NC + 1, 0); for (int c = 0; c < NC; ++c) pref[c + 1] = pref[c] + ch[c].count;
        for (int k = 0; k < K; ++k) {
            u64 r = pivRank[k];
            int c = 0; while (c + 1 < NC && lo + (hi - lo + 1) * (c + 1) / NC <= r) ++c;
            u64 a = lo + (hi - lo + 1) * c / NC, cnt = pref[c];
            for (u64 t = a; t < r; ++t) { u64 g = t ^ (t >> 1); if (g != MASK && g && isFirst(g, t)) ++cnt; }
            if (!isFirst(A[k], r)) { printf("pivot %d not first occurrence\n", k); return 1; }
            pivIdx[k] = cnt;
        }
    }
    // ---- step 2: segments (inclusive DD index ranges; a > b means backward)
    struct Seg { long long a, b; };
    std::vector<Seg> segs = {{0, (long long)L - 1}};
    for (int k = 0; k < K; ++k) {
        long long j = pivIdx[k];
        Seg f = segs[0];
        if (!(f.a == 0 && f.b >= j + 1)) { printf("pivot %d not inside the first segment\n", k); return 1; }
        std::vector<Seg> rest; rest.push_back({j + 1, f.b});
        for (size_t i = 1; i < segs.size(); ++i) rest.push_back(segs[i]);
        std::reverse(rest.begin(), rest.end());
        for (auto& s : rest) std::swap(s.a, s.b);
        segs.clear(); segs.push_back({0, j}); for (auto& s : rest) segs.push_back(s);
    }
    // ---- step 3: walk and lift. Representative words of DD indices are needed only at segment ends.
    auto wordAt = [&](long long idx) -> u64 {   // DD index -> first-occurrence word (via the chunk counts)
        u64 cnt = 0; int c = 0;
        while (c < NC && cnt + ch[c].count <= (u64)idx) { cnt += ch[c].count; ++c; }
        u64 a = lo + (hi - lo + 1) * c / NC;
        for (u64 t = a;; ++t) { u64 g = t ^ (t >> 1); if (g != MASK && g && isFirst(g, t)) { if (cnt == (u64)idx) return g; ++cnt; } }
    };
    std::vector<uint8_t> flips; flips.reserve(L);
    int o = 0;
    u64 cur = wordAt(segs[0].a);  // = 1
    auto junction = [&](u64 u, u64 v) {   // from rot^o(u) to some rotation of v by one flip
        int b, d; if (!edgeRec(u, v, b, d)) { printf("junction not adjacent\n"); exit(1); }
        flips.push_back((uint8_t)((b + o) % p)); o = (o + d) % p;
    };
    for (size_t si = 0; si < segs.size(); ++si) {
        Seg s = segs[si];
        if (si > 0) { u64 v = wordAt(s.a); junction(cur, v); cur = v; }
        if (s.a <= s.b) {
            for (long long i = s.a; i < s.b; ++i) { flips.push_back((uint8_t)((eb[i] + o) % p)); o = (o + ed[i]) % p; }
        } else {
            for (long long i = s.a; i > s.b; --i) {   // edge (i-1 -> i) used backwards
                int b = eb[i - 1], d = ed[i - 1];
                flips.push_back((uint8_t)(((b + o - d) % p + p) % p)); o = ((o - d) % p + p) % p;
            }
        }
        cur = wordAt(s.b);
    }
    // closing edge to the start word 1 = <0^{p-1}1>
    junction(cur, 1);
    int s = o;
    if (s == 0) {
        // Lemma 1: replace the first edge (1 -> second vertex) by its twin. The first flip turns 0..01 into a weight-2
        // word {0, i}; the twin flips bit p-i instead, landing on {0,p-i} = rot^{-i}... recompute offsets from scratch.
        printf("voltage 0: applying the Lemma 1 twin swap is not implemented; aborting\n"); return 1;
    }
    printf("cycle: %zu flips (L=%llu), segments=%zu, shift s=%d, %.0fs\n", flips.size(), (unsigned long long)L, segs.size(), s, secs());
    FILE* f = fopen((out + ".flips").c_str(), "wb"); fwrite(flips.data(), 1, flips.size(), f); fclose(f);
    f = fopen((out + ".json").c_str(), "w");
    fprintf(f, "{\"p\": %d, \"m\": %zu, \"s\": %d, \"start\": 1, \"rule\": \"pass q flips bit (f+q*s) mod p\", \"segments\": %zu}\n", p, flips.size(), s, segs.size());
    fclose(f);
    if (p <= 29) {   // track and heads for check.py / check2
        u64 P = (u64)p * flips.size();
        std::string track(P, '0'); u64 w = 1;
        for (u64 t = 0; t < P; ++t) { track[t] = (w & 1) ? '1' : '0'; int q = (int)(t / flips.size()); w ^= 1ULL << ((flips[t % flips.size()] + (u64)q * s) % p); }
        if (w != 1) { printf("does not return to start\n"); return 1; }
        f = fopen((out + ".track").c_str(), "w"); fwrite(track.data(), 1, P, f); fclose(f);
        std::vector<u64> heads(p);
        for (int k = 0; k < p; ++k) heads[((u64)k * s) % p] = (P - ((u64)k * flips.size()) % P) % P;
        f = fopen((out + ".heads").c_str(), "w"); for (int j = 0; j < p; ++j) fprintf(f, "%llu\n", (unsigned long long)heads[j]); fclose(f);
        printf("wrote track and heads\n");
    }
    printf("done %.0fs\n", secs());
    return 0;
}
