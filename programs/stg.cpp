// Optimal single-track Gray codes for prime n via a Hamilton cycle on nonconstant binary necklaces.
//
// Q: vertices = nonconstant n-bit necklaces (m = (2^n-2)/n of them for prime n), edge A-B when a one-bit flip of a
// word of A lands in B. A Hamilton cycle in Q, lifted along actual words, returns to rot^s(start); if s != 0 mod n,
// repeating the m flips n times (each pass shifted by s) is a single-track Gray code of period 2^n - 2.
//
// Search: start from a seed path (Degni-Drisko BRGC sublist, or greedy Warnsdorff), extend it, then Posa
// rotations (at either end) until it covers every vertex and closes with a nonzero total voltage.
//
// Usage: stg n seed_kind(brgc|greedy) rng_seed max_seconds out_prefix
// Writes out_prefix.track (P bytes, '0'/'1' = column 0), out_prefix.heads (n head offsets), out_prefix.json.
#include <algorithm>
#include <chrono>
#include <cstdint>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <random>
#include <string>
#include <vector>

static int n;
static uint32_t MASK;
static inline uint32_t rotl1(uint32_t w) { return ((w << 1) | (w >> (n - 1))) & MASK; }
// canonical = min rotation; k with w = rot^k(canon)
static inline uint32_t canon(uint32_t w, int* k) {
    uint32_t best = w, x = w;
    int bk = 0;
    for (int j = 1; j < n; ++j) {
        x = rotl1(x);  // x = rot^j(w)  => w = rot^{n-j}(x)
        if (x < best) { best = x; bk = (n - j) % n; }
    }
    *k = bk;
    return best;
}
static inline uint32_t rotk(uint32_t w, int k) {
    k %= n; if (k < 0) k += n;
    if (!k) return w;
    return ((w << k) | (w >> (n - k))) & MASK;
}

#pragma pack(push, 1)
struct Edge { int32_t to; int8_t bit; int8_t volt; };
#pragma pack(pop)
static std::vector<uint32_t> reps;          // sorted canonical reps
static std::vector<int64_t> off;             // CSR offsets into edges
static std::vector<Edge> edges;
static inline int idOf(uint32_t c) {
    auto it = std::lower_bound(reps.begin(), reps.end(), c);
    if (it == reps.end() || *it != c) return -1;
    return int(it - reps.begin());
}

static double now() {
    using namespace std::chrono;
    return duration<double>(steady_clock::now().time_since_epoch()).count();
}

int main(int argc, char** argv) {
    if (argc < 6) { fprintf(stderr, "usage: stg n brgc|greedy seed seconds out\n"); return 2; }
    n = atoi(argv[1]);
    std::string seedKind = argv[2];
    uint64_t rseed = strtoull(argv[3], 0, 10);
    double maxSec = atof(argv[4]);
    std::string out = argv[5];
    MASK = (n == 32) ? 0xffffffffu : ((1u << n) - 1);
    double t0 = now();
    std::mt19937_64 rng(rseed);

    for (uint32_t w = 1; w < MASK; ++w) {
        uint32_t x = w; bool mn = true;
        for (int j = 1; j < n; ++j) { x = rotl1(x); if (x < w) { mn = false; break; } }
        if (mn) reps.push_back(w);
    }
    int m = int(reps.size());
    if ((uint64_t)m * n != (uint64_t)MASK - 1) { fprintf(stderr, "n not prime? m=%d\n", m); return 1; }
    off.assign(m + 1, 0);
    for (int a = 0; a < m; ++a) {
        off[a] = int64_t(edges.size());
        for (int i = 0; i < n; ++i) {
            uint32_t w = reps[a] ^ (1u << i);
            if (w == 0 || w == MASK) continue;
            int k; uint32_t c = canon(w, &k);
            edges.push_back({idOf(c), int8_t(i), int8_t(k)});
        }
    }
    off[m] = int64_t(edges.size());
    fprintf(stderr, "n=%d m=%d edges=%zu built in %.2fs\n", n, m, edges.size(), now() - t0);

    // ---- path state
    std::vector<int> P; P.reserve(m);
    std::vector<int> pos(m, -1);
    auto push = [&](int v) { pos[v] = int(P.size()); P.push_back(v); };

    if (seedKind == "brgc") {
        // Degni-Drisko: first representative of each necklace in BRGC order (constants dropped).
        std::vector<char> seen(m, 0);
        for (uint64_t t = 0; t <= MASK; ++t) {
            uint32_t g = uint32_t(t ^ (t >> 1));
            if (g == 0 || g == MASK) continue;
            int k; int c = idOf(canon(g, &k));
            if (!seen[c]) { seen[c] = 1; push(c); }
        }
        // keep only the longest prefix whose consecutive necklaces are adjacent in Q (it should be all of it)
        int good = 1;
        for (; good < (int)P.size(); ++good) {
            int a = P[good - 1], b = P[good]; bool adj = false;
            for (int64_t e = off[a]; e < off[a + 1]; ++e) if (edges[e].to == b) { adj = true; break; }
            if (!adj) break;
        }
        fprintf(stderr, "brgc sublist: %zu necklaces, adjacent prefix %d\n", P.size(), good);
        for (int i = good; i < (int)P.size(); ++i) pos[P[i]] = -1;
        P.resize(good);
    } else {
        push(int(rng() % m));
    }

    // ---- extend + Posa rotations
    auto reverseRange = [&](int i, int j) {  // reverse P[i..j]
        while (i < j) { std::swap(P[i], P[j]); pos[P[i]] = i; pos[P[j]] = j; ++i; --j; }
    };
    auto unvisitedDeg = [&](int v) {
        int d = 0; for (int64_t e = off[v]; e < off[v + 1]; ++e) if (pos[edges[e].to] < 0) ++d; return d;
    };
    long rotations = 0, lastReport = 0;
    std::vector<char> nbrStart(m, 0);
    int startMarkFor = -1;
    double lastT = now();
    int bestLen = int(P.size());
    while (true) {
        if (now() - t0 > maxSec) { fprintf(stderr, "timeout at length %zu/%d\n", P.size(), m); return 3; }
        int L = int(P.size());
        if (L > bestLen) bestLen = L;
        int e = P[L - 1];
        // extend at the end (Warnsdorff: unvisited neighbour with fewest unvisited neighbours, random ties)
        int bestV = -1, bestD = 1 << 30;
        for (int64_t k = off[e]; k < off[e + 1]; ++k) {
            int u = edges[k].to;
            if (pos[u] >= 0) continue;
            int d = unvisitedDeg(u) * 64 + int(rng() % 64);
            if (d < bestD) { bestD = d; bestV = u; }
        }
        if (bestV >= 0) { push(bestV); continue; }
        if (L == m) {
            // closure: endpoint adjacent to start?
            int s0 = P[0];
            bool adj = false;
            for (int64_t k = off[e]; k < off[e + 1]; ++k) if (edges[k].to == s0) { adj = true; break; }
            if (adj) {
                // lift and choose parallel edges so total voltage != 0
                // collect, for each step, the set of voltages available
                long total = 0;
                std::vector<int64_t> choice(m);  // edge index used at step t (from P[t] to P[(t+1)%m])
                for (int t = 0; t < m; ++t) {
                    int a = P[t], b = P[(t + 1) % m];
                    for (int64_t k = off[a]; k < off[a + 1]; ++k) if (edges[k].to == b) { choice[t] = k; break; }
                    total += edges[choice[t]].volt;
                }
                int s = int(total % n);
                if (s == 0) {
                    bool fixed = false;
                    for (int t = 0; t < m && !fixed; ++t) {
                        int a = P[t], b = P[(t + 1) % m];
                        for (int64_t k = off[a]; k < off[a + 1]; ++k)
                            if (edges[k].to == b && edges[k].volt != edges[choice[t]].volt) {
                                total += edges[k].volt - edges[choice[t]].volt; choice[t] = k; fixed = true; break;
                            }
                    }
                    s = int(((total % n) + n) % n);
                    if (!fixed) { fprintf(stderr, "cycle with zero voltage and no parallel edge; rotating on\n"); }
                }
                if (s != 0) {
                    // expand: transition bits on actual words, first pass
                    std::vector<int> bits(m);
                    int o = 0;
                    for (int t = 0; t < m; ++t) {
                        const Edge& E = edges[choice[t]];
                        bits[t] = (E.bit + o) % n;
                        o = (o + E.volt) % n;
                    }
                    // o == s now; full code: word sequence over P = n*m steps
                    uint64_t Pp = (uint64_t)m * n;
                    std::vector<char> track(Pp);
                    std::vector<uint64_t> seen((uint64_t(MASK) + 64) / 64, 0);
                    uint32_t w = reps[P[0]];
                    bool ok = true;
                    // heads: col_{ks}(t) = col_0(t - k m)  =>  head of column (k s mod n) is -k m mod P
                    std::vector<long> heads(n);
                    for (int k = 0; k < n; ++k) heads[(long)k * s % n] = (long)(((int64_t)Pp - (int64_t)k * m) % (int64_t)Pp);
                    for (uint64_t t = 0; t < Pp; ++t) {
                        if (w == 0 || w == MASK || (seen[w >> 6] >> (w & 63) & 1)) ok = false;
                        seen[w >> 6] |= 1ull << (w & 63);
                        track[t] = char('0' + (w & 1));
                        int pass = int(t / m);
                        int b = (bits[t % m] + pass * s) % n;
                        w ^= (1u << b);
                    }
                    if (w != reps[P[0]]) ok = false;
                    // single-track spot check on 1e6 positions (full independent check is check.py / check.c)
                    std::mt19937_64 r2(99);
                    {
                        uint32_t ww = reps[P[0]];
                        for (uint64_t t = 0; t < std::min<uint64_t>(Pp, 2000000) && ok; ++t) {
                            for (int j = 0; j < n; ++j)
                                if (((ww >> j) & 1) != uint32_t(track[(t + heads[j]) % Pp] - '0')) { ok = false; break; }
                            int pass = int(t / m);
                            ww ^= (1u << ((bits[t % m] + pass * s) % n));
                        }
                    }
                    fprintf(stderr, "CYCLE n=%d s=%d rotations=%ld self-check %s (%.1fs)\n", n, s, rotations,
                            ok ? "PASS" : "FAIL", now() - t0);
                    FILE* f = fopen((out + ".track").c_str(), "wb"); fwrite(track.data(), 1, Pp, f); fclose(f);
                    f = fopen((out + ".heads").c_str(), "w");
                    for (int j = 0; j < n; ++j) fprintf(f, "%ld\n", heads[j]);
                    fclose(f);
                    f = fopen((out + ".json").c_str(), "w");
                    fprintf(f, "{\"n\": %d, \"period\": %llu, \"necklaces\": %d, \"shift\": %d, \"start\": %u, "
                               "\"rotations\": %ld, \"seed_kind\": \"%s\", \"rng_seed\": %llu, \"self_check\": \"%s\"}\n",
                            n, (unsigned long long)Pp, m, s, reps[P[0]], rotations, seedKind.c_str(),
                            (unsigned long long)rseed, ok ? "PASS" : "FAIL");
                    fclose(f);
                    return ok ? 0 : 1;
                }
            }
        }
        // Posa rotation at the end: pick a path neighbour x = P[j] of e (j < L-2), reverse P[j+1..L-1].
        // Pivot choice. When the path covers everything, first look one rotation ahead: a pivot x = P[j] whose
        // successor P[j+1] is adjacent to the start closes the cycle at once. Otherwise prefer the pivot nearest
        // the end (short reversal) half the time, a random one otherwise.
        int bestJ = -1;
        if (L == m) {
            if (startMarkFor != P[0]) {
                std::fill(nbrStart.begin(), nbrStart.end(), 0);
                for (int64_t k = off[P[0]]; k < off[P[0] + 1]; ++k) nbrStart[edges[k].to] = 1;
                startMarkFor = P[0];
            }
            for (int64_t k = off[e]; k < off[e + 1]; ++k) {
                int j = pos[edges[k].to];
                if (j >= 0 && j < L - 2 && nbrStart[P[j + 1]]) { bestJ = j; break; }
            }
        }
        if (bestJ < 0) {
            bool nearest = rng() & 1;
            int deg = int(off[e + 1] - off[e]);
            if (nearest) {
                for (int64_t k = off[e]; k < off[e + 1]; ++k) {
                    int j = pos[edges[k].to];
                    if (j >= 0 && j < L - 2 && j > bestJ) bestJ = j;
                }
            } else {
                for (int tries = 0; tries < 4 && bestJ < 0; ++tries) {
                    int j = pos[edges[off[e] + int(rng() % deg)].to];
                    if (j >= 0 && j < L - 2) bestJ = j;
                }
            }
        }
        if (bestJ < 0) {
            // also allow rotating at the start by reversing the whole path occasionally
            if ((rng() & 15) == 0) reverseRange(0, L - 1);
            continue;
        }
        reverseRange(bestJ + 1, L - 1);
        ++rotations;
        if ((rng() & 1023) == 0) reverseRange(0, L - 1);  // let both ends work
        if (now() - lastT > 10) {
            fprintf(stderr, "  len %d/%d (best %d) rotations %ld (%.0fs)\n", L, m, bestLen, rotations, now() - t0);
            lastT = now(); lastReport = rotations;
        }
    }
}
