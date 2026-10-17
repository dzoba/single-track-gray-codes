// Independent verifier for flip-sequence certificates of single-track Gray codes (written separately from ddstg).
// Certificate: prefix.flips (m bytes f_0..f_{m-1}), shift s, start word 1. Word sequence: w_0 = 1; in pass q
// (q = 0..p-1), step i flips bit (f_i + q*s) mod p. Hence w_{t+m} = rot^s(w_t) (rotate left by s), which makes column
// k*s mod p equal to column 0 delayed by k*m: a single-track code with equally spaced heads h_{ks} = -k*m.
// Checks: every f_i < p; P = p*m = 2^p - 2; all P words distinct (bitmap of 2^p bits) and nonconstant; the sequence
// returns to w_0 after P steps (cyclic, one bit per step by construction). Also checks, for each pass q, that its
// starting word equals rot^{q*s}(1) (consistency of the pass decomposition with the shift).
// Passes run in parallel threads; the bitmap uses atomic OR.
// Usage: vfy prefix p s threads
#include <pthread.h>
#include <stdatomic.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

static int p, s, T; static uint64_t m, MASK; static uint8_t* F; static _Atomic uint64_t* bm;
static _Atomic long long dups = 0, consts = 0; static uint64_t* endw;
static uint64_t rotl(uint64_t w, int k) { k %= p; return k ? (((w << k) | (w >> (p - k))) & MASK) : w; }
static void* run(void* arg) {
    long id = (long)arg;
    for (int q = (int)id; q < p; q += T) {
        uint64_t w = rotl(1, (int)(((long long)q * s) % p));
        long long d = 0, c = 0;
        for (uint64_t i = 0; i < m; ++i) {
            if (w == 0 || w == MASK) ++c;
            uint64_t bit = 1ULL << (w & 63);
            uint64_t old = atomic_fetch_or_explicit(&bm[w >> 6], bit, memory_order_relaxed);
            if (old & bit) ++d;
            w ^= 1ULL << ((F[i] + (uint64_t)q * s) % p);
        }
        endw[q] = w;
        dups += d; consts += c;
    }
    return 0;
}
int main(int argc, char** argv) {
    char path[4096]; p = atoi(argv[2]); s = atoi(argv[3]); T = atoi(argv[4]);
    MASK = (1ULL << p) - 1;
    snprintf(path, sizeof path, "%s.flips", argv[1]);
    FILE* f = fopen(path, "rb"); fseek(f, 0, SEEK_END); m = (uint64_t)ftell(f); fseek(f, 0, SEEK_SET);
    F = malloc(m); if (fread(F, 1, m, f) != m) { printf("read error\n"); return 2; } fclose(f);
    int badf = 0; for (uint64_t i = 0; i < m; ++i) if (F[i] >= p) badf = 1;
    uint64_t P = (uint64_t)p * m;
    bm = calloc((1ULL << p) / 64, 8); endw = calloc(p, 8);
    if (!bm) { printf("bitmap alloc failed\n"); return 2; }
    pthread_t th[64]; for (long i = 0; i < T; ++i) pthread_create(&th[i], 0, run, (void*)i);
    for (int i = 0; i < T; ++i) pthread_join(th[i], 0);
    // pass q must end where pass q+1 starts; the last pass must end at w_0 = 1
    int chain = 1;
    for (int q = 0; q < p; ++q) {
        uint64_t nextStart = (q + 1 < p) ? rotl(1, (int)(((long long)(q + 1) * s) % p)) : 1;
        if (endw[q] != nextStart) chain = 0;
    }
    // count marked words: must be exactly 2^p - 2 (all nonconstant words)
    uint64_t marked = 0; for (uint64_t i = 0; i < (1ULL << p) / 64; ++i) marked += __builtin_popcountll(bm[i]);
    int ok = !badf && P == MASK - 1 && dups == 0 && consts == 0 && chain && marked == P;
    printf("p=%d m=%llu s=%d P=%llu optimal_length=%d flips_valid=%d duplicates=%lld constant=%lld passes_chain=%d marked=%llu -> %s\n",
           p, (unsigned long long)m, s, (unsigned long long)P, P == MASK - 1, !badf, (long long)dups, (long long)consts, chain,
           (unsigned long long)marked, ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}
