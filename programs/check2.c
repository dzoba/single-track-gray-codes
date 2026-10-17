/* Independent checker (C, bitset) for a binary single-track Gray code, for sizes numpy cannot hold.
 * Usage: check2 <prefix>   reads <prefix>.track ('0'/'1' chars, length P) and <prefix>.heads (n offsets).
 * Word t = sum_j track[(t + h_j) mod P] << j. PASS iff P == 2^n - 2, words pairwise distinct (bitset), none
 * constant, and cyclically consecutive words differ in exactly one bit. Shares no code with stg.cpp or check.py. */
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>

int main(int argc, char **argv) {
    if (argc != 2) { fprintf(stderr, "usage: check2 prefix\n"); return 2; }
    char path[4096];
    snprintf(path, sizeof path, "%s.heads", argv[1]);
    FILE *f = fopen(path, "r");
    if (!f) { perror(path); return 2; }
    long long h[64]; int n = 0;
    while (n < 64 && fscanf(f, "%lld", &h[n]) == 1) n++;
    fclose(f);
    snprintf(path, sizeof path, "%s.track", argv[1]);
    f = fopen(path, "rb");
    if (!f) { perror(path); return 2; }
    fseek(f, 0, SEEK_END); long long P = ftell(f); fseek(f, 0, SEEK_SET);
    unsigned char *tr = malloc(P);
    if (fread(tr, 1, P, f) != (size_t)P) { fprintf(stderr, "short read\n"); return 2; }
    fclose(f);
    for (long long i = 0; i < P; i++) {
        if (tr[i] != '0' && tr[i] != '1') { printf("bad char\nFAIL\n"); return 1; }
        tr[i] -= '0';
    }
    uint64_t full = (n == 64) ? ~0ull : ((1ull << n) - 1);
    int lenok = (P == (long long)full - 1);
    uint64_t *seen = calloc((full >> 6) + 1, 8);
    long long dup = 0, cons = 0, badstep = 0;
    uint64_t first = 0, prev = 0;
    for (long long t = 0; t < P; t++) {
        uint64_t w = 0;
        for (int j = 0; j < n; j++) {
            long long idx = (t + h[j]) % P; if (idx < 0) idx += P;
            w |= (uint64_t)tr[idx] << j;
        }
        if (w == 0 || w == full) cons++;
        if (seen[w >> 6] >> (w & 63) & 1) dup++;
        seen[w >> 6] |= 1ull << (w & 63);
        if (t == 0) first = w;
        else { uint64_t x = w ^ prev; if (x == 0 || (x & (x - 1))) badstep++; }
        prev = w;
    }
    { uint64_t x = first ^ prev; if (x == 0 || (x & (x - 1))) badstep++; }
    int ok = lenok && !dup && !cons && !badstep;
    printf("n=%d P=%lld optimal_length=%d duplicates=%lld constant=%lld bad_steps=%lld -> %s\n",
           n, P, lenok, dup, cons, badstep, ok ? "PASS" : "FAIL");
    return ok ? 0 : 1;
}
