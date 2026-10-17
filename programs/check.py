#!/usr/bin/env python3
"""Independent checker for a binary single-track Gray code.

Input: <prefix>.track (P characters '0'/'1', the single track) and <prefix>.heads (n integers, one per line: head j
reads the track at offset h_j). Word t is  W_t = sum_j track[(t + h_j) mod P] << j.

PASS requires: P == 2^n - 2 (optimal for prime n); all P words distinct; no word is all-0 or all-1; every pair of
cyclically consecutive words differs in exactly one bit. By construction every column is a cyclic shift of the one
track, so this is a single-track Gray code. Shares no code with stg.cpp.
"""
import os
import sys
import numpy as np


def main(prefix):
    track = np.frombuffer(open(prefix + '.track', 'rb').read(), dtype=np.uint8)
    assert set(np.unique(track).tolist()) <= {48, 49}, 'track must be 0/1 characters'
    track = (track - 48).astype(np.uint64)
    heads = [int(x) for x in open(prefix + '.heads').read().split()]
    n, P = len(heads), len(track)
    if P > (1 << 28) or os.environ.get('CHUNKED'):
        return chunked(track, heads, n, P)
    t = np.arange(P, dtype=np.int64)
    W = np.zeros(P, dtype=np.uint64)
    for j, h in enumerate(heads):
        W |= track[(t + h) % P] << np.uint64(j)
    full = (1 << n) - 1
    ok_len = P == (1 << n) - 2
    distinct = len(np.unique(W)) == P
    nonconst = not np.any((W == 0) | (W == full))
    x = W ^ np.roll(W, -1)
    one_bit = bool(np.all((x != 0) & ((x & (x - np.uint64(1))) == 0)))
    ok = ok_len and distinct and nonconst and one_bit
    print(f'n={n} P={P} optimal_length={ok_len} distinct={distinct} nonconstant={nonconst} '
          f'one_bit_steps={one_bit} -> {"PASS" if ok else "FAIL"}')
    return 0 if ok else 1


def chunked(track, heads, n, P, chunk=1 << 26):
    """Same checks for large P: words built in chunks, distinctness via a byte map over all 2^n words."""
    track = track.astype(np.uint8)
    full = (1 << n) - 1
    hit = np.zeros(1 << n, dtype=np.uint8)
    nonconst = True
    one_bit = True
    first = prev_last = None
    for a in range(0, P, chunk):
        b = min(P, a + chunk)
        t = np.arange(a, b, dtype=np.int64)
        W = np.zeros(b - a, dtype=np.uint64)
        for j, h in enumerate(heads):
            W |= track[(t + h) % P].astype(np.uint64) << np.uint64(j)
        nonconst &= not np.any((W == 0) | (W == full))
        hit[W.astype(np.int64)] = 1
        seq = W if prev_last is None else np.concatenate([[prev_last], W])
        x = seq[1:] ^ seq[:-1]
        one_bit &= bool(np.all((x != 0) & ((x & (x - np.uint64(1))) == 0)))
        if first is None:
            first = W[0]
        prev_last = W[-1]
    x = np.uint64(first) ^ np.uint64(prev_last)
    one_bit &= bool(x != 0 and (x & (x - np.uint64(1))) == 0)
    ok_len = P == (1 << n) - 2
    # P = 2^n - 2 nonconstant words cover all 2^n - 2 nonconstant values  <=>  they are pairwise distinct
    distinct = ok_len and nonconst and bool(np.count_nonzero(hit[1:full]) == full - 1)
    ok = ok_len and distinct and nonconst and one_bit
    print(f'n={n} P={P} optimal_length={ok_len} distinct={distinct} nonconstant={nonconst} '
          f'one_bit_steps={one_bit} -> {"PASS" if ok else "FAIL"} (chunked)')
    return 0 if ok else 1


if __name__ == '__main__':
    sys.exit(main(sys.argv[1]))
