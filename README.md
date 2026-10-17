# Optimal single-track Gray codes

Paper, formalization, programs and computational certificates for **Optimal single-track Gray codes from Gray-ordered necklaces**, Chris Dzoba (2026).

## What is established

Theorem A proves that the Degni–Drisko necklace-adjacency property implies an optimal binary single-track Gray code for every odd prime. The implication is formalized in Lean 4; the hypothesis is not proved for every prime. Lean also checks the small cases described in `lean/README.md`.

The paper reports optimal codes at every odd prime through 47. Explicit codes through 37 were checked word by word by a program independent of their generator. For 41, 43 and 47, two independently written programs verified the Degni–Drisko property; Theorem A supplies the implication. These are finite computations, not a proof of the conjecture for all primes.

## Contents

- `paper/stgc.tex`, `paper/stgc.pdf`: article version.
- `paper/ieee/stgc-ieee.tex`, `paper/ieee/stgc-ieee.pdf`: IEEE review version, generated with `paper/make_ieee.py`.
- `lean/`: Lean project, pinned toolchain and Mathlib dependencies, without downloaded dependencies or build caches.
- `programs/`: search (`stg.cpp`), independent track checkers (`check.py`, `check2.c`), Theorem A construction (`ddstg.cpp`), independent flip verifier (`vfy.c`), and two streaming DD checkers (`ddverify.cpp`, `ddv.cpp`).
- `codes/`: compressed tracks, head positions and metadata for primes 5, 7, 11, 13, 17, 19, 23, 29 and 31, including both n=29 BRGC versions.
- `logs/`: DD verification logs for 37, 41, 43 and 47, n=37 construction/check logs, and Theorem A code-check logs.
- `SHA256SUMS`: checksums of the release files, excluding this checksum file itself.

The 3.7 GB n=37 flip sequence is regenerable with `ddstg`; its SHA-256 is in `logs/p37.flips.sha256`. It is not included here. Logs record earlier computations; packaging does not rerun them.

## Build Lean

Install the toolchain named in `lean/lean-toolchain` using elan, then:

```sh
cd lean
lake exe cache get
lake build
lake env lean STGC/Sanity.lean
```

The dependency versions are pinned in `lakefile.lean` and `lake-manifest.json`. See `lean/README.md` for the definitions, theorem statement and proof scope.

## Check a track

Each `.track.gz` decompresses to a string of `0`/`1` bytes. The accompanying `.heads` lists offsets: word t has bit j equal to `track[(t + heads[j]) mod P]`.

From the repository root, this small example builds the C checker and checks n=5:

```sh
mkdir -p build
cc -O3 -std=c11 programs/check2.c -o build/check2
gzip -dc codes/n5-brgc.track.gz > build/n5-brgc.track
cp codes/n5-brgc.heads build/n5-brgc.heads
build/check2 build/n5-brgc
```

Alternatively, with NumPy installed, run `python3 programs/check.py build/n5-brgc`. Both check optimal length, distinct nonconstant words and cyclic one-bit steps. Large tracks require substantial decompressed storage and memory: n=29 is about 0.5 GB and n=31 about 2.1 GB before checker working memory.

## Build the other programs

```sh
c++ -O3 -std=c++17 -pthread programs/stg.cpp -o build/stg
c++ -O3 -std=c++17 -pthread programs/ddstg.cpp -o build/ddstg
c++ -O3 -std=c++17 -pthread programs/ddverify.cpp -o build/ddverify
c++ -O3 -std=c++17 -pthread programs/ddv.cpp -o build/ddv
cc -O3 -std=c11 programs/vfy.c -pthread -o build/vfy
```

Usage is documented in each source header. These programs do not automatically select a safe resource budget; choose thread counts and sizes appropriate to your machine.

## Build the papers

With Tectonic installed:

```sh
python3 paper/make_ieee.py
tectonic paper/stgc.tex
tectonic paper/ieee/stgc-ieee.tex
```

## License

Code, including the Lean formalization and paper-generation script, is licensed under MIT; see `LICENSE-CODE`. Paper text/PDFs, documentation and data are licensed under Creative Commons Attribution 4.0 International; see `LICENSE-PAPER-DATA`. Dependency licenses remain their own.
