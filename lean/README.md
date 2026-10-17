# Lean 4 formalization: Degni–Drisko ⇒ optimal single-track Gray codes

Machine-checked proof of Theorem A of `../paper/stgc.tex`, stated for every odd prime.

```lean
theorem STGC.stgc_of_DD (n : ℕ) [NeZero n] (hn : n.Prime) (hodd : n ≠ 2) (hDD : DDProperty n) :
    Nonempty (SingleTrackGrayCode n (2 ^ n - 2))
```

`#print axioms STGC.stgc_of_DD` gives `[propext, Classical.choice, Quot.sound]`: Lean's standard axioms, nothing
else. There is no `sorry`, `admit` or `native_decide` anywhere. The Degni–Drisko property is a hypothesis of the
theorem, not an axiom.

## What a reader has to check

Three things:
1. **`STGC/Defs.lean`** (about 60 lines). Its definitions are listed below.
2. The **theorem statement** in `STGC/Main.lean`, quoted above.
3. The **Mathlib definitions** these use: `ZMod`, `hammingDist`, `Nat.Prime`, `Finset.range`/`card`, and `Nonempty`.

`Defs.lean` defines:

- `Word n`: bits indexed by `ZMod n`. Position 0 is the most significant bit.
- `rot k w`: cyclic rotation. `IsConst`.
- `NecklaceAdj u v`: some rotation of `v` is at Hamming distance 1 from `u`.
- `prefPar` and `rank`: the position of a word in the binary reflected Gray code, as the number whose binary
  digits are the prefix parities.
- `IsFirstOcc w`: `w` is nonconstant and no rotation of `w` has smaller rank.
- `DDProperty n`: first occurrences that are consecutive in rank order lie in adjacent necklaces. This is implied
  by the Degni–Drisko conjecture, EJC 14 (2007) R7, Conj. 3.12, for prime n, and is weaker than it in two ways:
  - it asks only for necklace adjacency (some rotation at Hamming distance 1), not for the first-occurrence words
    themselves to differ in one bit;
  - it leaves out the constant words 0^n and 1^n.
  So the theorem needs only this weaker hypothesis.
- `SingleTrackGrayCode n P`: `P` distinct words indexed by `ZMod P`; consecutive words, cyclically, differ in
  exactly one bit; and every column is a cyclic shift of column 0
  (`word t j = word (t + heads j) 0`).

Everything else is proof.

**Scope.** Lean proves `DDProperty` itself only at n = 5 (by computation, `Sanity.lean`). For n ≥ 7 the hypothesis
rests on the computational verifications outside Lean:
- Degni–Drisko for n ≤ 37;
- ddverify and indep3/ddv (`programs/ddverify.cpp`, `programs/ddv.cpp` in the arXiv ancillary files) at 37, 41, 43 and 47.

The independent Lean referee (2026-10-14) found the semantics faithful and the build clean.

## Sanity checks of the definitions

- **`STGC/Check.lean`** evaluates the definitions with `#eval` and agrees with the independent C and Python tools.
  `rank` equals the reflected-Gray-code position for every word at n = 5, 7, 9. The Degni–Drisko list at n = 7
  matches ddstg word for word, including the closing pivots. The list lengths are 6, 18, 186. The property holds at
  5, 7, 11 and fails at 9, as ddverify found.
- **`STGC/Sanity.lean`** proves `DDProperty 5` by kernel computation, so the hypothesis is satisfiable.
- **`STGC/SmallCases.lean`** proves explicit optimal codes for n = 3 and n = 5 by `decide`, so the conclusion is
  satisfiable.

## Structure

| File | Content | Paper |
|---|---|---|
| `Defs.lean` | definitions (above) | §1–3 |
| `Interface.lean` | `HamCycle n m`: a Hamilton cycle of the necklace graph starting at ⟨0^{n−1}1⟩ | — |
| `Necklace.lean`, `Lift.lean` | `stgc_of_hamCycle`: a Hamilton cycle gives an optimal STGC for prime n (Lemma V, including the shift fix) | Lemma V |
| `Prefix.lean`, `RotWord.lean` | rank facts: Fact P, leading zeros, injectivity, flipping position n−2 adds 1 | Fact P |
| `Words.lean` | the explicit words A_k, E_k and Lemmas 0–5 for all odd n ≥ 7 | Lemmas 0–5 |
| `Posa.lean` | the generic Pósa rotation lemma on lists | — |
| `Closing.lean` | `hamCycle_of_DD`: DD plus the (n−3)/2 explicit rotations give a Hamilton cycle | proof of Theorem A |
| `SmallCases.lean` | n = 3, 5 | — |
| `Main.lean` | `stgc_of_DD` | Theorem A |

The project is about 1,750 lines.

## Build

Toolchain `leanprover/lean4:v4.32.1`, Mathlib at `520045ab` (see `lakefile.lean`).

```sh
lake exe cache get
lake build
lake env lean STGC/Sanity.lean
```

## Differences from the paper's write-up (bookkeeping only)

- Lemma 1 at k = 1 uses a different rotation, because the Lean development works with the first-occurrence word
  E_1 = 0 1^{n−5} 0101.
- Lemma 4's step-0 gap check is not needed: the list form of the Pósa lemma only requires j + 1 < length.
- Lemmas 2 and 3 for k ≥ 1 are proved by exhibiting a one before position 2k+1 in every nontrivial rotation,
  rather than by the "unique longest zero run" wording. The content is the same.
- Lemma V uses the rotate-the-tail shift fix, as in the revised paper (2026-10-14).

None of the paper's lemmas was false.
