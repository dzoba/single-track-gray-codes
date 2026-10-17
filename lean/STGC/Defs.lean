/-
  Definitions used in the statement of the main theorem. This is the file a reader has to check.

  Paper: "Optimal single-track Gray codes from Gray-ordered necklaces" (paper/stgc.tex), Sections 1-3.
-/
import Mathlib

namespace STGC

/-- A word of length `n`: one bit for each position. Positions are taken in `ZMod n`, so that rotation is cyclic. -/
abbrev Word (n : ℕ) := ZMod n → Bool

variable {n : ℕ}

/-- Rotation by `k` positions: `(rot k w) i = w (i + k)`. For `k = 1` this is the left rotation
`x₁x₂⋯xₙ ↦ x₂⋯xₙx₁` of the paper (position `i` of the result holds the bit from position `i + 1`). -/
def rot (k : ZMod n) (w : Word n) : Word n := fun i => w (i + k)

/-- A word is constant if all its bits are equal (the words `0ⁿ` and `1ⁿ`). -/
def IsConst (w : Word n) : Prop := ∀ i j, w i = w j

/-- Two words lie in adjacent necklaces: some rotation of `v` differs from `u` in exactly one position. -/
def NecklaceAdj [NeZero n] (u v : Word n) : Prop := ∃ k : ZMod n, hammingDist u (rot k v) = 1

/-- Prefix parity: `prefPar w i` is the parity of the number of ones among positions `0, 1, …, i`
(positions read as natural numbers, most significant first). This is the paper's `π(x)_{i+1}`. -/
def prefPar (w : Word n) (i : ℕ) : Bool :=
  decide (((Finset.range (i + 1)).filter (fun j : ℕ => w (j : ZMod n) = true)).card % 2 = 1)

/-- The rank of a word: its position in the binary reflected Gray code of length `n` (position 0 holds `0ⁿ`).
The inverse of the Gray code `t ↦ t xor ⌊t/2⌋` is the prefix-parity map, so the rank is the number whose binary
digits, most significant first, are the prefix parities of `w`. (`rank_grayWord` checks this against the Gray
code.) -/
def rank (w : Word n) : ℕ :=
  ∑ i ∈ Finset.range n, if prefPar w i then 2 ^ (n - 1 - i) else 0

/-- `w` is the first occurrence of its necklace in the reflected Gray code: it is nonconstant and no rotation of it
has a smaller rank. -/
def IsFirstOcc (w : Word n) : Prop := ¬ IsConst w ∧ ∀ k : ZMod n, rank w ≤ rank (rot k w)

/-- **The Degni–Drisko property** at length `n` (Degni and Drisko, Electron. J. Combin. 14 (2007) R7, Conjecture
3.12 for prime `n`). List the nonconstant necklaces by the rank of their first occurrence. Then any two consecutive
necklaces in this list are adjacent. Formally: if `u` and `v` are first occurrences with `rank u < rank v`, and no
first occurrence has rank strictly between them, then their necklaces are adjacent. -/
def DDProperty (n : ℕ) [NeZero n] : Prop :=
  ∀ u v : Word n, IsFirstOcc u → IsFirstOcc v → rank u < rank v →
    (∀ x : Word n, IsFirstOcc x → ¬ (rank u < rank x ∧ rank x < rank v)) → NecklaceAdj u v

/-- **A single-track Gray code** of length `n` and period `P`: a cyclic sequence of `P` distinct words, in which
consecutive words (cyclically, `t` and `t + 1` in `ZMod P`) differ in exactly one position, and in which every
column is a cyclic shift of column 0: for each position `j` there is a head offset `heads j` with
`(word t) j = (word (t + heads j)) 0` for all `t`. -/
structure SingleTrackGrayCode (n P : ℕ) [NeZero n] where
  word : ZMod P → Word n
  injective : Function.Injective word
  oneBitSteps : ∀ t : ZMod P, hammingDist (word t) (word (t + 1)) = 1
  heads : ZMod n → ZMod P
  singleTrack : ∀ (t : ZMod P) (j : ZMod n), word t j = word (t + heads j) 0

end STGC
