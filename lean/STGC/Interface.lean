/-
  The interface between the two halves of the proof.

  * `HamCycle n m`: a Hamilton cycle of the necklace graph of length `n`, given by one representative word per
    nonconstant necklace, in cyclic order (indices in `ZMod m`), consecutive necklaces adjacent, and starting at a
    word with a single one (the necklace ⟨0^{n-1}1⟩).
  * `Lift.lean` proves:     HamCycle n m  ⇒  a single-track Gray code of length n and period 2^n - 2  (n prime).
  * `Closing.lean` proves:  DDProperty n  ⇒  HamCycle n m for some m                                    (n odd, n ≥ 7).
-/
import STGC.Defs

namespace STGC

/-- A word with exactly one `true`, at position `a`. -/
def IsSingleton {n : ℕ} (w : Word n) : Prop := ∃ a : ZMod n, ∀ i, w i = decide (i = a)

/-- A Hamilton cycle of the necklace graph on the nonconstant necklaces of length `n`, of length `m`. -/
structure HamCycle (n m : ℕ) [NeZero n] [NeZero m] where
  rep : ZMod m → Word n
  nonconst : ∀ i, ¬ IsConst (rep i)
  cover : ∀ x : Word n, ¬ IsConst x → ∃ i k, x = rot k (rep i)
  distinct : ∀ i j k, rot k (rep i) = rep j → i = j
  adj : ∀ i, NecklaceAdj (rep i) (rep (i + 1))
  start : IsSingleton (rep 0)

end STGC
