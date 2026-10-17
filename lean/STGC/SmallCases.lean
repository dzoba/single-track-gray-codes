/-
  Optimal single-track Gray codes for n = 3 (period 6) and n = 5 (period 30), checked by `decide`.
  The general argument (Closing.lean) needs n ≥ 7.
-/
import STGC.Defs

namespace STGC

/-- The code given by a track and head offsets: `word t j = track (t + heads j)`. -/
def ofTrack {n P : ℕ} (track : ZMod P → Bool) (heads : ZMod n → ZMod P) : ZMod P → Word n :=
  fun t j => track (t + heads j)

def track3 : ZMod 6 → Bool := fun t => [false, false, false, true, true, true].getD t.val false
def heads3 : ZMod 3 → ZMod 6 := fun j => [0, 2, 4].getD j.val 0

def track5 : ZMod 30 → Bool := fun t =>
  [false, true, true, true, true, true, true, true, true, true, false, false, false, false, true, true, true,
    false, false, false, false, true, true, true, false, false, false, false, false, false].getD t.val false
def heads5 : ZMod 5 → ZMod 30 := fun j => [0, 24, 18, 12, 6].getD j.val 0

theorem stgc_three' : Nonempty (SingleTrackGrayCode 3 6) :=
  ⟨{ word := ofTrack track3 heads3
     injective := by decide
     oneBitSteps := by decide
     heads := heads3
     singleTrack := by decide }⟩

theorem stgc_five' : Nonempty (SingleTrackGrayCode 5 30) :=
  ⟨{ word := ofTrack track5 heads5
     injective := by decide
     oneBitSteps := by decide
     heads := heads5
     singleTrack := by decide }⟩

theorem stgc_three : Nonempty (SingleTrackGrayCode 3 (2 ^ 3 - 2)) := stgc_three'
theorem stgc_five : Nonempty (SingleTrackGrayCode 5 (2 ^ 5 - 2)) := stgc_five'

end STGC
