/-
  Main theorem (paper/stgc.tex, Theorem A, stated for every odd prime):

  If the Degni–Drisko property holds at length n (an explicit hypothesis, `DDProperty n`), then an optimal
  single-track Gray code of length n and period 2^n - 2 exists.
-/
import STGC.SmallCases
import STGC.Lift
import STGC.Closing

namespace STGC

theorem prime_cases (n : ℕ) (hn : n.Prime) (hodd : n ≠ 2) : n = 3 ∨ n = 5 ∨ 7 ≤ n := by
  have h2 := hn.two_le
  by_contra hc
  push Not at hc
  obtain ⟨h3, h5, h7⟩ := hc
  interval_cases n <;> simp_all <;> norm_num at hn

/-- **Theorem A.** For every odd prime `n`, the Degni–Drisko property at length `n` implies that an optimal
single-track Gray code of length `n` and period `2^n - 2` exists. -/
theorem stgc_of_DD (n : ℕ) [NeZero n] (hn : n.Prime) (hodd : n ≠ 2) (hDD : DDProperty n) :
    Nonempty (SingleTrackGrayCode n (2 ^ n - 2)) := by
  rcases prime_cases n hn hodd with h | h | h
  · subst h; exact stgc_three
  · subst h; exact stgc_five
  · obtain ⟨m, hm, ⟨H⟩⟩ := hamCycle_of_DD (hn.odd_of_ne_two hodd) h hDD
    exact stgc_of_hamCycle hn H

end STGC
