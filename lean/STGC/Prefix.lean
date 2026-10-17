/-
  Rank machinery: prefix parities, the binary value of a digit sequence, comparison of ranks, leading zeros,
  injectivity of the rank.
-/
import STGC.Defs

namespace STGC

open Finset

variable {n : ℕ}

/-- The number of ones among positions `0, …, i`. -/
def cnt (w : Word n) (i : ℕ) : ℕ :=
  ((Finset.range (i + 1)).filter (fun j : ℕ => w (j : ZMod n) = true)).card

lemma prefPar_eq_cnt (w : Word n) (i : ℕ) : prefPar w i = decide (cnt w i % 2 = 1) := rfl

lemma cnt_zero (w : Word n) : cnt w 0 = if w 0 = true then 1 else 0 := by
  unfold cnt
  rw [Finset.range_one, Finset.filter_singleton]
  simp only [Nat.cast_zero]
  split_ifs <;> simp

lemma cnt_succ (w : Word n) (i : ℕ) :
    cnt w (i + 1) = cnt w i + if w ((i + 1 : ℕ) : ZMod n) = true then 1 else 0 := by
  unfold cnt
  rw [Finset.range_add_one (n := i + 1), Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

lemma cnt_congr {u v : Word n} {i : ℕ} (h : ∀ j ≤ i, u (j : ZMod n) = v (j : ZMod n)) :
    cnt u i = cnt v i := by
  unfold cnt
  congr 1
  apply Finset.filter_congr
  intro j hj
  rw [h j (by simp at hj; omega)]

lemma cnt_le_succ (w : Word n) (i : ℕ) : cnt w i ≤ cnt w (i + 1) := by
  rw [cnt_succ]; omega

/-- On a block of ones the count grows by one per position. -/
lemma cnt_ones {w : Word n} {s t : ℕ} (h : ∀ j, s < j → j ≤ s + t → w (j : ZMod n) = true) :
    cnt w (s + t) = cnt w s + t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← add_assoc, cnt_succ, ih (fun j h1 h2 => h j h1 (by omega)), if_pos (h _ (by omega) (by omega))]
    ring

/-- On a block of zeros the count is constant. -/
lemma cnt_zeros {w : Word n} {s t : ℕ} (h : ∀ j, s < j → j ≤ s + t → w (j : ZMod n) = false) :
    cnt w (s + t) = cnt w s := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [← add_assoc, cnt_succ, ih (fun j h1 h2 => h j h1 (by omega)), h _ (by omega) (by omega)]
    simp

lemma cnt_eq_zero {w : Word n} {i : ℕ} (h : ∀ j ≤ i, w (j : ZMod n) = false) : cnt w i = 0 := by
  unfold cnt
  rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  intro j hj
  rw [h j (by simp at hj; omega)]
  simp

/-! ### Binary value of a digit sequence -/

/-- The number with binary digits `d 0, d 1, …, d (m-1)`, most significant first. -/
def bsum (d : ℕ → Bool) (m : ℕ) : ℕ := ∑ i ∈ range m, if d i then 2 ^ (m - 1 - i) else 0

lemma rank_eq_bsum (w : Word n) : rank w = bsum (prefPar w) n := rfl

lemma bsum_zero (d : ℕ → Bool) : bsum d 0 = 0 := by simp [bsum]

lemma bsum_succ (d : ℕ → Bool) (m : ℕ) : bsum d (m + 1) = 2 * bsum d m + if d m then 1 else 0 := by
  unfold bsum
  rw [sum_range_succ, mul_sum]
  congr 1
  · apply sum_congr rfl
    intro i hi
    simp only [mem_range] at hi
    split_ifs
    · rw [← pow_succ']; congr 1; omega
    · simp
  · simp

lemma bsum_congr {d e : ℕ → Bool} {m : ℕ} (h : ∀ i < m, d i = e i) : bsum d m = bsum e m := by
  unfold bsum
  apply sum_congr rfl
  intro i hi
  simp only [mem_range] at hi
  rw [h i hi]

lemma bsum_lt (d : ℕ → Bool) (m : ℕ) : bsum d m < 2 ^ m := by
  induction m with
  | zero => simp [bsum_zero]
  | succ m ih => rw [bsum_succ, pow_succ]; split_ifs <;> omega

lemma bsum_lex {d e : ℕ → Bool} {p m : ℕ} (hpm : p < m) (hagree : ∀ i < p, d i = e i)
    (hd : d p = false) (he : e p = true) : bsum d m + 1 ≤ bsum e m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = p + 1 + t := ⟨m - (p + 1), by omega⟩
  induction t with
  | zero =>
    rw [add_zero, bsum_succ, bsum_succ, hd, he, bsum_congr hagree]
    simp
  | succ t ih =>
    rw [← add_assoc, bsum_succ, bsum_succ]
    have := ih (by omega)
    split_ifs <;> omega

lemma bsum_eq_zero {d : ℕ → Bool} {z : ℕ} (h : ∀ i < z, d i = false) : bsum d z = 0 := by
  induction z with
  | zero => exact bsum_zero d
  | succ z ih =>
    rw [bsum_succ, ih (fun i hi => h i (by omega)), h z (by omega)]
    simp

lemma bsum_lt_of_zeros {d : ℕ → Bool} {z m : ℕ} (hzm : z ≤ m) (h : ∀ i < z, d i = false) :
    bsum d m < 2 ^ (m - z) := by
  obtain ⟨t, rfl⟩ : ∃ t, m = z + t := ⟨m - z, by omega⟩
  induction t with
  | zero => simp [bsum_eq_zero h]
  | succ t ih =>
    rw [← add_assoc, bsum_succ]
    have := ih (by omega)
    have e1 : z + t + 1 - z = (z + t - z) + 1 := by omega
    rw [e1, pow_succ]
    split_ifs <;> omega

lemma bsum_ge_of_one {d : ℕ → Bool} {z m : ℕ} (hzm : z < m) (h : d z = true) :
    2 ^ (m - 1 - z) ≤ bsum d m := by
  obtain ⟨t, rfl⟩ : ∃ t, m = z + 1 + t := ⟨m - (z + 1), by omega⟩
  induction t with
  | zero =>
    rw [add_zero, bsum_succ, h]
    simp
  | succ t ih =>
    rw [← add_assoc, bsum_succ]
    have := ih (by omega)
    have e1 : z + 1 + t + 1 - 1 - z = (z + 1 + t - 1 - z) + 1 := by omega
    rw [e1, pow_succ]
    split_ifs <;> omega

/-! ### Rank facts -/

lemma rank_lt_pow (w : Word n) : rank w < 2 ^ n := bsum_lt _ _

lemma prefPar_congr {u v : Word n} {i : ℕ} (h : ∀ j ≤ i, u (j : ZMod n) = v (j : ZMod n)) :
    prefPar u i = prefPar v i := by
  rw [prefPar_eq_cnt, prefPar_eq_cnt, cnt_congr h]

/-- Lexicographic comparison: the words agree below position `p`, and the prefix parity at `p` is `0` for `u` and
`1` for `v`. -/
lemma rank_lt_of_lex {u v : Word n} {p : ℕ} (hp : p < n)
    (hagree : ∀ j < p, u (j : ZMod n) = v (j : ZMod n))
    (hu : cnt u p % 2 = 0) (hv : cnt v p % 2 = 1) : rank u < rank v := by
  rw [rank_eq_bsum, rank_eq_bsum]
  have := bsum_lex (d := prefPar u) (e := prefPar v) hp
    (fun i hi => prefPar_congr (fun j hj => hagree j (by omega)))
    (by rw [prefPar_eq_cnt]; simp [hu]) (by rw [prefPar_eq_cnt]; simp [hv])
  omega

/-- A word with zeros at positions `0, …, z-1` has rank `< 2^(n-z)`. -/
lemma rank_lt_of_zeros {w : Word n} {z : ℕ} (hz : z ≤ n) (h : ∀ j < z, w (j : ZMod n) = false) :
    rank w < 2 ^ (n - z) := by
  rw [rank_eq_bsum]
  apply bsum_lt_of_zeros hz
  intro i hi
  rw [prefPar_eq_cnt, cnt_eq_zero (fun j hj => h j (by omega))]
  simp

/-- A word with a one at position `z` has rank `≥ 2^(n-1-z)`. -/
lemma rank_ge_of_one {w : Word n} {z : ℕ} (hz : z < n) (h : w (z : ZMod n) = true) :
    2 ^ (n - 1 - z) ≤ rank w := by
  rw [rank_eq_bsum]
  rcases z with _ | z
  · apply bsum_ge_of_one hz
    rw [prefPar_eq_cnt, cnt_zero]
    simp only [Nat.cast_zero] at h
    simp [h]
  · have hs := cnt_succ w z
    rw [if_pos h] at hs
    by_cases hc : cnt w z % 2 = 1
    · have := bsum_ge_of_one (d := prefPar w) (z := z) (m := n) (by omega)
        (by rw [prefPar_eq_cnt]; simp [hc])
      have h2 : 2 ^ (n - 1 - (z + 1)) ≤ 2 ^ (n - 1 - z) :=
        Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    · exact bsum_ge_of_one hz (by rw [prefPar_eq_cnt]; simp; omega)

lemma natCast_val_eq [NeZero n] (i : ZMod n) : ((i.val : ℕ) : ZMod n) = i := ZMod.natCast_zmod_val i

/-- The prefix parities determine the word. -/
lemma eq_of_prefPar [NeZero n] {u v : Word n} (h : ∀ i < n, prefPar u i = prefPar v i) : u = v := by
  have hc : ∀ i < n, cnt u i % 2 = cnt v i % 2 := by
    intro i hi
    have := h i hi
    rw [prefPar_eq_cnt, prefPar_eq_cnt] at this
    simp only [decide_eq_decide] at this
    omega
  funext x
  rw [← natCast_val_eq x]
  have hx := ZMod.val_lt x
  generalize x.val = j at hx ⊢
  rcases j with _ | j
  · have := hc 0 hx
    rw [cnt_zero, cnt_zero] at this
    simp only [Nat.cast_zero]
    revert this
    cases u 0 <;> cases v 0 <;> simp
  · have h1 := hc j (by omega)
    have h2 := hc (j + 1) hx
    rw [cnt_succ, cnt_succ] at h2
    revert h2
    cases u ((j + 1 : ℕ) : ZMod n) <;> cases v ((j + 1 : ℕ) : ZMod n) <;> simp <;> omega

lemma rank_injective [NeZero n] {u v : Word n} (h : rank u = rank v) : u = v := by
  by_contra hne
  have hex : ∃ i, i < n ∧ prefPar u i ≠ prefPar v i := by
    by_contra hall
    push Not at hall
    exact hne (eq_of_prefPar hall)
  classical
  let p := Nat.find hex
  have hp : p < n ∧ prefPar u p ≠ prefPar v p := Nat.find_spec hex
  have hmin : ∀ i < p, prefPar u i = prefPar v i := by
    intro i hi
    have := Nat.find_min hex hi
    push Not at this
    exact this (by omega)
  rw [rank_eq_bsum, rank_eq_bsum] at h
  rcases hpu : prefPar u p with _ | _
  · have := bsum_lex (m := n) hp.1 hmin hpu (by
      have := hp.2; rw [hpu] at this; cases hv : prefPar v p <;> simp_all)
    omega
  · have := bsum_lex (m := n) hp.1 (fun i hi => (hmin i hi).symm) (by
      have := hp.2; rw [hpu] at this; cases hv : prefPar v p <;> simp_all) hpu
    omega

/-- The all-zero word has rank `0`; every nonconstant word has positive rank. -/
lemma rank_pos [NeZero n] {w : Word n} (hw : ¬ IsConst w) : 0 < rank w := by
  by_contra h0
  apply hw
  have hz : rank w = rank (fun _ : ZMod n => false) := by
    have : rank (fun _ : ZMod n => false) = 0 := by
      rw [rank_eq_bsum]
      apply bsum_eq_zero
      intro i _
      rw [prefPar_eq_cnt, cnt_eq_zero (fun j _ => rfl)]
      simp
    omega
  rw [rank_injective hz]
  intro i j
  rfl


/-! ### Comparison helpers -/

lemma rank_lt_of_lex_odd {u v : Word n} {s : ℕ} (hs : s + 1 < n)
    (hagree : ∀ j ≤ s, u (j : ZMod n) = v (j : ZMod n)) (hc : cnt u s % 2 = 1)
    (hu : u ((s + 1 : ℕ) : ZMod n) = true) (hv : v ((s + 1 : ℕ) : ZMod n) = false) : rank u < rank v := by
  apply rank_lt_of_lex hs (fun j hj => hagree j (by omega))
  · rw [cnt_succ, if_pos hu]; omega
  · rw [cnt_succ, hv, ← cnt_congr hagree]; simpa using hc

lemma rank_lt_of_lex_even {u v : Word n} {s : ℕ} (hs : s + 1 < n)
    (hagree : ∀ j ≤ s, u (j : ZMod n) = v (j : ZMod n)) (hc : cnt u s % 2 = 0)
    (hu : u ((s + 1 : ℕ) : ZMod n) = false) (hv : v ((s + 1 : ℕ) : ZMod n) = true) : rank u < rank v := by
  apply rank_lt_of_lex hs (fun j hj => hagree j (by omega))
  · rw [cnt_succ, hu]; simpa using hc
  · rw [cnt_succ, if_pos hv, ← cnt_congr hagree]; omega

/-- The count on a prefix `0 1^a`. -/
lemma cnt_lead01 {w : Word n} {a : ℕ} (h0 : w 0 = false)
    (h1 : ∀ j, 0 < j → j ≤ a → w (j : ZMod n) = true) : cnt w a = a := by
  have := cnt_ones (s := 0) (t := a) (w := w) (fun j hj1 hj2 => h1 j hj1 (by omega))
  rw [zero_add] at this
  rw [this, cnt_zero, h0]
  simp

/-- Flipping a one at position `n-2` (followed by a one at `n-1`) when the prefix parity before it is odd raises
the rank by one. -/
lemma rank_succ_of_flip {u v : Word n} (hn : 3 ≤ n)
    (hagree : ∀ j < n - 2, u (j : ZMod n) = v (j : ZMod n))
    (hu2 : u ((n - 2 : ℕ) : ZMod n) = true) (hv2 : v ((n - 2 : ℕ) : ZMod n) = false)
    (hu1 : u ((n - 1 : ℕ) : ZMod n) = true) (hv1 : v ((n - 1 : ℕ) : ZMod n) = true)
    (hc : cnt u (n - 3) % 2 = 1) : rank v = rank u + 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  have e2 : m + 3 - 2 = m + 1 := by omega
  have e1 : m + 3 - 1 = m + 1 + 1 := by omega
  have e3 : m + 3 - 3 = m := by omega
  rw [e2] at hagree hu2 hv2
  rw [e1] at hu1 hv1
  rw [e3] at hc
  have hcm : cnt v m = cnt u m := cnt_congr (fun j hj => (hagree j (by omega)).symm)
  have hu_a : cnt u (m + 1) = cnt u m + 1 := by rw [cnt_succ, if_pos hu2]
  have hv_a : cnt v (m + 1) = cnt u m := by rw [cnt_succ, hv2, hcm]; simp
  have hu_b : cnt u (m + 1 + 1) = cnt u m + 2 := by rw [cnt_succ, if_pos hu1, hu_a]
  have hv_b : cnt v (m + 1 + 1) = cnt u m + 1 := by rw [cnt_succ, if_pos hv1, hv_a]
  rw [rank_eq_bsum, rank_eq_bsum]
  have bv2 := bsum_succ (prefPar v) (m + 1 + 1)
  have bv1 := bsum_succ (prefPar v) (m + 1)
  have bu2 := bsum_succ (prefPar u) (m + 1 + 1)
  have bu1 := bsum_succ (prefPar u) (m + 1)
  have bc := bsum_congr (d := prefPar v) (e := prefPar u) (m := m + 1)
      (fun i hi => prefPar_congr (fun j hj => (hagree j (by omega)).symm))
  simp only [prefPar_eq_cnt, hu_a, hv_a, hu_b, hv_b] at bv2 bv1 bu2 bu1
  have h1 : (cnt u m + 1) % 2 = 0 := by omega
  have h2 : (cnt u m + 2) % 2 = 1 := by omega
  simp [hc, h1, h2] at bv2 bv1 bu2 bu1
  show bsum (prefPar v) (m + 1 + 1 + 1) = bsum (prefPar u) (m + 1 + 1 + 1) + 1
  omega


lemma cnt_succ_true {w : Word n} {i : ℕ} (h : w ((i + 1 : ℕ) : ZMod n) = true) :
    cnt w (i + 1) = cnt w i + 1 := by rw [cnt_succ, if_pos h]

lemma cnt_succ_false {w : Word n} {i : ℕ} (h : w ((i + 1 : ℕ) : ZMod n) = false) :
    cnt w (i + 1) = cnt w i := by rw [cnt_succ, h]; simp

end STGC
