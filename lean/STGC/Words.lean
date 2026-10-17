/-
  The explicit words of the closing argument (paper Lemmas 0-5).

  Positions are 0-indexed (the paper's position p is position p-1 here). With K = (n-3)/2 and c_k = n-2k-3:
  * `sing n` = 0^{n-1} 1, `E0 n` = 0 1^{n-1};
  * `A n 0` = 0 1^{n-5} 0111, `A n k` = 0^{2k+1} 1 0 1^{c_k} (k ≥ 1);
  * `E n 1` = 0 1^{n-5} 0101, `E n (k+1)` = 0^{2k+1} 1 0 1^{c_k-2} 0 1 (k ≥ 1); in particular `E n K` = 0^{n-4} 1001.
-/
import STGC.Prefix
import STGC.RotWord

namespace STGC

variable {n : ℕ}

/-- Close a goal `decide P = true`, `decide P = false` or `decide P = decide Q` about natural numbers. -/
macro "wbit" : tactic =>
  `(tactic| (simp only [decide_eq_true_eq, decide_eq_false_iff_not, ne_eq, decide_eq_decide] <;>
    first | omega | (simp <;> omega)))

/-! ### Definitions -/

/-- `0^{n-1} 1`. -/
def sing (n : ℕ) : Word n := fun i => decide (i.val + 1 = n)
/-- `E_0 = 0 1^{n-1}`. -/
def E0 (n : ℕ) : Word n := fun i => decide (i.val ≠ 0)
/-- `A_0 = 0 1^{n-5} 0 1 1 1`. -/
def A0 (n : ℕ) : Word n := fun i => decide (i.val ≠ 0 ∧ i.val + 4 ≠ n)
/-- `E_1 = 0 1^{n-5} 0 1 0 1`. -/
def E1 (n : ℕ) : Word n := fun i => decide (i.val ≠ 0 ∧ i.val + 4 ≠ n ∧ i.val + 2 ≠ n)
/-- `A_k = 0^{2k+1} 1 0 1^{n-2k-3}` (for `k ≥ 1`). -/
def Ak (n k : ℕ) : Word n := fun i => decide (i.val = 2 * k + 1 ∨ 2 * k + 3 ≤ i.val)
/-- `E_{k+1} = 0^{2k+1} 1 0 1^{n-2k-5} 0 1` (for `k ≥ 1`). -/
def Ek (n k : ℕ) : Word n := fun i => decide (i.val = 2 * k + 1 ∨ (2 * k + 3 ≤ i.val ∧ i.val + 2 ≠ n))

/-- The pivots `A_k`. -/
def A (n k : ℕ) : Word n := if k = 0 then A0 n else Ak n k

/-- The ends `E_k`. -/
def E (n : ℕ) : ℕ → Word n
  | 0 => E0 n
  | k + 1 => if k = 0 then E1 n else Ek n k

lemma E_zero : E n 0 = E0 n := rfl
lemma E_succ (k : ℕ) : E n (k + 1) = if k = 0 then E1 n else Ek n k := rfl

/-! ### Evaluation at natural positions -/

lemma sing_nat {t : ℕ} (ht : t < n) : sing n (t : ZMod n) = decide (t + 1 = n) := by
  simp [sing, val_natCast_of_lt ht]
lemma E0_nat {t : ℕ} (ht : t < n) : E0 n (t : ZMod n) = decide (t ≠ 0) := by
  simp [E0, val_natCast_of_lt ht]
lemma A0_nat {t : ℕ} (ht : t < n) : A0 n (t : ZMod n) = decide (t ≠ 0 ∧ t + 4 ≠ n) := by
  simp only [A0, val_natCast_of_lt ht]
lemma E1_nat {t : ℕ} (ht : t < n) : E1 n (t : ZMod n) = decide (t ≠ 0 ∧ t + 4 ≠ n ∧ t + 2 ≠ n) := by
  simp only [E1, val_natCast_of_lt ht]
lemma Ak_nat {k t : ℕ} (ht : t < n) : Ak n k (t : ZMod n) = decide (t = 2 * k + 1 ∨ 2 * k + 3 ≤ t) := by
  simp only [Ak, val_natCast_of_lt ht]
lemma Ek_nat {k t : ℕ} (ht : t < n) :
    Ek n k (t : ZMod n) = decide (t = 2 * k + 1 ∨ (2 * k + 3 ≤ t ∧ t + 2 ≠ n)) := by
  simp only [Ek, val_natCast_of_lt ht]

lemma not_isConst_of {w : Word n} (a b : ZMod n) (ha : w a = false) (hb : w b = true) : ¬ IsConst w := by
  intro h
  have := h a b
  rw [ha, hb] at this
  exact Bool.false_ne_true this

/-! ### First occurrences via leading zeros -/

/-- If `w` starts with `z` zeros and every nontrivial rotation of `w` has a one before position `z`, then `w` is
a first occurrence. -/
lemma isFirstOcc_of_lead [NeZero n] {w : Word n} {z : ℕ} (hz : z ≤ n) (hnc : ¬ IsConst w)
    (hzero : ∀ j < z, w (j : ZMod n) = false)
    (hrot : ∀ r, 0 < r → r < n → ∃ t < z, w ((t + r : ℕ) : ZMod n) = true) : IsFirstOcc w := by
  refine ⟨hnc, fun m => ?_⟩
  have hm : m = ((m.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val m).symm
  rcases Nat.eq_zero_or_pos m.val with h0 | hpos
  · rw [hm, h0, Nat.cast_zero, rot_zero']
  · obtain ⟨t, htz, ht⟩ := hrot m.val hpos (ZMod.val_lt m)
    have h1 := rank_lt_of_zeros hz hzero
    have h2 := rank_ge_of_one (w := rot m w) (z := t) (by omega) (by rw [hm, rot_natCast]; exact ht)
    have h3 : 2 ^ (n - z) ≤ 2 ^ (n - 1 - t) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-! ### Lemma 2 and Lemma 3 for `k ≥ 1` -/

lemma Ak_firstOcc [NeZero n] {k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k + 5 ≤ n) : IsFirstOcc (Ak n k) := by
  apply isFirstOcc_of_lead (z := 2 * k + 1) (by omega)
  · apply not_isConst_of ((0 : ℕ) : ZMod n) ((2 * k + 1 : ℕ) : ZMod n)
    · rw [Ak_nat (by omega)]; simp
    · rw [Ak_nat (by omega)]; simp
  · intro j hj
    rw [Ak_nat (by omega)]; wbit
  · intro r hr0 hrn
    by_cases h1 : r ≤ 2 * k + 1
    · refine ⟨2 * k + 1 - r, by omega, ?_⟩
      rw [Ak_nat (by omega)]; wbit
    · by_cases h2 : r = 2 * k + 2
      · refine ⟨1, by omega, ?_⟩
        rw [Ak_nat (by omega)]; wbit
      · refine ⟨0, by omega, ?_⟩
        rw [Ak_nat (by omega)]; wbit

lemma Ek_firstOcc [NeZero n] {k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k + 5 ≤ n) : IsFirstOcc (Ek n k) := by
  apply isFirstOcc_of_lead (z := 2 * k + 1) (by omega)
  · apply not_isConst_of ((0 : ℕ) : ZMod n) ((2 * k + 1 : ℕ) : ZMod n)
    · rw [Ek_nat (by omega)]; simp
    · rw [Ek_nat (by omega)]; simp
  · intro j hj
    rw [Ek_nat (by omega)]; wbit
  · intro r hr0 hrn
    by_cases h1 : r ≤ 2 * k + 1
    · refine ⟨2 * k + 1 - r, by omega, ?_⟩
      rw [Ek_nat (by omega)]; wbit
    · by_cases h2 : r = 2 * k + 2
      · by_cases h3 : n = 2 * k + 5
        · refine ⟨2, by omega, ?_⟩
          rw [Ek_nat (by omega)]; wbit
        · refine ⟨1, by omega, ?_⟩
          rw [Ek_nat (by omega)]; wbit
      · by_cases h3 : r + 2 = n
        · refine ⟨1, by omega, ?_⟩
          rw [Ek_nat (by omega)]; wbit
        · refine ⟨0, by omega, ?_⟩
          rw [Ek_nat (by omega)]; wbit


/-! ### Lemma 0 (the easy parts), Lemma 2 and Lemma 3 for `k = 0` -/

lemma E0_firstOcc [NeZero n] (hn : 2 ≤ n) : IsFirstOcc (E0 n) := by
  apply isFirstOcc_of_lead (z := 1) (by omega)
  · apply not_isConst_of ((0 : ℕ) : ZMod n) ((1 : ℕ) : ZMod n)
    · rw [E0_nat (by omega)]; simp
    · rw [E0_nat (by omega)]; simp
  · intro j hj
    rw [E0_nat (by omega)]; wbit
  · intro r hr0 hrn
    refine ⟨0, by omega, ?_⟩
    rw [E0_nat (by omega)]; wbit

lemma rank_sing [NeZero n] (hn : 2 ≤ n) : rank (sing n) = 1 := by
  have h1 := rank_lt_of_zeros (w := sing n) (z := n - 1) (by omega)
    (fun j hj => by rw [sing_nat (by omega)]; wbit)
  have h2 := rank_ge_of_one (w := sing n) (z := n - 1) (by omega)
    (by rw [sing_nat (by omega)]; wbit)
  rw [show n - (n - 1) = 1 by omega] at h1
  rw [show n - 1 - (n - 1) = 0 by omega] at h2
  simp at h1 h2
  omega

lemma sing_not_const [NeZero n] (hn : 2 ≤ n) : ¬ IsConst (sing n) := by
  apply not_isConst_of ((0 : ℕ) : ZMod n) ((n - 1 : ℕ) : ZMod n)
  · rw [sing_nat (by omega)]; wbit
  · rw [sing_nat (by omega)]; wbit

lemma rank_sing_le [NeZero n] (hn : 2 ≤ n) {w : Word n} (hw : ¬ IsConst w) : rank (sing n) ≤ rank w := by
  rw [rank_sing hn]; exact rank_pos hw

lemma sing_firstOcc [NeZero n] (hn : 2 ≤ n) : IsFirstOcc (sing n) :=
  ⟨sing_not_const hn, fun _ => rank_sing_le hn (fun h => sing_not_const hn (isConst_of_rot h))⟩

lemma rank_lt_of_rot_one [NeZero n] (hn : 2 ≤ n) {w : Word n} (h0 : w 0 = false) (m : ZMod n)
    (h : w m = true) : rank w < rank (rot m w) := by
  have h1 := rank_lt_of_zeros (w := w) (z := 1) (by omega) (fun j hj => by
    rw [show j = 0 by omega, Nat.cast_zero]; exact h0)
  have h2 := rank_ge_of_one (w := rot m w) (z := 0) (by omega) (by simpa using h)
  rw [show n - 1 - 0 = n - 1 by omega] at h2
  omega

lemma A0_firstOcc [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) : IsFirstOcc (A0 n) := by
  have h00 : A0 n 0 = false := by
    have := A0_nat (n := n) (t := 0) (by omega); simpa using this
  refine ⟨not_isConst_of _ ((1 : ℕ) : ZMod n) h00 (by rw [A0_nat (by omega)]; wbit), fun m => ?_⟩
  have hm : m = ((m.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val m).symm
  rcases Nat.eq_zero_or_pos m.val with hz | hpos
  · rw [hm, hz, Nat.cast_zero, rot_zero']
  by_cases hr : A0 n m = true
  · exact (rank_lt_of_rot_one (by omega) h00 m hr).le
  have hmv := ZMod.val_lt m
  have hr4 : m.val + 4 = n := by
    rw [hm, A0_nat hmv, decide_eq_true_eq] at hr; omega
  rw [hm]
  apply le_of_lt
  by_cases h7' : n = 7
  · subst h7'
    apply rank_lt_of_lex_even (s := 2) (by omega)
    · intro j hj
      rw [rot_natCast, A0_nat (by omega), A0_nat (by omega)]
      wbit
    · rw [cnt_lead01 h00 (fun j h1 h2 => by rw [A0_nat (by omega)]; wbit)]
    · rw [A0_nat (by omega)]; simp
    · rw [rot_natCast, A0_nat (by omega)]; wbit
  · apply rank_lt_of_lex_odd (s := 3) (by omega)
    · intro j hj
      rw [rot_natCast, A0_nat (by omega), A0_nat (by omega)]
      wbit
    · rw [cnt_lead01 h00 (fun j h1 h2 => by rw [A0_nat (by omega)]; wbit)]
    · rw [A0_nat (by omega)]; wbit
    · rw [rot_natCast, show 3 + 1 + m.val = n by omega, ZMod.natCast_self]; exact h00

lemma E1_firstOcc [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) : IsFirstOcc (E1 n) := by
  have h00 : E1 n 0 = false := by
    have := E1_nat (n := n) (t := 0) (by omega); simpa using this
  refine ⟨not_isConst_of _ ((1 : ℕ) : ZMod n) h00 (by rw [E1_nat (by omega)]; wbit), fun m => ?_⟩
  have hm : m = ((m.val : ℕ) : ZMod n) := (ZMod.natCast_zmod_val m).symm
  rcases Nat.eq_zero_or_pos m.val with hz | hpos
  · rw [hm, hz, Nat.cast_zero, rot_zero']
  by_cases hr : E1 n m = true
  · exact (rank_lt_of_rot_one (by omega) h00 m hr).le
  have hmv := ZMod.val_lt m
  have hr4 : m.val + 4 = n ∨ m.val + 2 = n := by
    rw [hm, E1_nat hmv, decide_eq_true_eq] at hr; omega
  rw [hm]
  apply le_of_lt
  apply rank_lt_of_lex_odd (s := 1) (by omega)
  · intro j hj
    rw [rot_natCast, E1_nat (by omega), E1_nat (by omega)]
    wbit
  · rw [cnt_lead01 h00 (fun j h1 h2 => by rw [E1_nat (by omega)]; wbit)]
  · rw [E1_nat (by omega)]; wbit
  · rcases hr4 with h | h
    · rw [rot_natCast, E1_nat (by omega)]; wbit
    · rw [rot_natCast, show 1 + 1 + m.val = n by omega, ZMod.natCast_self]; exact h00

/-! ### Lemma 3: the rank of `E_{k+1}` is one more than the rank of `A_k` -/

lemma rank_E1 [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) : rank (E1 n) = rank (A0 n) + 1 := by
  have h00 : A0 n 0 = false := by
    have := A0_nat (n := n) (t := 0) (by omega); simpa using this
  apply rank_succ_of_flip (by omega)
  · intro j hj
    rw [A0_nat (by omega), E1_nat (by omega)]
    wbit
  · rw [A0_nat (by omega)]; wbit
  · rw [E1_nat (by omega)]; wbit
  · rw [A0_nat (by omega)]; wbit
  · rw [E1_nat (by omega)]; wbit
  · have c1 : cnt (A0 n) (n - 5) = n - 5 :=
      cnt_lead01 h00 (fun j h1 h2 => by rw [A0_nat (by omega)]; wbit)
    have c2 : cnt (A0 n) (n - 5 + 1) = n - 5 := by
      rw [cnt_succ_false (i := n - 5) (by rw [A0_nat (by omega)]; wbit), c1]
    have c3 : cnt (A0 n) (n - 5 + 1 + 1) = n - 4 := by
      rw [cnt_succ_true (i := n - 5 + 1) (by rw [A0_nat (by omega)]; wbit), c2]; omega
    rw [show n - 3 = n - 5 + 1 + 1 by omega, c3]
    omega

lemma rank_Ek [NeZero n] (hodd : n % 2 = 1) {k : ℕ} (hk : 1 ≤ k) (hkn : 2 * k + 5 ≤ n) :
    rank (Ek n k) = rank (Ak n k) + 1 := by
  apply rank_succ_of_flip (by omega)
  · intro j hj
    rw [Ak_nat (by omega), Ek_nat (by omega)]
    wbit
  · rw [Ak_nat (by omega)]; wbit
  · rw [Ek_nat (by omega)]; wbit
  · rw [Ak_nat (by omega)]; wbit
  · rw [Ek_nat (by omega)]; wbit
  · have c1 : cnt (Ak n k) (2 * k) = 0 :=
      cnt_eq_zero (fun j hj => by rw [Ak_nat (by omega)]; wbit)
    have c2 : cnt (Ak n k) (2 * k + 1) = 1 := by
      rw [cnt_succ_true (i := 2 * k) (by rw [Ak_nat (by omega)]; wbit), c1]
    have c3 : cnt (Ak n k) (2 * k + 1 + 1) = 1 := by
      rw [cnt_succ_false (i := 2 * k + 1) (by rw [Ak_nat (by omega)]; wbit), c2]
    have c4 := cnt_ones (w := Ak n k) (s := 2 * k + 1 + 1) (t := n - 3 - (2 * k + 2))
      (fun j h1 h2 => by rw [Ak_nat (by omega)]; wbit)
    rw [c3, show 2 * k + 1 + 1 + (n - 3 - (2 * k + 2)) = n - 3 by omega] at c4
    rw [c4]
    omega


/-! ### Lemma 1 and Lemma 5: adjacencies -/

lemma A0_adj_E0 [NeZero n] (h7 : 7 ≤ n) : NecklaceAdj (A0 n) (E0 n) := by
  refine ⟨0, hammingDist_eq_one_of ((n - 4 : ℕ) : ZMod n) (fun i => ?_)⟩
  rw [rot_zero', eq_natCast_iff i (by omega)]
  have := ZMod.val_lt i
  simp only [A0, E0, ne_eq, decide_eq_decide]
  omega

lemma A1_adj_E1 [NeZero n] (h7 : 7 ≤ n) : NecklaceAdj (Ak n 1) (E1 n) := by
  refine ⟨((n - 4 : ℕ) : ZMod n), hammingDist_eq_one_of ((1 : ℕ) : ZMod n) (fun i => ?_)⟩
  rw [eq_natCast_iff i (by omega)]
  have := ZMod.val_lt i
  simp only [rot_apply_w, Ak, E1, ne_eq, decide_eq_decide]
  rw [val_add_natCast i (by omega)]
  split_ifs <;> omega

lemma Ak_adj_Ek [NeZero n] {j : ℕ} (hj : 1 ≤ j) (hjn : 2 * j + 7 ≤ n) :
    NecklaceAdj (Ak n (j + 1)) (Ek n j) := by
  refine ⟨((n - 2 : ℕ) : ZMod n), hammingDist_eq_one_of ((1 : ℕ) : ZMod n) (fun i => ?_)⟩
  rw [eq_natCast_iff i (by omega)]
  have := ZMod.val_lt i
  simp only [rot_apply_w, Ak, Ek, ne_eq, decide_eq_decide]
  rw [val_add_natCast i (by omega)]
  split_ifs <;> omega

lemma Ek_adj_sing [NeZero n] {j : ℕ} (hjn : 2 * j + 5 = n) : NecklaceAdj (Ek n j) (sing n) := by
  refine ⟨0, hammingDist_eq_one_of ((n - 4 : ℕ) : ZMod n) (fun i => ?_)⟩
  rw [rot_zero', eq_natCast_iff i (by omega)]
  have := ZMod.val_lt i
  simp only [Ek, sing, ne_eq, decide_eq_decide]
  omega

/-! ### The facts about `A n k` and `E n k` used by the closing argument -/

lemma A_firstOcc [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) {k : ℕ} (hkn : 2 * k + 5 ≤ n) :
    IsFirstOcc (A n k) := by
  unfold A
  split_ifs with hk
  · exact A0_firstOcc hodd h7
  · exact Ak_firstOcc (by omega) hkn

lemma E_succ_firstOcc [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) {k : ℕ} (hkn : 2 * k + 5 ≤ n) :
    IsFirstOcc (E n (k + 1)) := by
  rw [E_succ]
  split_ifs with hk
  · exact E1_firstOcc hodd h7
  · exact Ek_firstOcc (by omega) hkn

lemma E_firstOcc [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) {k : ℕ} (hkn : 2 * k + 3 ≤ n) :
    IsFirstOcc (E n k) := by
  rcases k with _ | k
  · exact E0_firstOcc (by omega)
  · exact E_succ_firstOcc hodd h7 (by omega)

lemma rank_E_succ [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) {k : ℕ} (hkn : 2 * k + 5 ≤ n) :
    rank (E n (k + 1)) = rank (A n k) + 1 := by
  rw [E_succ]
  unfold A
  split_ifs with hk
  · exact rank_E1 hodd h7
  · exact rank_Ek hodd (by omega) hkn

lemma A_adj_E [NeZero n] (h7 : 7 ≤ n) {k : ℕ} (hkn : 2 * k + 5 ≤ n) : NecklaceAdj (A n k) (E n k) := by
  rcases k with _ | _ | j
  · exact A0_adj_E0 h7
  · exact A1_adj_E1 h7
  · rw [E_succ]
    unfold A
    simp only [show j + 1 + 1 ≠ 0 by omega, show j + 1 ≠ 0 by omega, if_false]
    exact Ak_adj_Ek (by omega) (by omega)

lemma E_last_adj_sing [NeZero n] (hodd : n % 2 = 1) (h7 : 7 ≤ n) :
    NecklaceAdj (E n ((n - 3) / 2)) (sing n) := by
  obtain ⟨j, hj⟩ : ∃ j, (n - 3) / 2 = j + 2 := ⟨(n - 3) / 2 - 2, by omega⟩
  rw [hj, E_succ, if_neg (by omega)]
  exact Ek_adj_sing (by omega)

/-! ### Lemma 4: the pivots are in decreasing rank order -/

lemma rank_A_succ_lt [NeZero n] {k : ℕ} (hkn : 2 * k + 7 ≤ n) :
    rank (A n (k + 1)) + 1 < rank (A n k) := by
  have h1 : rank (A n (k + 1)) < 2 ^ (n - (2 * k + 3)) := by
    unfold A
    rw [if_neg (by omega)]
    exact rank_lt_of_zeros (by omega) (fun j hj => by rw [Ak_nat (by omega)]; wbit)
  have h2 : 2 ^ (n - 1 - (2 * k + 1)) ≤ rank (A n k) := by
    apply rank_ge_of_one (by omega)
    unfold A
    split_ifs
    · rw [A0_nat (by omega)]; wbit
    · rw [Ak_nat (by omega)]; wbit
  have h3 : 2 ^ (n - (2 * k + 3)) < 2 ^ (n - 1 - (2 * k + 1)) :=
    Nat.pow_lt_pow_right (by norm_num) (by omega)
  omega

/-! ### Lemma 0: `E0` has the largest rank among first occurrences -/

/-- A word beginning `0 1^a 0` with `a` even has smaller rank than `E0`. -/
lemma rank_lt_E0_of_gap [NeZero n] {v : Word n} {a : ℕ} (ha : a % 2 = 0) (han : a + 1 < n)
    (h0 : v 0 = false) (h1 : ∀ j, 0 < j → j ≤ a → v (j : ZMod n) = true)
    (h2 : v ((a + 1 : ℕ) : ZMod n) = false) : rank v < rank (E0 n) := by
  apply rank_lt_of_lex_even (s := a) han
  · intro j hj
    rcases Nat.eq_zero_or_pos j with rfl | hj0
    · rw [Nat.cast_zero, h0, ← Nat.cast_zero, E0_nat (by omega)]; wbit
    · rw [h1 j hj0 hj, E0_nat (by omega)]; wbit
  · rw [cnt_lead01 h0 h1]; exact ha
  · exact h2
  · rw [E0_nat han]; wbit

theorem rank_le_E0 [NeZero n] (hodd : n % 2 = 1) {w : Word n} (hw : IsFirstOcc w) :
    rank w ≤ rank (E0 n) := by
  classical
  by_contra hlt
  push Not at hlt
  obtain ⟨hnc, hmin⟩ := hw
  obtain ⟨z0, hz0⟩ : ∃ z0, w z0 = false := by
    by_contra h
    push Not at h
    apply hnc
    intro i j
    simp only [ne_eq, Bool.not_eq_false] at h
    rw [h i, h j]
  set x := rot z0 w with hx
  have hbig : ∀ m : ZMod n, rank (E0 n) < rank (rot m x) := fun m => by
    rw [hx, rot_rot']; exact lt_of_lt_of_le hlt (hmin _)
  have hx0 : x 0 = false := by simp [hx, hz0]
  -- no gap of ones of even length between two zeros
  have key : ∀ s a : ℕ, x (s : ZMod n) = false →
      (∀ j, 0 < j → j ≤ a → x ((j + s : ℕ) : ZMod n) = true) →
      x ((a + 1 + s : ℕ) : ZMod n) = false → a + 1 < n → a % 2 = 1 := by
    intro s a hs hrun hend han
    by_contra hev
    have := rank_lt_E0_of_gap (v := rot (s : ZMod n) x) (a := a) (by omega) han
      (by rw [← Nat.cast_zero, rot_natCast, zero_add]; exact hs)
      (fun j h1 h2 => by rw [rot_natCast]; exact hrun j h1 h2)
      (by rw [rot_natCast]; exact hend)
    exact absurd (hbig _) (not_lt.mpr this.le)
  -- all zeros of `x` are at even positions
  have hzeros : ∀ i, i < n → x (i : ZMod n) = false → i % 2 = 0 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi hxi
      rcases Nat.eq_zero_or_pos i with rfl | hpos
      · rfl
      · set i' := Nat.findGreatest (fun j => x (j : ZMod n) = false) (i - 1) with hi'
        have hi'1 : x (i' : ZMod n) = false :=
          Nat.findGreatest_spec (P := fun j => x (j : ZMod n) = false) (m := 0) (by omega)
            (by simpa using hx0)
        have hi'2 : i' ≤ i - 1 := Nat.findGreatest_le _
        have hi'3 : ∀ j, i' < j → j ≤ i - 1 → x (j : ZMod n) = true := fun j h1 h2 => by
          have := Nat.findGreatest_is_greatest h1 h2
          simpa using this
        have h1 := key i' (i - i' - 1) hi'1 (fun j h1 h2 => hi'3 _ (by omega) (by omega))
          (by rw [show i - i' - 1 + 1 + i' = i by omega]; exact hxi) (by omega)
        have h2 := ih i' (by omega) (by omega) hi'1
        omega
  -- the last zero
  set zl := Nat.findGreatest (fun j => x (j : ZMod n) = false) (n - 1) with hzl
  have hzl1 : x (zl : ZMod n) = false :=
    Nat.findGreatest_spec (P := fun j => x (j : ZMod n) = false) (m := 0) (by omega) (by simpa using hx0)
  have hzl2 : zl ≤ n - 1 := Nat.findGreatest_le _
  have hzl3 : ∀ j, zl < j → j ≤ n - 1 → x (j : ZMod n) = true := fun j h1 h2 => by
    have := Nat.findGreatest_is_greatest h1 h2
    simpa using this
  have hn0 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  by_cases hz : zl = 0
  · -- then `x = E0`, and `w` would have rank at most that of `E0`
    have hxE : x = E0 n := by
      funext i
      rw [← natCast_val_eq i]
      have hiv := ZMod.val_lt i
      rw [E0_nat hiv]
      rcases Nat.eq_zero_or_pos i.val with h | h
      · rw [h, Nat.cast_zero, hx0]; simp
      · rw [hzl3 _ (by omega) (by omega)]; exact (decide_eq_true (by omega)).symm
    have := hmin z0
    rw [← hx, hxE] at this
    omega
  · have h1 := key zl (n - 1 - zl) hzl1 (fun j h1 h2 => hzl3 _ (by omega) (by omega))
      (by rw [show n - 1 - zl + 1 + zl = n by omega, ZMod.natCast_self]; exact hx0) (by omega)
    have h2 := hzeros zl (by omega) hzl1
    omega

end STGC
