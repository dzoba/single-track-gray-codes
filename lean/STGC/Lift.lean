/-
  Lemma V (lifting): for prime `n`, a Hamilton cycle of the necklace graph gives a single-track Gray code of length
  `n` and period `2 ^ n - 2`.  Paper: Lemma V (with the shift fix), PROOF.md "Lemma V".
-/
import STGC.Necklace

namespace STGC

set_option linter.unusedSectionVars false

variable {n m : ℕ} [NeZero n] [NeZero m]

section Walk

variable (rep : ZMod m → Word n) (k : ZMod m → ZMod n)

/-- The offset of the `j`-th word of the lifted walk: `o j = ∑_{i<j} k i`. -/
def offs (j : ℕ) : ZMod n := ∑ i ∈ Finset.range j, k (i : ZMod m)

/-- The `j`-th word of the lifted walk. -/
def walk (j : ℕ) : Word n := rot (offs k j) (rep (j : ZMod m))

lemma offs_succ (j : ℕ) : offs k (j + 1) = offs k j + k (j : ZMod m) :=
  Finset.sum_range_succ _ _

lemma offs_add_m (j : ℕ) : offs k (j + m) = offs k j + offs k m := by
  induction j with
  | zero => simp [offs]
  | succ j ih =>
    rw [Nat.add_right_comm, offs_succ, ih, offs_succ]
    have : ((j + m : ℕ) : ZMod m) = (j : ZMod m) := by simp
    rw [this]; ring

lemma walk_add_m (j : ℕ) : walk rep k (j + m) = rot (offs k m) (walk rep k j) := by
  unfold walk
  rw [offs_add_m, rot_rot, add_comm (offs k m)]
  congr 2
  simp

lemma walk_add_mul (j c : ℕ) :
    walk rep k (j + c * m) = rot ((c : ZMod n) * offs k m) (walk rep k j) := by
  induction c with
  | zero => simp
  | succ c ih =>
    rw [Nat.succ_mul, ← add_assoc, walk_add_m, ih, rot_rot]
    congr 1
    push_cast; ring

lemma walk_mod (j : ℕ) : walk rep k (j % (n * m)) = walk rep k j := by
  conv_rhs => rw [← Nat.mod_add_div j (n * m)]
  rw [show n * m * (j / (n * m)) = (n * (j / (n * m))) * m by ring, walk_add_mul]
  simp

lemma walk_eq (j : ℕ) :
    walk rep k j = rot (((j / m : ℕ) : ZMod n) * offs k m + offs k (j % m)) (rep (j : ZMod m)) := by
  conv_lhs => rw [← Nat.mod_add_div' j m]
  rw [walk_add_mul, walk, rot_rot]
  congr 2
  simp

lemma walk_step (hk : ∀ i, hammingDist (rep i) (rot (k i) (rep (i + 1))) = 1) (j : ℕ) :
    hammingDist (walk rep k j) (walk rep k (j + 1)) = 1 := by
  unfold walk
  rw [offs_succ, ← rot_rot, hammingDist_rot, Nat.cast_succ]
  exact hk _

end Walk

section Code

variable (H : HamCycle n m) (k : ZMod m → ZMod n)

lemma walk_nonconst (j : ℕ) : ¬ IsConst (walk H.rep k j) := by
  unfold walk; rw [isConst_rot]; exact H.nonconst _

lemma walk_inj (hn : n.Prime) (hs : offs k m ≠ 0) {j j' : ℕ} (hj : j < n * m) (hj' : j' < n * m)
    (h : walk H.rep k j = walk H.rep k j') : j = j' := by
  haveI := Fact.mk hn
  rw [walk_eq, walk_eq] at h
  set A := ((j / m : ℕ) : ZMod n) * offs k m + offs k (j % m)
  set A' := ((j' / m : ℕ) : ZMod n) * offs k m + offs k (j' % m)
  have h1 : rot (A - A') (H.rep (j : ZMod m)) = H.rep (j' : ZMod m) := by
    have := congrArg (rot (-A')) h
    rw [rot_neg_rot, rot_rot] at this
    rwa [sub_eq_neg_add]
  have hjm : (j : ZMod m) = (j' : ZMod m) := H.distinct _ _ _ h1
  have hr : j % m = j' % m := (ZMod.natCast_eq_natCast_iff' _ _ _).1 hjm
  rw [← hjm] at h1
  have hA : A - A' = 0 := eq_zero_of_rot_eq hn (H.nonconst _) h1
  have hq : ((j / m : ℕ) : ZMod n) = ((j' / m : ℕ) : ZMod n) := by
    have : ((j / m : ℕ) : ZMod n) * offs k m = ((j' / m : ℕ) : ZMod n) * offs k m := by
      have := sub_eq_zero.1 hA
      simp only [A, A', hr] at this
      exact add_right_cancel this
    exact mul_right_cancel₀ hs this
  have hq' : j / m = j' / m := by
    rw [ZMod.natCast_eq_natCast_iff'] at hq
    have h1 : j / m < n := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    have h2 : j' / m < n := Nat.div_lt_of_lt_mul (by rwa [mul_comm])
    rwa [Nat.mod_eq_of_lt h1, Nat.mod_eq_of_lt h2] at hq
  rw [← Nat.mod_add_div j m, ← Nat.mod_add_div j' m, hr, hq']

lemma walk_surj (hn : n.Prime) (hs : offs k m ≠ 0) (x : Word n) (hx : ¬ IsConst x) :
    ∃ j : ℕ, walk H.rep k j = x := by
  haveI := Fact.mk hn
  obtain ⟨i, κ, rfl⟩ := H.cover x hx
  refine ⟨i.val + ((κ - offs k i.val) * (offs k m)⁻¹).val * m, ?_⟩
  rw [walk_add_mul, walk, rot_rot, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hs, mul_one, sub_add_cancel]

lemma walk_val_add (t : ZMod (n * m)) (x : ℕ) :
    walk H.rep k (t + (x : ZMod (n * m))).val = walk H.rep k (t.val + x) := by
  rw [ZMod.val_add, ZMod.val_natCast, walk_mod, ← walk_mod, Nat.add_mod_mod, walk_mod]

/-- The single-track Gray code built from the lifted walk, when the total shift is nonzero. -/
def code (hn : n.Prime) (hk : ∀ i, hammingDist (H.rep i) (rot (k i) (H.rep (i + 1))) = 1)
    (hs : offs k m ≠ 0) : SingleTrackGrayCode n (n * m) where
  word t := walk H.rep k t.val
  injective := by
    intro t t' h
    exact ZMod.val_injective _ (walk_inj H k hn hs (ZMod.val_lt t) (ZMod.val_lt t') h)
  oneBitSteps := by
    intro t
    have := walk_val_add H k t 1
    rw [Nat.cast_one] at this
    show hammingDist (walk H.rep k t.val) (walk H.rep k (t + 1).val) = 1
    rw [this]
    exact walk_step H.rep k hk _
  heads j := (((j * (offs k m)⁻¹).val * m : ℕ) : ZMod (n * m))
  singleTrack := by
    intro t j
    haveI := Fact.mk hn
    show walk H.rep k t.val j = walk H.rep k (t + (((j * (offs k m)⁻¹).val * m : ℕ) : ZMod (n * m))).val 0
    have := walk_val_add H k t ((j * (offs k m)⁻¹).val * m)
    rw [this, walk_add_mul, rot_apply, ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hs, mul_one,
      zero_add]

include H in
/-- The period equals the number of nonconstant words: `n * m = 2 ^ n - 2`. -/
lemma period_eq (hn : n.Prime) (hs : offs k m ≠ 0) : n * m = 2 ^ n - 2 := by
  let F : ZMod (n * m) → {x : Word n // ¬ IsConst x} := fun t => ⟨walk H.rep k t.val, walk_nonconst H k _⟩
  have hF : Function.Bijective F := by
    constructor
    · intro t t' h
      exact ZMod.val_injective _
        (walk_inj H k hn hs (ZMod.val_lt t) (ZMod.val_lt t') (congrArg Subtype.val h))
    · rintro ⟨x, hx⟩
      obtain ⟨j, rfl⟩ := walk_surj H k hn hs x hx
      refine ⟨(j : ZMod (n * m)), ?_⟩
      apply Subtype.ext
      simp only [F]
      rw [ZMod.val_natCast, walk_mod]
  rw [← card_nonconst, ← Nat.card_eq_of_bijective F hF, Nat.card_zmod]

/-- The shift fix: the connecting rotations can be chosen with nonzero total shift. -/
lemma exists_shifts : ∃ k : ZMod m → ZMod n,
    (∀ i, hammingDist (H.rep i) (rot (k i) (H.rep (i + 1))) = 1) ∧ offs k m ≠ 0 := by
  classical
  choose k0 hk0 using H.adj
  obtain ⟨k', hk'ne, hk'⟩ := twin H.start (H.nonconst _) (hk0 0)
  obtain ⟨m', hm'⟩ : ∃ m', m = m' + 1 := Nat.exists_eq_succ_of_ne_zero (NeZero.ne m)
  subst hm'
  set R : ZMod n := ∑ i ∈ Finset.range m', k0 ((i + 1 : ℕ) : ZMod (m' + 1)) with hR
  have hsum : ∀ κ, offs (Function.update k0 0 κ) (m' + 1) = R + κ := by
    intro κ
    unfold offs
    rw [Finset.sum_range_succ']
    congr 1
    · apply Finset.sum_congr rfl
      intro i hi
      rw [Function.update_of_ne]
      intro h0
      rw [ZMod.natCast_eq_zero_iff] at h0
      have := Nat.le_of_dvd (Nat.succ_pos _) h0
      simp only [Finset.mem_range] at hi; omega
  have hadj : ∀ κ, hammingDist (H.rep 0) (rot κ (H.rep (0 + 1))) = 1 →
      ∀ i, hammingDist (H.rep i) (rot (Function.update k0 0 κ i) (H.rep (i + 1))) = 1 := by
    intro κ hκ i
    by_cases hi : i = 0
    · subst hi; simpa using hκ
    · rw [Function.update_of_ne hi]; exact hk0 i
  by_cases h0 : R + k0 0 = 0
  · refine ⟨Function.update k0 0 k', hadj _ hk', ?_⟩
    rw [hsum]
    intro h
    apply hk'ne
    have := h.trans h0.symm
    exact add_left_cancel this
  · exact ⟨Function.update k0 0 (k0 0), hadj _ (hk0 0), by rwa [hsum]⟩

end Code

/-- **Lemma V.** For prime `n`, a Hamilton cycle of the necklace graph yields a single-track Gray code of length `n`
and period `2 ^ n - 2`. -/
theorem stgc_of_hamCycle {n m : ℕ} [NeZero n] [NeZero m] (hn : n.Prime) (H : HamCycle n m) :
    Nonempty (SingleTrackGrayCode n (2 ^ n - 2)) := by
  obtain ⟨k, hk, hs⟩ := exists_shifts H
  rw [← period_eq H k hn hs]
  exact ⟨code H k hn hk hs⟩

end STGC
