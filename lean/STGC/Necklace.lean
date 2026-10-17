/-
  Basic facts about rotations and necklaces, used by `Lift.lean`.

  * rotation lemmas (`rot_zero`, `rot_rot`, `hammingDist_rot`, `isConst_rot`);
  * aperiodicity for prime length (`eq_zero_of_rot_eq`);
  * the twin lemma of the shift fix (`twin`);
  * the count of nonconstant words (`card_nonconst`).
-/
import STGC.Interface

namespace STGC

variable {n : ℕ}

@[simp] lemma rot_apply (k : ZMod n) (w : Word n) (i : ZMod n) : rot k w i = w (i + k) := rfl

@[simp] lemma rot_zero (w : Word n) : rot 0 w = w := by
  funext i; simp [rot]

lemma rot_rot (a b : ZMod n) (w : Word n) : rot a (rot b w) = rot (a + b) w := by
  funext i; simp [rot, add_assoc]

lemma rot_neg_rot (k : ZMod n) (w : Word n) : rot (-k) (rot k w) = w := by
  rw [rot_rot, neg_add_cancel, rot_zero]

lemma rot_rot_neg (k : ZMod n) (w : Word n) : rot k (rot (-k) w) = w := by
  rw [rot_rot, add_neg_cancel, rot_zero]

lemma rot_injective (k : ZMod n) : Function.Injective (rot (n := n) k) := by
  intro u v h
  rw [← rot_neg_rot k u, h, rot_neg_rot]

lemma isConst_rot (k : ZMod n) (w : Word n) : IsConst (rot k w) ↔ IsConst w := by
  constructor
  · intro h i j
    have := h (i - k) (j - k)
    simpa using this
  · intro h i j
    exact h _ _

variable [NeZero n]

lemma hammingDist_rot (k : ZMod n) (u v : Word n) :
    hammingDist (rot k u) (rot k v) = hammingDist u v := by
  unfold hammingDist
  apply Finset.card_bij (fun i _ => i + k)
  · intro i hi; simpa [rot] using hi
  · intro a _ b _ h; simpa using h
  · intro b hb
    refine ⟨b - k, ?_, by simp⟩
    simpa [rot] using hb

lemma hammingDist_eq_one_iff (u v : Word n) :
    hammingDist u v = 1 ↔ ∃ b, ∀ i, (u i ≠ v i ↔ i = b) := by
  unfold hammingDist
  rw [Finset.card_eq_one]
  simp [Finset.ext_iff]

/-- Aperiodicity: for prime `n`, a nonconstant word is fixed by no nontrivial rotation. -/
lemma eq_zero_of_rot_eq (hn : n.Prime) {w : Word n} (hw : ¬ IsConst w) {k : ZMod n}
    (h : rot k w = w) : k = 0 := by
  haveI := Fact.mk hn
  by_contra hk
  apply hw
  have step : ∀ t : ℕ, ∀ i, w (i + (t : ZMod n) * k) = w i := by
    intro t
    induction t with
    | zero => intro i; simp
    | succ t ih =>
      intro i
      have := congrFun h (i + t * k)
      simp only [rot_apply] at this
      rw [Nat.cast_succ, add_mul, one_mul, ← add_assoc, this, ih]
  intro i j
  have := step ((j - i) * k⁻¹).val i
  rw [ZMod.natCast_zmod_val, mul_assoc, inv_mul_cancel₀ hk, mul_one, add_sub_cancel] at this
  exact this.symm

/-- The twin lemma (shift fix): a singleton word at distance one from a rotation of a nonconstant word `v` is at
distance one from a second, different rotation of `v`. -/
lemma twin {u v : Word n} (hu : IsSingleton u) (hv : ¬ IsConst v) {k : ZMod n}
    (h : hammingDist u (rot k v) = 1) : ∃ k', k' ≠ k ∧ hammingDist u (rot k' v) = 1 := by
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := (hammingDist_eq_one_iff _ _).1 h
  have hwc : ¬ IsConst (rot k v) := by rwa [isConst_rot]
  have hab : b ≠ a := by
    rintro rfl
    apply hwc
    have hf : ∀ i, rot k v i = false := by
      intro i
      have := hb i
      rw [ha] at this
      by_cases hi : i = b
      · subst hi; simpa using this
      · simp only [hi, decide_false, iff_false, ne_eq, not_not] at this
        exact this.symm
    intro i j; rw [hf, hf]
  have hw : ∀ i, rot k v i = decide (i = a ∨ i = b) := by
    intro i
    have := hb i
    rw [ha] at this
    by_cases h1 : i = a <;> by_cases h2 : i = b
    · exact absurd (h2.symm.trans h1) hab
    all_goals cases hr : rot k v i <;> simp_all
  refine ⟨(b - a) + k, ?_, ?_⟩
  · intro h'
    apply hab
    have : b - a = 0 := by simpa using h'
    exact sub_eq_zero.1 this
  · rw [← rot_rot, hammingDist_eq_one_iff]
    refine ⟨2 * a - b, fun i => ?_⟩
    rw [ha, rot_apply, hw]
    have e1 : i + (b - a) = a ↔ i = 2 * a - b := by
      constructor <;> intro h <;> linear_combination h
    have e2 : i + (b - a) = b ↔ i = a := by
      constructor <;> intro h <;> linear_combination h
    have hc : 2 * a - b ≠ a := by
      intro h; apply hab; linear_combination -h
    simp only [e1, e2]
    by_cases h1 : i = a
    · subst h1; simp [hc.symm]
    · by_cases h2 : i = 2 * a - b <;> simp [h1, h2, hc]

/-- There are exactly `2 ^ n - 2` nonconstant words of length `n`. -/
lemma card_nonconst : Nat.card {x : Word n // ¬ IsConst x} = 2 ^ n - 2 := by
  classical
  have h2 : Nat.card {x : Word n // IsConst x} = 2 := by
    have e : {x : Word n // IsConst x} ≃ Bool :=
      { toFun := fun x => x.1 0
        invFun := fun b => ⟨fun _ => b, fun _ _ => rfl⟩
        left_inv := by
          rintro ⟨x, hx⟩
          ext i
          exact hx 0 i
        right_inv := fun b => rfl }
    rw [Nat.card_congr e]; simp
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, h2]
  simp

end STGC
