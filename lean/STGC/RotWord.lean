/-
  Basic facts on rotations, Hamming distance and necklace adjacency, used by the closing argument.
-/
import STGC.Defs

namespace STGC

variable {n : ℕ}

@[simp] lemma rot_apply_w (k : ZMod n) (w : Word n) (i : ZMod n) : rot k w i = w (i + k) := rfl

@[simp] lemma rot_zero' (w : Word n) : rot 0 w = w := by
  funext i; simp

lemma rot_rot' (a b : ZMod n) (w : Word n) : rot a (rot b w) = rot (a + b) w := by
  funext i; simp [add_assoc]

lemma isConst_of_rot {k : ZMod n} {w : Word n} (h : IsConst (rot k w)) : IsConst w := by
  intro i j
  have := h (i - k) (j - k)
  simpa using this

/-- Value of `i + r` for a natural `r < n`. -/
lemma val_add_natCast [NeZero n] (i : ZMod n) {r : ℕ} (hr : r < n) :
    (i + (r : ZMod n)).val = if i.val + r < n then i.val + r else i.val + r - n := by
  rw [ZMod.val_add, ZMod.val_natCast, Nat.mod_eq_of_lt hr]
  have := ZMod.val_lt i
  split_ifs with h
  · exact Nat.mod_eq_of_lt h
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]

lemma val_natCast_of_lt {t : ℕ} (ht : t < n) : ((t : ℕ) : ZMod n).val = t := by
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt ht]

lemma eq_natCast_iff [NeZero n] (i : ZMod n) {c : ℕ} (hc : c < n) : i = (c : ZMod n) ↔ i.val = c := by
  constructor
  · rintro rfl; exact val_natCast_of_lt hc
  · intro h; rw [← h, ZMod.natCast_zmod_val]

lemma hammingDist_rot_rot [NeZero n] (k : ZMod n) (u v : Word n) :
    hammingDist (rot k u) (rot k v) = hammingDist u v := by
  unfold hammingDist
  apply Finset.card_bij (fun i _ => i + k)
  · intro a ha; simpa using ha
  · intro a _ b _ h; simpa using h
  · intro b hb
    refine ⟨b - k, ?_, by simp⟩
    simpa using hb

lemma hammingDist_eq_one_of [NeZero n] {u v : Word n} (a : ZMod n) (h : ∀ i, u i ≠ v i ↔ i = a) :
    hammingDist u v = 1 := by
  unfold hammingDist
  rw [Finset.card_eq_one]
  refine ⟨a, ?_⟩
  ext i
  simp [h]

lemma necklaceAdj_symm [NeZero n] {u v : Word n} (h : NecklaceAdj u v) : NecklaceAdj v u := by
  obtain ⟨k, hk⟩ := h
  refine ⟨-k, ?_⟩
  rw [← hammingDist_rot_rot k, rot_rot', add_neg_cancel, rot_zero', hammingDist_comm, hk]

lemma necklaceAdj_rot_left [NeZero n] {u v : Word n} (m : ZMod n) (h : NecklaceAdj (rot m u) v) :
    NecklaceAdj u v := by
  obtain ⟨k, hk⟩ := h
  refine ⟨k - m, ?_⟩
  rw [← hammingDist_rot_rot m, rot_rot', add_sub_cancel, hk]

lemma rot_natCast (r j : ℕ) (w : Word n) :
    rot (r : ZMod n) w (j : ZMod n) = w ((j + r : ℕ) : ZMod n) := by
  simp [Nat.cast_add]

end STGC
