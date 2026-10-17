/-
  The Pósa rotation of a path, for lists: keep `l[0..j]` and reverse the rest. If `l[j]` is adjacent to the last
  element, the result is again a path through the same elements, now ending at `l[j+1]`.
-/
import Mathlib

namespace STGC

open List

variable {α : Type*}

/-- The Pósa rotation at pivot index `j`: `l[0..j] ++ reverse l[j+1..]`. -/
def posa (l : List α) (j : ℕ) : List α := l.take (j + 1) ++ (l.drop (j + 1)).reverse

lemma posa_perm (l : List α) (j : ℕ) : (posa l j).Perm l := by
  unfold posa
  calc (l.take (j + 1) ++ (l.drop (j + 1)).reverse).Perm (l.take (j + 1) ++ l.drop (j + 1)) :=
        Perm.append_left _ (reverse_perm _)
    _ = l := take_append_drop _ _

lemma posa_length (l : List α) (j : ℕ) : (posa l j).length = l.length := (posa_perm l j).length_eq

lemma posa_getElem?_le (l : List α) {j i : ℕ} (hij : i ≤ j) : (posa l j)[i]? = l[i]? := by
  unfold posa
  by_cases hi : i < l.length
  · rw [getElem?_append_left (by simp; omega), getElem?_take, if_pos (by omega)]
  · have h1 : l[i]? = none := getElem?_eq_none (by omega)
    have h2 : (l.take (j + 1) ++ (l.drop (j + 1)).reverse)[i]? = none :=
      getElem?_eq_none (by simp; omega)
    rw [h1, h2]

lemma posa_getElem?_last (l : List α) {j : ℕ} (hj : j + 1 < l.length) :
    (posa l j)[l.length - 1]? = l[j + 1]? := by
  unfold posa
  rw [getElem?_append_right (by simp; omega), getElem?_reverse (by simp; omega), getElem?_drop]
  congr 1
  simp
  omega

lemma posa_isChain {R : α → α → Prop} (hsymm : ∀ a b, R a b → R b a) {l : List α} (hl : IsChain R l)
    {j : ℕ} (hj : j + 1 < l.length)
    (hpiv : ∀ a b, l[j]? = some a → l[l.length - 1]? = some b → R a b) : IsChain R (posa l j) := by
  unfold posa
  rw [isChain_append]
  refine ⟨hl.take _, ?_, ?_⟩
  · rw [isChain_reverse]
    exact (hl.drop _).imp (fun a b h => hsymm a b h)
  · intro x hx y hy
    rw [getLast?_eq_getElem?, getElem?_take] at hx
    rw [head?_reverse, getLast?_eq_getElem?, getElem?_drop] at hy
    simp only [length_take, length_drop] at hx hy
    rw [if_pos (by omega), show min (j + 1) l.length - 1 = j by omega] at hx
    rw [show j + 1 + (l.length - (j + 1) - 1) = l.length - 1 by omega] at hy
    exact hpiv x y hx hy

end STGC
