/-
  The closing argument (paper, Theorem): DD(n) for odd n ≥ 7 gives a Hamilton cycle of the necklace graph.

  `D` is the list of first-occurrence words in increasing rank (the Degni–Drisko list). DD makes it a Hamilton
  path from `0^{n-1}1` to `0 1^{n-1}` (Lemma 0). K = (n-3)/2 Pósa rotations at the pivots A_0, …, A_{K-1} move its end
  to E_K = 0^{n-4}1001, which is adjacent to the start (Lemma 5).
-/
import STGC.Words
import STGC.Posa
import STGC.Interface

namespace STGC

open List Classical

variable {n : ℕ} [NeZero n]

/-! ### Two first occurrences of one necklace are equal -/

lemma firstOcc_rot_eq {u v : Word n} (hu : IsFirstOcc u) (hv : IsFirstOcc v) {k : ZMod n}
    (h : rot k u = v) : u = v := by
  subst h
  apply rank_injective
  have h1 := hu.2 k
  have h2 := hv.2 (-k)
  rw [rot_rot', neg_add_cancel, rot_zero'] at h2
  omega

/-- Every nonconstant word has a rotation that is a first occurrence. -/
lemma exists_firstOcc_rot {x : Word n} (hx : ¬ IsConst x) : ∃ k : ZMod n, IsFirstOcc (rot k x) := by
  obtain ⟨k, -, hk⟩ := Finset.exists_min_image Finset.univ (fun k : ZMod n => rank (rot k x))
    Finset.univ_nonempty
  refine ⟨k, fun h => hx (isConst_of_rot h), fun m => ?_⟩
  rw [rot_rot']
  exact hk _ (Finset.mem_univ _)

/-! ### The Degni–Drisko list -/

/-- The first occurrence of rank `r`, if there is one. -/
noncomputable def foOf (n : ℕ) [NeZero n] (r : ℕ) : Option (Word n) :=
  if h : ∃ w : Word n, IsFirstOcc w ∧ rank w = r then some (Classical.choose h) else none

lemma foOf_spec {r : ℕ} {w : Word n} (h : foOf n r = some w) : IsFirstOcc w ∧ rank w = r := by
  unfold foOf at h
  split_ifs at h with hex
  · cases h
    exact Classical.choose_spec hex

/-- The first-occurrence words, sorted by rank. -/
noncomputable def DList (n : ℕ) [NeZero n] : List (Word n) := (List.range (2 ^ n)).filterMap (foOf n)

lemma mem_DList {w : Word n} : w ∈ DList n ↔ IsFirstOcc w := by
  unfold DList
  rw [mem_filterMap]
  constructor
  · rintro ⟨r, -, hr⟩
    exact (foOf_spec hr).1
  · intro hw
    refine ⟨rank w, mem_range.mpr (rank_lt_pow w), ?_⟩
    have hex : ∃ w' : Word n, IsFirstOcc w' ∧ rank w' = rank w := ⟨w, hw, rfl⟩
    unfold foOf
    rw [dif_pos hex]
    congr 1
    exact rank_injective (Classical.choose_spec hex).2

lemma DList_pairwise : (DList n).Pairwise (fun u v => rank u < rank v) := by
  unfold DList
  rw [pairwise_filterMap]
  apply pairwise_lt_range.imp
  intro a b hab u hu v hv
  rw [(foOf_spec hu).2, (foOf_spec hv).2]
  exact hab

/-! ### Generic facts on a list sorted by rank -/

section Sorted

omit [NeZero n]

variable {l : List (Word n)} (hs : l.Pairwise (fun u v => rank u < rank v))
include hs

lemma sorted_lt_of_lt {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    rank l[i] < rank l[j] :=
  pairwise_iff_getElem.mp hs i j hi hj hij

lemma sorted_idx_lt {i j : ℕ} (hi : i < l.length) (hj : j < l.length) (h : rank l[i] < rank l[j]) : i < j := by
  by_contra hc
  rcases Nat.lt_or_ge j i with h' | h'
  · have := sorted_lt_of_lt hs hj hi h'; omega
  · have : i = j := by omega
    subst this; omega

lemma sorted_no_between {i : ℕ} (hi : i + 1 < l.length) {x : Word n} (hx : x ∈ l) :
    ¬ (rank l[i] < rank x ∧ rank x < rank l[i + 1]) := by
  rintro ⟨h1, h2⟩
  obtain ⟨j, hj, rfl⟩ := mem_iff_getElem.mp hx
  have a := sorted_idx_lt hs (by omega) hj h1
  have b := sorted_idx_lt hs hj hi h2
  omega

lemma sorted_next {i : ℕ} (hi : i < l.length) {v : Word n} (hv : v ∈ l) (hr : rank v = rank l[i] + 1) :
    ∃ h : i + 1 < l.length, l[i + 1] = v := by
  obtain ⟨j, hj, rfl⟩ := mem_iff_getElem.mp hv
  have hij := sorted_idx_lt hs hi hj (by omega)
  by_cases hji : j = i + 1
  · subst hji; exact ⟨hj, rfl⟩
  · exfalso
    have a := sorted_lt_of_lt hs hi (show i + 1 < l.length by omega) (by omega)
    have b := sorted_lt_of_lt hs (show i + 1 < l.length by omega) hj (by omega)
    omega

end Sorted

/-- Under DD, consecutive entries of `D` are adjacent. -/
lemma DList_chain (hDD : DDProperty n) : IsChain NecklaceAdj (DList n) := by
  rw [isChain_iff_getElem]
  intro i hi
  apply hDD
  · exact mem_DList.mp (getElem_mem _)
  · exact mem_DList.mp (getElem_mem _)
  · exact sorted_lt_of_lt DList_pairwise _ _ (by omega)
  · intro x hx
    exact sorted_no_between DList_pairwise hi (mem_DList.mpr hx)

/-! ### The Hamilton cycle from a closed Hamilton path of first occurrences -/

lemma val_add_one_of_lt {m : ℕ} [NeZero m] (i : ZMod m) (h : i.val + 1 < m) : (i + 1).val = i.val + 1 := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod, Nat.mod_eq_of_lt h]

lemma val_add_one_of_eq {m : ℕ} [NeZero m] (i : ZMod m) (h : i.val + 1 = m) : (i + 1).val = 0 := by
  rw [ZMod.val_add, ZMod.val_one_eq_one_mod, Nat.add_mod_mod, h, Nat.mod_self]

lemma isSingleton_sing (hn : 2 ≤ n) : IsSingleton (sing n) := by
  refine ⟨((n - 1 : ℕ) : ZMod n), fun i => ?_⟩
  have := ZMod.val_lt i
  simp only [sing, eq_natCast_iff i (show n - 1 < n by omega), decide_eq_decide]
  omega

lemma hamCycle_of_list (hn : 2 ≤ n) (L : List (Word n)) (hperm : L.Perm (DList n))
    (hchain : IsChain NecklaceAdj L) {e : Word n} (hlast : L[L.length - 1]? = some e)
    (hhead : L[0]? = some (sing n)) (hwrap : NecklaceAdj e (sing n)) :
    ∃ (m : ℕ) (_ : NeZero m), Nonempty (HamCycle n m) := by
  have hlen : 0 < L.length := by
    rcases L with _ | _
    · simp at hhead
    · simp
  have hnd : L.Nodup := hperm.nodup_iff.mpr (DList_pairwise.imp (fun {a b} h heq => by subst heq; omega))
  haveI : NeZero L.length := ⟨by omega⟩
  have hmemL : ∀ w, w ∈ L ↔ IsFirstOcc w := fun w => by rw [hperm.mem_iff, mem_DList]
  refine ⟨L.length, inferInstance, ⟨{
    rep := fun i => L[i.val]'(ZMod.val_lt i)
    nonconst := fun i => ((hmemL _).mp (getElem_mem _)).1
    cover := ?_
    distinct := ?_
    adj := ?_
    start := ?_ }⟩⟩
  · intro x hx
    obtain ⟨k, hk⟩ := exists_firstOcc_rot hx
    obtain ⟨i, hi, hLi⟩ := mem_iff_getElem.mp ((hmemL _).mpr hk)
    refine ⟨(i : ZMod L.length), -k, ?_⟩
    have hv : ((i : ℕ) : ZMod L.length).val = i := val_natCast_of_lt hi
    simp only [hv, hLi, rot_rot', neg_add_cancel, rot_zero']
  · intro i j k h
    have hi := (hmemL _).mp (getElem_mem (ZMod.val_lt i))
    have hj := (hmemL _).mp (getElem_mem (ZMod.val_lt j))
    have heq := firstOcc_rot_eq hi hj h
    exact ZMod.val_injective _ ((hnd.getElem_inj_iff).mp heq)
  · intro i
    have hi := ZMod.val_lt i
    by_cases h : i.val + 1 < L.length
    · have hv := val_add_one_of_lt i h
      simp only [hv]
      exact isChain_iff_getElem.mp hchain i.val h
    · have hv := val_add_one_of_eq i (by omega)
      simp only [hv]
      have h1 : L[i.val] = e := by
        rw [getElem_eq_iff, show i.val = L.length - 1 by omega]; exact hlast
      have h2 : L[0] = sing n := by rw [getElem_eq_iff]; exact hhead
      rw [h1, h2]
      exact hwrap
  · show IsSingleton (L[(0 : ZMod L.length).val]'(ZMod.val_lt _))
    have h2 : L[0] = sing n := by rw [getElem_eq_iff]; exact hhead
    simp only [ZMod.val_zero, h2]
    exact isSingleton_sing hn


/-! ### The Pósa rotations -/

/-- The index of the pivot `A_k` in `D`. -/
noncomputable def pivIdx (n : ℕ) [NeZero n] (k : ℕ) : ℕ := (DList n).idxOf (A n k)

/-- The path after `k` rotations. -/
noncomputable def path (n : ℕ) [NeZero n] : ℕ → List (Word n)
  | 0 => DList n
  | k + 1 => posa (path n k) (pivIdx n k)

/-- The prefix of `D` that is untouched after `k` rotations. -/
noncomputable def bound (n : ℕ) [NeZero n] : ℕ → ℕ
  | 0 => (DList n).length
  | k + 1 => pivIdx n k + 1

lemma pivIdx_spec (hodd : n % 2 = 1) (h7 : 7 ≤ n) {k : ℕ} (hkn : 2 * k + 5 ≤ n) :
    ∃ h : pivIdx n k < (DList n).length, (DList n)[pivIdx n k] = A n k := by
  have hmem : A n k ∈ DList n := mem_DList.mpr (A_firstOcc hodd h7 hkn)
  exact ⟨idxOf_lt_length_of_mem hmem, getElem_idxOf _⟩

lemma DList_last (hodd : n % 2 = 1) (h7 : 7 ≤ n) :
    (DList n)[(DList n).length - 1]? = some (E0 n) := by
  obtain ⟨p, hp, hpe⟩ := mem_iff_getElem.mp (mem_DList.mpr (E0_firstOcc (n := n) (by omega)))
  have : p = (DList n).length - 1 := by
    by_contra hne
    have h1 := sorted_lt_of_lt DList_pairwise hp (show (DList n).length - 1 < (DList n).length by omega)
      (by omega)
    have h2 := rank_le_E0 hodd (mem_DList.mp (getElem_mem (show (DList n).length - 1 < (DList n).length by omega)))
    rw [hpe] at h1
    omega
  subst this
  rw [getElem?_eq_getElem hp, hpe]

lemma DList_head (h7 : 7 ≤ n) : (DList n)[0]? = some (sing n) := by
  obtain ⟨p, hp, hpe⟩ := mem_iff_getElem.mp (mem_DList.mpr (sing_firstOcc (n := n) (by omega)))
  have : p = 0 := by
    by_contra hne
    have h1 := sorted_lt_of_lt DList_pairwise (show 0 < (DList n).length by omega) hp (by omega)
    have h2 := rank_sing_le (n := n) (by omega) (mem_DList.mp (getElem_mem (show 0 < (DList n).length by omega))).1
    rw [hpe] at h1
    omega
  subst this
  rw [getElem?_eq_getElem hp, hpe]

lemma path_inv (hodd : n % 2 = 1) (h7 : 7 ≤ n) (hDD : DDProperty n) :
    ∀ k, 2 * k + 3 ≤ n →
      (path n k).Perm (DList n) ∧ IsChain NecklaceAdj (path n k) ∧
      (path n k)[(DList n).length - 1]? = some (E n k) ∧
      (∀ i < bound n k, (path n k)[i]? = (DList n)[i]?) := by
  intro k
  induction k with
  | zero =>
    intro _
    exact ⟨Perm.refl _, DList_chain hDD, DList_last hodd h7, fun _ _ => rfl⟩
  | succ k ih =>
    intro hkn
    obtain ⟨hperm, hchain, hlast, hpre⟩ := ih (by omega)
    obtain ⟨hj, hjA⟩ := pivIdx_spec (k := k) hodd h7 (by omega)
    set j := pivIdx n k with hjdef
    have hEmem : E n (k + 1) ∈ DList n := mem_DList.mpr (E_succ_firstOcc hodd h7 (by omega))
    obtain ⟨hj1, hjE⟩ := sorted_next DList_pairwise hj hEmem (by rw [hjA, rank_E_succ hodd h7 (by omega)])
    have hbound : j + 1 < bound n k := by
      rcases k with _ | k'
      · exact hj1
      · obtain ⟨hj', hj'A⟩ := pivIdx_spec (k := k') hodd h7 (by omega)
        show j + 1 < pivIdx n k' + 1
        have hlt : rank (DList n)[j + 1] < rank (DList n)[pivIdx n k'] := by
          rw [hjE, hj'A, rank_E_succ hodd h7 (by omega)]
          exact rank_A_succ_lt (by omega)
        have := sorted_idx_lt DList_pairwise hj1 hj' hlt
        omega
    have hlen : (path n k).length = (DList n).length := hperm.length_eq
    have hPj : (path n k)[j]? = some (A n k) := by
      rw [hpre j (by omega), getElem?_eq_getElem hj, hjA]
    have hPj1 : (path n k)[j + 1]? = some (E n (k + 1)) := by
      rw [hpre (j + 1) hbound, getElem?_eq_getElem hj1, hjE]
    refine ⟨(posa_perm _ _).trans hperm, ?_, ?_, ?_⟩
    · apply posa_isChain (fun a b h => necklaceAdj_symm h) hchain (by omega)
      intro a b ha hb
      rw [hlen, hlast] at hb
      rw [hPj] at ha
      cases ha
      cases hb
      exact A_adj_E h7 (by omega)
    · show (posa (path n k) j)[(DList n).length - 1]? = some (E n (k + 1))
      rw [← hlen, posa_getElem?_last _ (by omega), hPj1]
    · intro i hi
      show (posa (path n k) j)[i]? = (DList n)[i]?
      have hi' : i < j + 1 := hi
      rw [posa_getElem?_le _ (by omega), hpre i (by omega)]

theorem hamCycle_of_DD' (hodd : n % 2 = 1) (h7 : 7 ≤ n) (hDD : DDProperty n) :
    ∃ (m : ℕ) (_ : NeZero m), Nonempty (HamCycle n m) := by
  obtain ⟨hperm, hchain, hlast, hpre⟩ := path_inv hodd h7 hDD ((n - 3) / 2) (by omega)
  have hlen : (path n ((n - 3) / 2)).length = (DList n).length := hperm.length_eq
  apply hamCycle_of_list (by omega) (path n ((n - 3) / 2)) hperm hchain (e := E n ((n - 3) / 2))
  · rw [hlen]; exact hlast
  · rw [hpre 0 ?_, DList_head h7]
    obtain ⟨K, hK⟩ : ∃ K, (n - 3) / 2 = K + 1 := ⟨(n - 3) / 2 - 1, by omega⟩
    rw [hK]
    show 0 < pivIdx n K + 1
    omega
  · exact E_last_adj_sing hodd h7

/-- **Closing theorem.** For odd `n ≥ 7`, the Degni–Drisko property gives a Hamilton cycle of the necklace
graph. -/
theorem hamCycle_of_DD {n : ℕ} [NeZero n] (hodd : Odd n) (h7 : 7 ≤ n) (hDD : DDProperty n) :
    ∃ (m : ℕ) (_ : NeZero m), Nonempty (HamCycle n m) :=
  hamCycle_of_DD' (Nat.odd_iff.mp hodd) h7 hDD

end STGC
