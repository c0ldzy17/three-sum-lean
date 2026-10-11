import Submission.ThreeSum.SubsetAddress

/-!
# Deleting one coordinate from an integer subset mask

The routine inspects the highest remaining power of two at each recursive
step. It uses no division or scan proportional to the mask's numeric value.
-/

namespace ThreeSum.MaskErase

open Finset
open scoped BigOperators
open SubsetAddress

def eraseMask : ℕ → ℕ → ℕ → ℕ
  | 0, _, _ => 0
  | L+1, a, m =>
    if m < 2^L then eraseMask L a m
    else if a = L then m-2^L
    else 2^L + eraseMask L a (m-2^L)

theorem eraseMask_le {L a m : ℕ} (hm : m < 2^L) : eraseMask L a m ≤ m := by
  induction L generalizing m with
  | zero => simp [eraseMask]
  | succ L ih =>
    by_cases hlo : m < 2^L
    · simpa only [eraseMask, hlo, ite_true] using ih hlo
    · have hm' : m-2^L < 2^L := by rw [pow_succ] at hm; omega
      rw [eraseMask, if_neg hlo]
      split
      · exact Nat.sub_le _ _
      · have hh := ih hm'
        omega

private theorem subset_range_pred {L : ℕ} {s : Finset ℕ}
    (hs : s ⊆ Finset.range (L+1)) (hL : L ∉ s) : s ⊆ Finset.range L := by
  intro i hi
  have h := Finset.mem_range.mp (hs hi)
  have hn : i ≠ L := by rintro rfl; exact hL hi
  exact Finset.mem_range.mpr (by omega)

theorem eraseMask_maskOf {L : ℕ} (s : Finset ℕ) (hs : s ⊆ Finset.range L) (a : ℕ) :
    eraseMask L a (maskOf s) = maskOf (s.erase a) := by
  induction L generalizing s with
  | zero =>
    have he : s = ∅ := by simpa using hs
    subst s
    simp [eraseMask, maskOf]
  | succ L ih =>
    by_cases hL : L ∈ s
    · have ht : s.erase L ⊆ Finset.range L :=
        subset_range_pred ((Finset.erase_subset L s).trans hs) (Finset.notMem_erase _ _)
      have he : 2^L + maskOf (s.erase L) = maskOf s :=
        Finset.add_sum_erase s (fun i => 2^i) hL
      have hb := (maskOf_isMask ht).1
      have hlo : ¬maskOf s < 2^L := by omega
      rw [eraseMask, if_neg hlo]
      have hsub : maskOf s - 2^L = maskOf (s.erase L) := by omega
      rw [hsub]
      by_cases ha : a = L
      · simp only [ha, ite_true]
      · rw [if_neg ha, ih (s.erase L) ht]
        have hL' : L ∈ s.erase a := Finset.mem_erase.mpr ⟨Ne.symm ha, hL⟩
        have heer : (s.erase L).erase a = (s.erase a).erase L := by
          ext i
          simp only [Finset.mem_erase]
          tauto
        rw [heer]
        exact Finset.add_sum_erase (s.erase a) (fun i => 2^i) hL'
    · have hs' := subset_range_pred hs hL
      have hlo := (maskOf_isMask hs').1
      rw [eraseMask, if_pos hlo]
      exact ih s hs'

theorem natPositions_erase {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    natPositions (s.erase a) = (natPositions s).erase a.val := by
  exact Finset.map_erase Fin.valEmbedding s a

theorem eraseMask_subsetMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) = subsetMask (s.erase a) := by
  rw [subsetMask, eraseMask_maskOf _ (natPositions_subset s),
    ← natPositions_erase, ← subsetMask]

theorem eraseMask_ne_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) ≠ subsetMask s ↔ a ∈ s := by
  rw [eraseMask_subsetMask, (subsetMask_injective L).ne_iff, Finset.erase_ne_self]

theorem eraseMask_lt_iff {L : ℕ} (s : Finset (Fin L)) (a : Fin L) :
    eraseMask L a.val (subsetMask s) < subsetMask s ↔ a ∈ s := by
  have hb := eraseMask_le (a := a.val) (subsetMask_isMask s).1
  rw [lt_iff_le_and_ne]
  simpa only [hb, true_and] using eraseMask_ne_iff s a

theorem eraseMask_isMask {L : ℕ} (s : Finset (Fin L)) (a : Fin L) (ha : a ∈ s) :
    IsMask L (s.card-1) (eraseMask L a.val (subsetMask s)) := by
  rw [eraseMask_subsetMask, ← Finset.card_erase_of_mem ha]
  exact subsetMask_isMask (s.erase a)

end ThreeSum.MaskErase
