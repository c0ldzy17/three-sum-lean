import Submission.ThreeSum.SubsetAddress

/-!
# The inverse interpretation of enumerated subset masks

Decoding is used only to state the meaning of machine table cells. The
enumeration itself is the guarded cardinality-layer routine.
-/

namespace ThreeSum.MaskDecode

open Finset
open scoped BigOperators
open SubsetAddress

def decode (L m : ℕ) : Finset (Fin L) := univ.filter fun i => i.val ∈ m.bitIndices

private theorem bitIndices_subset {L m : ℕ} (hm : m < 2^L) :
    m.bitIndices.toFinset ⊆ Finset.range L := by
  intro i hi
  have hp := Nat.two_pow_le_of_mem_bitIndices (List.mem_toFinset.mp hi)
  apply Finset.mem_range.mpr
  by_contra hn
  have hh : 2^L ≤ 2^i := Nat.pow_le_pow_right (by decide) (Nat.le_of_not_gt hn)
  omega

theorem natPositions_decode {L m : ℕ} (hm : m < 2^L) :
    natPositions (decode L m) = m.bitIndices.toFinset := by
  ext i
  constructor
  · intro hi
    obtain ⟨j, hj, he⟩ := Finset.mem_map.mp hi
    rw [← he]
    exact List.mem_toFinset.mpr (Finset.mem_filter.mp hj).2
  · intro hi
    have hiL := Finset.mem_range.mp (bitIndices_subset hm hi)
    apply Finset.mem_map.mpr
    refine ⟨⟨i, hiL⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
    exact List.mem_toFinset.mp hi

theorem subsetMask_decode {L m : ℕ} (hm : m < 2^L) : subsetMask (decode L m) = m := by
  rw [subsetMask, natPositions_decode hm, maskOf]
  exact Finset.sum_toFinset_bitIndices_two_pow m

theorem decode_subsetMask {L : ℕ} (s : Finset (Fin L)) : decode L (subsetMask s) = s := by
  apply subsetMask_injective L
  exact subsetMask_decode (subsetMask_isMask s).1

theorem decode_card {L m : ℕ} (hm : m < 2^L) : (decode L m).card = weight L m := by
  have h := (subsetMask_isMask (decode L m)).2
  rw [subsetMask_decode hm] at h
  exact h.symm

theorem decode_card_layer {L k m : ℕ} (hm : m ∈ enumerateLayer L k) :
    (decode L m).card = k := by
  have h := (mem_enumerateLayer L k m).mp hm
  rw [decode_card h.1, h.2]

theorem decoded_layer_complete {L k : ℕ} (s : Finset (Fin L)) (hs : s.card = k) :
    s ∈ (enumerateLayer L k).map (decode L) := by
  apply List.mem_map.mpr
  refine ⟨subsetMask s, (mem_enumerateLayer L k _).mpr ?_, decode_subsetMask s⟩
  simpa only [hs] using subsetMask_isMask s

theorem decoded_downset_complete {L cut : ℕ} (s : Finset (Fin L)) (hs : s.card ≤ cut) :
    s ∈ (enumerateDownset L cut).map (decode L) := by
  exact List.mem_map.mpr ⟨subsetMask s, subsetMask_mem_enumeration hs, decode_subsetMask s⟩

end ThreeSum.MaskDecode
