import Submission.ThreeSum.SubsetAddress

/-! # Exact arithmetic subtraction of one subset mask from another -/

namespace ThreeSum.MaskDifference

open Finset ThreeSum.SubsetAddress

theorem subsetMask_sum {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = ∑ i ∈ S, 2^i.val := by
  simp [subsetMask,maskOf,natPositions]

@[simp] theorem subsetMask_empty (L : ℕ) : subsetMask (∅ : Finset (Fin L)) = 0 := by
  simp [subsetMask_sum]

theorem subsetMask_eq_zero_iff {L : ℕ} (S : Finset (Fin L)) :
    subsetMask S = 0 ↔ S = ∅ := by
  constructor
  · intro h
    exact subsetMask_injective L (h.trans (subsetMask_empty L).symm)
  · rintro rfl
    exact subsetMask_empty L

theorem subsetMask_union_sdiff {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    subsetMask U+subsetMask (Q \ U) = subsetMask Q := by
  have hd : Disjoint U (Q \ U) := by
    apply Finset.disjoint_left.mpr
    intro a ha hb
    exact (Finset.mem_sdiff.mp hb).2 ha
  have he : U ∪ (Q \ U) = Q := by
    ext a
    simp only [mem_union,mem_sdiff]
    constructor
    · rintro (ha | ⟨ha,_⟩)
      · exact hU ha
      · exact ha
    · intro ha
      by_cases hb : a ∈ U
      · exact Or.inl hb
      · exact Or.inr ⟨ha,hb⟩
  calc
    _ = (∑ i ∈ U, 2^i.val)+(∑ i ∈ Q \ U, 2^i.val) := by simp only [subsetMask_sum]
    _ = ∑ i ∈ U ∪ (Q \ U), 2^i.val := (Finset.sum_union hd).symm
    _ = subsetMask Q := by rw [he,subsetMask_sum]

theorem subsetMask_sdiff {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    subsetMask Q-subsetMask U = subsetMask (Q \ U) := by
  have h := subsetMask_union_sdiff Q U hU
  omega

theorem subsetMask_sdiff_int {L : ℕ} (Q U : Finset (Fin L)) (hU : U ⊆ Q) :
    (subsetMask Q : ℤ)-(subsetMask U : ℤ) = (subsetMask (Q \ U) : ℤ) := by
  have h := subsetMask_union_sdiff Q U hU
  have hz : (subsetMask U : ℤ)+(subsetMask (Q \ U) : ℤ) = (subsetMask Q : ℤ) := by
    exact_mod_cast h
  omega

end ThreeSum.MaskDifference
