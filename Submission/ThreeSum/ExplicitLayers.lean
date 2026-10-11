import Submission.ThreeSum.SignedLeaf
import Submission.ThreeSum.SparseBoxes

/-! # Exact values and sizes of the explicitly evaluated missing layers -/

namespace ThreeSum.ExplicitLayers

open Finset ThreeSum.SubsetAddress
open scoped BigOperators

@[simp] theorem missing_length {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (SignedLeaf.explicitMissing Q t).length = layerOffset Q.card t := by
  unfold SignedLeaf.explicitMissing
  rw [List.length_flatMap]
  simp only [QueryCoordinates.missingSets_length]
  have he := List.sum_toFinset (fun j => Q.card.choose j) (List.nodup_range (n := t))
  simpa only [List.toFinset_range,layerOffset] using he.symm

@[simp] theorem leaves_length {W : ℕ} (Q : Finset (Fin W)) (t : ℕ) :
    (SignedLeaf.explicitLeaves Q t).length = layerOffset Q.card t := by
  simp [SignedLeaf.explicitLeaves]

theorem choose_le_offset {c j t : ℕ} (hj : j < t) : c.choose j ≤ layerOffset c t := by
  exact Finset.single_le_sum (fun i hi => Nat.zero_le (c.choose i)) (Finset.mem_range.mpr hj)

def valueSum {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) : ℤ :=
  ((SignedLeaf.explicitLeaves Q t).map weight).sum

@[simp] theorem valueSum_zero {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) :
    valueSum Q weight 0 = 0 := by
  simp [valueSum,SignedLeaf.explicitLeaves,SignedLeaf.explicitMissing]

theorem valueSum_succ {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    valueSum Q weight (t+1) = valueSum Q weight t+
      ((QueryCoordinates.missingSets Q t).map fun U => weight (Q \ U)).sum := by
  simp [valueSum,SignedLeaf.explicitLeaves,SignedLeaf.explicitMissing,List.range_succ,
    List.flatMap_append,List.map_append,List.map_map,Function.comp_def,List.sum_append]

theorem valueSum_abs_le {W B : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ)
    (hw : ∀ S, S ⊆ Q → |weight S| ≤ B) :
    |valueSum Q weight t| ≤ ((layerOffset Q.card t*B : ℕ) : ℤ) := by
  have hh := List.abs_sum_take_map_le (SignedLeaf.explicitLeaves Q t) weight
    (fun S hs => hw S ((SignedLeaf.mem_explicitLeaves Q S t).mp hs).1)
    (SignedLeaf.explicitLeaves Q t).length
  have he : (SignedLeaf.explicitLeaves Q t).length =
      ((SignedLeaf.explicitLeaves Q t).map weight).length := (List.length_map _).symm
  rw [he,List.take_length] at hh
  simpa only [valueSum,List.length_map,leaves_length,Nat.cast_mul] using hh

theorem valueSum_eq_explicit {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    valueSum Q weight t = ∑ S ∈ SparseBoxes.explicitLeaves Q t, weight S := by
  have he : (SignedLeaf.explicitLeaves Q t).toFinset = SparseBoxes.explicitLeaves Q t := by
    ext S
    simp only [List.mem_toFinset,SignedLeaf.mem_explicitLeaves,SparseBoxes.mem_explicitLeaves]
  rw [valueSum,← List.sum_toFinset weight (SignedLeaf.explicitLeaves_nodup Q t),he]

theorem sparse_identity {W : ℕ} (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ) (t : ℕ) :
    (∑ S ∈ Q.powerset, weight S) = valueSum Q weight t+
      ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight := by
  rw [valueSum_eq_explicit]
  exact SparseBoxes.sparse_query_identity_enumerated Q t weight

end ThreeSum.ExplicitLayers
