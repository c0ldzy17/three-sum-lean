import Submission.ThreeSum.BlockIndexedQuery
import Submission.ThreeSum.MaskDifference

/-! # Exact row-major mask packing and prefix scan invariants -/

namespace ThreeSum.BlockMaskLayout

open Finset BlockRows BlockIndex ThreeSum.SubsetAddress
open scoped BigOperators

def rowMask {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) : ℕ :=
  2^(i.val*L)*subsetMask (rows i)

def prefixMask {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) : ℕ :=
  subsetMask (indexSet (join (prefixIndices J k) rows))

theorem mask_join {J L : ℕ} (I : Finset (Fin J)) (rows : Fin J → Finset (Fin L)) :
    subsetMask (indexSet (join I rows)) = ∑ i ∈ I, rowMask rows i := by
  rw [MaskDifference.subsetMask_sum]
  unfold indexSet
  rw [Finset.sum_map]
  unfold join
  rw [Finset.sum_sigma]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Equiv.toEmbedding_apply,coordEquiv_val,pow_add,rowMask,
    MaskDifference.subsetMask_sum,Finset.mul_sum]

theorem prefixMask_eq_sum {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    prefixMask rows k = ∑ i ∈ prefixIndices J k, rowMask rows i := mask_join _ _

@[simp] theorem prefixMask_zero {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    prefixMask rows 0 = 0 := by
  rw [prefixMask_eq_sum]
  simp [prefixIndices]

theorem prefixIndices_succ {J k : ℕ} (hk : k < J) :
    prefixIndices J (k+1) = insert ⟨k,hk⟩ (prefixIndices J k) := by
  ext i
  simp only [mem_prefixIndices,Finset.mem_insert,Fin.ext_iff]
  omega

theorem prefixMask_succ {J L k : ℕ} (rows : Fin J → Finset (Fin L)) (hk : k < J) :
    prefixMask rows (k+1) = prefixMask rows k+rowMask rows ⟨k,hk⟩ := by
  rw [prefixMask_eq_sum,prefixIndices_succ hk,Finset.sum_insert (by simp),prefixMask_eq_sum]
  exact Nat.add_comm _ _

@[simp] theorem prefixMask_all {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    prefixMask rows J = subsetMask (indexSet (flat rows)) := by
  have he : prefixIndices J J = univ := by
    ext i
    simp only [mem_prefixIndices,Finset.mem_univ,iff_true]
    exact i.isLt
  simp only [prefixMask,he,flat]

theorem prefixMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (k : ℕ) :
    prefixMask rows k < 2^(J*L) := (subsetMask_isMask _).1

theorem rowMask_lt {J L : ℕ} (rows : Fin J → Finset (Fin L)) (i : Fin J) :
    rowMask rows i < 2^(J*L) := by
  have he : prefixMask rows (i.val+1) = prefixMask rows i.val+rowMask rows i :=
    prefixMask_succ rows i.isLt
  have hb := prefixMask_lt rows (i.val+1)
  omega

def rawMasks {J L : ℕ} (rows : Fin J → Finset (Fin L)) : List ℕ :=
  List.ofFn (fun i => subsetMask (rows i))

def packedMasks {J L : ℕ} (rows : Fin J → Finset (Fin L)) : List ℕ := List.ofFn (rowMask rows)

@[simp] theorem rawMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (rawMasks rows).length = J := by simp [rawMasks]

@[simp] theorem packedMasks_length {J L : ℕ} (rows : Fin J → Finset (Fin L)) :
    (packedMasks rows).length = J := by simp [packedMasks]

theorem packedMasks_take_succ {J L j : ℕ} (rows : Fin J → Finset (Fin L)) (hj : j < J) :
    (packedMasks rows).take (j+1) = (packedMasks rows).take j ++ [rowMask rows ⟨j,hj⟩] := by
  rw [List.take_succ_eq_append_getElem (by simpa using hj)]
  simp [packedMasks]

end ThreeSum.BlockMaskLayout
