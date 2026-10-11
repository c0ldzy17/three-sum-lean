import Submission.ThreeSum.BoxStages
import Submission.ThreeSum.MaskDifference

/-! # Exact width-scan invariants for general mask union -/

namespace ThreeSum.MaskUnion

open Finset ThreeSum.SubsetAddress

/-- Bits of `B` below the scan position have been added to `A`. -/
def scanSet {W : ℕ} (A B : Finset (Fin W)) (j : ℕ) : Finset (Fin W) :=
  A ∪ (B ∩ BoxStages.initialCoords W j)

@[simp] theorem scanSet_zero {W : ℕ} (A B : Finset (Fin W)) : scanSet A B 0 = A := by
  simp [scanSet]

@[simp] theorem scanSet_all {W : ℕ} (A B : Finset (Fin W)) : scanSet A B W = A ∪ B := by
  simp [scanSet]

theorem scanSet_succ_mem {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) :
    scanSet A B (j+1) = insert ⟨j,hj⟩ (scanSet A B j) := by
  rw [scanSet,BoxStages.prefix_succ hj]
  change A ∪ (B ∩ insert ⟨j,hj⟩ (BoxStages.initialCoords W j)) = _
  rw [Finset.inter_insert_of_mem hb,Finset.union_insert]
  rfl

theorem scanSet_succ_notMem {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∉ B) : scanSet A B (j+1) = scanSet A B j := by
  rw [scanSet,BoxStages.prefix_succ hj]
  change A ∪ (B ∩ insert ⟨j,hj⟩ (BoxStages.initialCoords W j)) = _
  rw [Finset.inter_insert_of_notMem hb]
  rfl

theorem current_mem_iff {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W) :
    (⟨j,hj⟩ : Fin W) ∈ scanSet A B j ↔ (⟨j,hj⟩ : Fin W) ∈ A := by
  simp [scanSet,BoxStages.mem_prefix]

theorem scanSet_succ_already {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) (ha : (⟨j,hj⟩ : Fin W) ∈ A) :
    scanSet A B (j+1) = scanSet A B j := by
  rw [scanSet_succ_mem A B hj hb]
  exact Finset.insert_eq_of_mem ((current_mem_iff A B hj).mpr ha)

theorem scanSet_card_succ_new {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) (ha : (⟨j,hj⟩ : Fin W) ∉ A) :
    (scanSet A B (j+1)).card = (scanSet A B j).card+1 := by
  rw [scanSet_succ_mem A B hj hb,Finset.card_insert_of_notMem]
  exact fun h => ha ((current_mem_iff A B hj).mp h)

theorem scanSet_mask_succ_new {W j : ℕ} (A B : Finset (Fin W)) (hj : j < W)
    (hb : (⟨j,hj⟩ : Fin W) ∈ B) (ha : (⟨j,hj⟩ : Fin W) ∉ A) :
    subsetMask (scanSet A B (j+1)) = subsetMask (scanSet A B j)+2^j := by
  have hn : (⟨j,hj⟩ : Fin W) ∉ scanSet A B j := fun h => ha ((current_mem_iff A B hj).mp h)
  rw [scanSet_succ_mem A B hj hb,MaskDifference.subsetMask_sum,Finset.sum_insert hn,
    MaskDifference.subsetMask_sum]
  exact Nat.add_comm _ _

end ThreeSum.MaskUnion
