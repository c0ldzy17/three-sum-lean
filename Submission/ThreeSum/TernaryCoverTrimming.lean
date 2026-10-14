import Submission.ThreeSum.TernaryCoverHashes
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Separable trimming for actual tagged linear hashes

Pair and same-side triple counts are supplied by the concrete tag vectors.
The following finite Markov argument retains at least three quarters of
every ordered edge's representation mass with the trinary threshold eight.
-/

namespace ThreeSum.TernaryCoverTrimming

open Finset TernaryCoverHashes
open scoped BigOperators

variable {ι K : Type*} [Fintype ι] [DecidableEq ι]
variable [Field K] [Fintype K] [DecidableEq K]

abbrev Word := ι → K
abbrev Weight := Coordinate ι → K

def bucketSize (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (w : Weight (ι := ι) (K := K))
    (a : K) : ℕ :=
  (vertices.filter fun u => linearHash (vector u) w = a).card

def loadedMass (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) : ℕ :=
  ∑ w ∈ event, bucketSize vertices vector w a

theorem loadedMass_eq (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) :
    loadedMass event vertices vector a =
      ∑ u ∈ vertices, (event.filter fun w => linearHash (vector u) w = a).card := by
  classical
  unfold loadedMass bucketSize
  simp_rw [card_eq_sum_ones, sum_filter]
  rw [sum_comm]

theorem left_loadedMass_bound (x y : Word (ι := ι) (K := K)) (a b : K)
    (vertices : Finset (Word (ι := ι) (K := K))) :
    Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices leftVector a ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)) := by
  classical
  rw [loadedMass_eq, mul_sum]
  have hterm (u : Word (ι := ι) (K := K)) :
      Fintype.card K ^ 3 *
        ((pairEvent x y a b).filter fun w => linearHash (leftVector u) w = a).card ≤
      (if u = x then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
        Fintype.card (Weight (ι := ι) (K := K)) := by
    by_cases hu : u = x
    · subst u
      have heq : ((pairEvent x y a b).filter fun w => linearHash (leftVector x) w = a) =
          pairEvent x y a b := by
        apply filter_eq_self.mpr
        intro w hw
        exact (mem_filter.mp hw).2.1
      rw [heq, if_pos rfl]
      have hp := pairEvent_card x y a b
      have hm := congrArg (fun z : ℕ => Fintype.card K * z) hp
      nlinarith
    · rw [if_neg hu]
      simpa using (left_triple_card (Ne.symm hu) y a b a).le
  calc
    _ ≤ ∑ u ∈ vertices,
        ((if u = x then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
          Fintype.card (Weight (ι := ι) (K := K))) := sum_le_sum fun u _ => hterm u
    _ ≤ Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) +
        vertices.card * Fintype.card (Weight (ι := ι) (K := K)) := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq']
      simp only [Nat.cast_id]
      split_ifs <;> omega
    _ = _ := by ring

theorem right_loadedMass_bound (x y : Word (ι := ι) (K := K)) (a b : K)
    (vertices : Finset (Word (ι := ι) (K := K))) :
    Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices rightVector b ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)) := by
  classical
  rw [loadedMass_eq, mul_sum]
  have hterm (u : Word (ι := ι) (K := K)) :
      Fintype.card K ^ 3 *
        ((pairEvent x y a b).filter fun w => linearHash (rightVector u) w = b).card ≤
      (if u = y then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
        Fintype.card (Weight (ι := ι) (K := K)) := by
    by_cases hu : u = y
    · subst u
      have heq : ((pairEvent x y a b).filter fun w => linearHash (rightVector y) w = b) =
          pairEvent x y a b := by
        apply filter_eq_self.mpr
        intro w hw
        exact (mem_filter.mp hw).2.2
      rw [heq, if_pos rfl]
      have hp := pairEvent_card x y a b
      have hm := congrArg (fun z : ℕ => Fintype.card K * z) hp
      nlinarith
    · rw [if_neg hu]
      simpa using (right_triple_card x (Ne.symm hu) a b b).le
  calc
    _ ≤ ∑ u ∈ vertices,
        ((if u = y then Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) else 0) +
          Fintype.card (Weight (ι := ι) (K := K))) := sum_le_sum fun u _ => hterm u
    _ ≤ Fintype.card K * Fintype.card (Weight (ι := ι) (K := K)) +
        vertices.card * Fintype.card (Weight (ι := ι) (K := K)) := by
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, sum_ite_eq']
      simp only [Nat.cast_id]
      split_ifs <;> omega
    _ = _ := by ring

def heavyEvent (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) (B : ℕ) :
    Finset (Weight (ι := ι) (K := K)) :=
  event.filter fun w => B < bucketSize vertices vector w a

theorem heavyEvent_markov (event : Finset (Weight (ι := ι) (K := K)))
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (a : K) (B : ℕ) :
    B * (heavyEvent event vertices vector a B).card ≤
      loadedMass event vertices vector a := by
  calc
    _ = ∑ _w ∈ heavyEvent event vertices vector a B, B := by simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ heavyEvent event vertices vector a B, bucketSize vertices vector w a :=
      sum_le_sum fun w hw => (mem_filter.mp hw).2.le
    _ ≤ loadedMass event vertices vector a :=
      sum_le_sum_of_subset_of_nonneg (filter_subset ..) (fun _ _ _ => Nat.zero_le _)

/-- Markov's bound with denominator cleared. -/
theorem heavyEvent_bound (x y : Word (ι := ι) (K := K)) (a b target : K)
    (vertices : Finset (Word (ι := ι) (K := K)))
    (vector : Word (ι := ι) (K := K) → Coordinate ι → K) (B : ℕ)
    (hload : Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices vector target ≤
      (Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K)))
    (hB : 8 * (Fintype.card K + vertices.card) ≤ B * Fintype.card K) :
    8 * Fintype.card K ^ 2 * (heavyEvent (pairEvent x y a b) vertices vector target B).card ≤
      Fintype.card (Weight (ι := ι) (K := K)) := by
  have hm := heavyEvent_markov (pairEvent x y a b) vertices vector target B
  have hp : 0 < Fintype.card K := Fintype.card_pos
  have hpos : 0 < B * Fintype.card K := lt_of_lt_of_le (by omega) hB
  apply Nat.le_of_mul_le_mul_left (c := B * Fintype.card K) ?_ hpos
  calc
    _ = 8 * (Fintype.card K ^ 3 *
        (B * (heavyEvent (pairEvent x y a b) vertices vector target B).card)) := by ring
    _ ≤ 8 * (Fintype.card K ^ 3 * loadedMass (pairEvent x y a b) vertices vector target) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ ≤ 8 * ((Fintype.card K + vertices.card) * Fintype.card (Weight (ι := ι) (K := K))) :=
      Nat.mul_le_mul_left _ hload
    _ ≤ _ := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (Fintype.card (Weight (ι := ι) (K := K))) hB

def trimmedPairEvent (x y : Word (ι := ι) (K := K)) (a b : K)
    (VL VR : Finset (Word (ι := ι) (K := K))) (B : ℕ) : Finset (Weight (ι := ι) (K := K)) :=
  (pairEvent x y a b).filter fun w =>
    bucketSize VL leftVector w a ≤ B ∧ bucketSize VR rightVector w b ≤ B

theorem trimmedPairEvent_bound (x y : Word (ι := ι) (K := K)) (a b : K)
    (VL VR : Finset (Word (ι := ι) (K := K))) (B : ℕ)
    (hBL : 8 * (Fintype.card K + VL.card) ≤ B * Fintype.card K)
    (hBR : 8 * (Fintype.card K + VR.card) ≤ B * Fintype.card K) :
    3 * Fintype.card (Weight (ι := ι) (K := K)) ≤
      4 * Fintype.card K ^ 2 * (trimmedPairEvent x y a b VL VR B).card := by
  classical
  have hsub : pairEvent x y a b ⊆
      (trimmedPairEvent x y a b VL VR B ∪
        heavyEvent (pairEvent x y a b) VL leftVector a B) ∪
          heavyEvent (pairEvent x y a b) VR rightVector b B := by
    intro w hw
    by_cases hl : bucketSize VL leftVector w a ≤ B
    · by_cases hr : bucketSize VR rightVector w b ≤ B
      · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hw, hl, hr⟩))
      · exact mem_union_right _ (mem_filter.mpr ⟨hw, by omega⟩)
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hw, by omega⟩))
  have hcard : (pairEvent x y a b).card ≤
      (trimmedPairEvent x y a b VL VR B).card +
        (heavyEvent (pairEvent x y a b) VL leftVector a B).card +
          (heavyEvent (pairEvent x y a b) VR rightVector b B).card :=
    (card_le_card hsub).trans ((card_union_le ..).trans (Nat.add_le_add_right (card_union_le ..) _))
  have hraw := pairEvent_card x y a b
  have hleft := heavyEvent_bound x y a b a VL leftVector B (left_loadedMass_bound x y a b VL) hBL
  have hright := heavyEvent_bound x y a b b VR rightVector B (right_loadedMass_bound x y a b VR) hBR
  have hscaled := Nat.mul_le_mul_left (8 * Fintype.card K ^ 2) hcard
  nlinarith

end ThreeSum.TernaryCoverTrimming
