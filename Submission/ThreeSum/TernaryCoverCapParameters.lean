import Submission.ThreeSum.TernaryCoverFrequency
import Mathlib.Algebra.Order.Floor.Div

/-! # An explicit computable raw cap

This threshold clears the all-target bad-map loss using a finite positive
moment order.  Its size is stated explicitly.  This module does not claim
the separate asymptotic machine-cost estimate for a chosen moment schedule.
-/

namespace ThreeSum.TernaryCoverCapParameters

open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryPartitionCount TernaryTypeLowerBound

def capBudget (p B k : ℕ) : ℕ :=
  4*(Nat.log2 p+1)+2*(Nat.log2 B+1)+8*k^2+4

def capExponent (p B k : ℕ) : ℕ := capBudget p B k ⌈/⌉ k

def rawThreshold (p B k : ℕ) : ℕ := 2 ^ capExponent p B k

theorem rawThreshold_pos (p B k : ℕ) : 0 < rawThreshold p B k := Nat.pow_pos (by decide)

theorem budget_bound (p B k : ℕ) : 16*p^4*B^2*3^(4*k^2) ≤ 2^capBudget p B k := by
  have hp : p^4 ≤ 2^(4*(Nat.log2 p+1)) := by
    have h := Nat.pow_le_pow_left (Nat.lt_log2_self (n := p)).le 4
    simpa only [← pow_mul, Nat.mul_comm] using h
  have hB : B^2 ≤ 2^(2*(Nat.log2 B+1)) := by
    have h := Nat.pow_le_pow_left (Nat.lt_log2_self (n := B)).le 2
    simpa only [← pow_mul, Nat.mul_comm] using h
  have h3 : 3^(4*k^2) ≤ 2^(8*k^2) := by
    have h := Nat.pow_le_pow_left (by decide : (3 : ℕ) ≤ 2^2) (4*k^2)
    simpa only [← pow_mul, show 2*(4*k^2) = 8*k^2 by ring] using h
  calc
    _ ≤ 16*2^(4*(Nat.log2 p+1))*2^(2*(Nat.log2 B+1))*2^(8*k^2) :=
      Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 16 hp) hB) h3
    _ = 2^capBudget p B k := by
      rw [show (16 : ℕ) = 2^4 by norm_num, ← pow_add, ← pow_add, ← pow_add]
      congr 1
      unfold capBudget
      omega

theorem threshold_clears_budget (p B k : ℕ) (hk : 0 < k) :
    16*p^4*B^2*3^(4*k^2) ≤ rawThreshold p B k ^ k := by
  have hb : capBudget p B k ≤ k*capExponent p B k :=
    (ceilDiv_le_iff_le_mul hk).mp le_rfl
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) hb
  exact (budget_bound p B k).trans (by
    simpa only [rawThreshold, ← pow_mul, Nat.mul_comm] using hpow)

theorem actual_edge_pos (m : ℕ) : 0 < Fintype.card (ActualEdge m) := by
  have hR : 0 < 2^(fixedPi m 1)*3^(fixedPi m 2) := by positivity
  have hM := hR.trans_le (vertices_lower_bound (fixedPi m) (fixedPi_total m) (fixedPi_space m))
  have hpos := Nat.mul_pos hM hR
  have hmass := fixed_edge_mass_lower m
  by_contra hn
  have hz : Fintype.card (ActualEdge m) = 0 := by omega
  change _ ≤ _*Fintype.card (ActualEdge m) at hmass
  rw [hz, mul_zero] at hmass
  omega

theorem actual_pruning_guard (m p B k : ℕ) (hk : 0 < k) :
    16*p^4*B^2*3^(4*k^2) ≤ rawThreshold p B k ^ k*Fintype.card (ActualEdge m) := by
  calc
    _ ≤ rawThreshold p B k ^ k := threshold_clears_budget p B k hk
    _ ≤ rawThreshold p B k ^ k*Fintype.card (ActualEdge m) := by
      simpa only [Nat.succ_eq_add_one, Nat.zero_add, mul_one] using
        Nat.mul_le_mul_left (rawThreshold p B k ^ k) (actual_edge_pos m)

noncomputable def sourceCap (m p : ℕ) : ℕ :=
  (8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card)) ⌈/⌉ p

theorem sourceCap_threshold (m p : ℕ) (hp : 0 < p) :
    8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ sourceCap m p*p := by
  have h : 8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ p*sourceCap m p :=
    (ceilDiv_le_iff_le_mul hp).mp le_rfl
  simpa only [Nat.mul_comm] using h

theorem frequencyFactor_gt_one (m : ℕ) : 1 < frequencyFactor m := by
  have hD : 0 < partitionLoss (7930175*m) (978249*m) := by unfold partitionLoss; positivity
  have hC : 0 < (3 : ℕ)^16 := by positivity
  have hQ : 0 < (16*partitionLoss (7930175*m) (978249*m))^2 := by positivity
  have h := Nat.mul_le_mul_left 4 (Nat.mul_pos hC hQ)
  have h4 : 4 ≤ frequencyFactor m := by
    simpa only [Nat.succ_eq_add_one, Nat.zero_add, mul_one, frequencyFactor, Nat.mul_assoc] using h
  omega

/-- Every numerical pruning parameter is defined explicitly.  Under the
literal prime interval, the finite greedy cover covers all ordered targets
with the global raw cap; no moment, entropy, or coverage premise remains. -/
theorem explicit_greedy_covers (m p : ℕ) [Fact p.Prime]
    (maps : List (Weight m p)) (hall : ∀ w, w ∈ maps) (hp : 4 < p)
    (hlo : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)))
    (k : ℕ) (hk : 0 < k) (t : ZMod p × ZMod p) :
    ∃ w ∈ Cover.greedyChoices maps
        (Covers m p (sourceCap m p) (rawThreshold p (sourceCap m p) k)) Finset.univ
        (frequencyFactor m*(Nat.log2 (p^2)+1)),
      Covers m p (sourceCap m p) (rawThreshold p (sourceCap m p) k) w t := by
  apply greedy_covers m p maps hall hp hlo (sourceCap m p) k
    (rawThreshold p (sourceCap m p) k) (frequencyFactor m) (frequencyFactor_gt_one m)
    (rawThreshold_pos p (sourceCap m p) k) (sourceCap_threshold m p (by omega))
    (actual_pruning_guard m p (sourceCap m p) k hk) (polynomial_frequency_scale m p hup) t

end ThreeSum.TernaryCoverCapParameters
