import Submission.ThreeSum.LightDenseSetup
import Submission.ThreeSum.BandPrimeCostBounds
import Submission.ThreeSum.SharedReportingCostBounds

/-!
# Charge the actual threshold construction

One final aggregate score is covered by the existing executed arithmetic
budget. Computing the cap and storing its product adds only O(J) work.
This is a cost theorem for this concrete stage, not a full solver claim.
-/

namespace ThreeSum.LightDenseSetupCosts

open Scales BandScales CostLedger ArithmeticStageBounds Parameters

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000

theorem aggregate_time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightBandWeightedScore.time (maxMod n) (bandSize n) R
      (LightPrimePool.size (primeWindow n)) (n^k) ≤ BandPrimeCosts.timeBudget k n := by
  let s := LightPrimePool.size (primeWindow n)
  have hs : s+1 ≤ (s+1)^2 := by nlinarith
  have hd : 6 ≤ 15*(primeDepth radix n+1) := by omega
  have ht := BandPrimeCosts.aggregate_time_le (maxMod n) (bandSize n) R s (n^k)
  have hu := BandPrimeCosts.unit_le_budget k hn
  calc
    _ ≤ 2*(R+1)*(s+1)*BandPrimeCosts.unit (maxMod n) (bandSize n) (n^k) := ht
    _ ≤ 2*(3*bandCount n^2+1)*(s+1)*(3*perTripleBudget k n) := by gcongr
    _ = 6*((3*bandCount n^2+1)*((s+1)*perTripleBudget k n)) := by ring
    _ ≤ (15*(primeDepth radix n+1))*
        ((3*bandCount n^2+1)*((s+1)^2*perTripleBudget k n)) :=
      Nat.mul_le_mul hd (Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hs))
    _ ≤ BandPrimeCosts.timeBudget k n := by unfold BandPrimeCosts.timeBudget; dsimp [s]; nlinarith

def timeBudget (k n : ℕ) : ℕ :=
  BandPrimeCosts.timeBudget k n+20*blockCount (inputBits n)+570

theorem time_le_budget {n R : ℕ} (k : ℕ) (hn : 0 < n)
    (hR : R ≤ 3*bandCount n^2) :
    LightDenseSetup.time (maxMod n) (bandSize n) R (LightPrimePool.size (primeWindow n))
      (n^k) (blockCount (inputBits n)) ≤ timeBudget k n := by
  have hh := aggregate_time_le_budget k hn hR
  unfold LightDenseSetup.time LightDenseCap.time LightNatPower.time timeBudget
  omega

open Filter Real StageBounds
open scoped Topology

noncomputable section

theorem scalar_time_powerBound : PowerBound (fun n => 20*blockCount (inputBits n)+570) 0 := by
  have hj := (PowerBound.const 20).mul SharedReportingCosts.blocks_powerBound
  have hj' : PowerBound (fun n => 20*blockCount (inputBits n)) 0 := by
    simpa only [zero_add,SharedReportingCosts.blocks] using hj
  exact hj'.add_same (PowerBound.const 570)

theorem timeBudget_powerBound (k : ℕ) :
    PowerBound (timeBudget k) (2+epsilon*(4/5-(2/5)*E-2*bandShift)) := by
  change PowerBound (fun n => BandPrimeCosts.timeBudget k n+20*blockCount (inputBits n)+570)
    (2+epsilon*(4/5-(2/5)*E-2*bandShift))
  have he : (0 : ℝ) ≤ 2+epsilon*(4/5-(2/5)*E-2*bandShift) := by
    have hh := E_bounds.2
    unfold epsilon bandShift
    linarith
  have hh := (BandPrimeCosts.timeBudget_powerBound k).add_same (scalar_time_powerBound.mono_exponent he)
  simpa only [Nat.add_assoc] using hh

theorem timeBudget_certificate (k : ℕ) : PowerBound (timeBudget k) certificateExponent :=
  (timeBudget_powerBound k).mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

theorem timeBudget_endStatementBigO (k : ℕ) :
    EndStatement.BigO (timeBudget k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  have hh := (timeBudget_certificate k) (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa [targetExponent] using hh

end
end ThreeSum.LightDenseSetupCosts
