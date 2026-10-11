import Submission.ThreeSum.EncodedColorTimeSources
import Submission.ThreeSum.EncodedColorTimeNormalize
import Submission.ThreeSum.EncodedColorTimeWanted

/-!
# The executed selected-color preprocessing fits the final time exponent

This charges the actual fixed256 program's complete time expression:
normalization and incidence construction, common-prime selection, local
cover and global keys, balanced wanted rows, shared source banks and the
retained result-header computation. Reporting and the outer color loop
remain separate composition obligations.
-/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def preprocessingTime (k n : ℕ) : ℕ := LightEncodedColorPipeline.time n (n^k)

noncomputable section

theorem prime_time_certificate (k : ℕ) :
    PowerBound (fun n => LightEncodedColorPrime.time (maxMod n) n n n (bandSize n)
      (radix n) (primeWindow n) (n^k)) certificateExponent := by
  apply powerBound_mono ((BandPrimeCosts.timeBudget_certificate k).add_same (const_certificate 1160))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact EncodedColorPrimeCosts.time_le_budget (nA := n) (nB := n) (nC := n)
    (n := n) k (by omega) le_rfl le_rfl le_rfl

theorem prime_host_time_certificate (k : ℕ) :
    PowerBound (fun n => LightEncodedColorPrimeHost.inputTime n (n^k)) certificateExponent := by
  change PowerBound (fun n => LightEncodedColorNormalize.time n+
    LightEncodedColorPrime.time (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) (n^k)+600) _
  exact (normalize_time_certificate.add_same (prime_time_certificate k)).add_same (const_certificate 600)

theorem stage_time_certificate (k : ℕ) :
    PowerBound (fun n => EncodedColorStageCosts.time n (maxMod n) (radix n) (n^k)
      (EncodedColorStageCosts.incidenceCap n)) certificateExponent := by
  change PowerBound (fun n => EncodedColorWantedCosts.time (maxMod n) (radix n) (half n) (blocks n)
    (n^k) (EncodedColorStageCosts.incidenceCap n)+EncodedColorSourcesCosts.time n (maxMod n) (n^k) (radix n)+400) _
  exact ((wanted_time_certificate k).add_same (sources_time_certificate k)).add_same (const_certificate 400)

theorem wanted_header_time_powerBound :
    PowerBound (fun n => LightEncodedColorWantedHeader.time (blocks n)) 0 :=
  sum_zero (product_zero (PowerBound.const 100) blocks_powerBound) (PowerBound.const 1000)

theorem pipeline_time_powerBound (k : ℕ) : PowerBound (preprocessingTime k) certificateExponent := by
  change PowerBound (fun n => LightEncodedColorPrimeHost.inputTime n (n^k)+
    EncodedColorStageCosts.time n (maxMod n) (radix n) (n^k) (EncodedColorStageCosts.incidenceCap n)+
    LightEncodedColorWantedHeader.time (blocks n)+1600) _
  have hh := wanted_header_time_powerBound.mono_exponent (show (0 : ℝ) ≤ certificateExponent by
    norm_num [certificateExponent])
  exact (((prime_host_time_certificate k).add_same (stage_time_certificate k)).add_same hh).add_same
    (const_certificate 1600)

theorem pipeline_time_eventually_target (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (preprocessingTime k n : ℝ) ≤ (n : ℝ)^targetExponent := by
  have hh := (pipeline_time_powerBound k) (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh

theorem pipeline_time_endStatementBigO (k : ℕ) :
    EndStatement.BigO (preprocessingTime k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using pipeline_time_eventually_target k

end
end ThreeSum.EncodedColorTime
