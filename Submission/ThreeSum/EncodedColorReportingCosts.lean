import Submission.ThreeSum.LightThreeSumReportingSetupBank
import Submission.ThreeSum.LightThreeSumReportingSetupDense
import Submission.ThreeSum.EncodedColorPipelineTime

/-! # Actual time of the source, shared reporting and dense prelude -/

namespace ThreeSum.EncodedColorReportingCosts

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open CostLedger
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def setupTime (n U : ℕ) : ℕ := LightThreeSumReportingSetupBank.time n+
  LightThreeSumReportingSetupDense.time n U (ColorBandBounds.count n (bandSize n))+200

def time (n U : ℕ) : ℕ := LightEncodedColorPipeline.time n U+setupTime n U+1000

def preprocessingTime (k n : ℕ) : ℕ := time n (n^k)

theorem setup_time_le {n U R : ℕ} (hR : R ≤ ColorBandBounds.count n (bandSize n)) :
    LightThreeSumReportingSetupBank.time n+LightThreeSumReportingSetupDense.time n U R+200 ≤
      setupTime n U := by
  unfold setupTime LightThreeSumReportingSetupDense.time LightDenseSetup.time LightBandWeightedScore.time
  gcongr

theorem dense_time_le_budget {n : ℕ} (k : ℕ) (hn : 0 < n) :
    LightThreeSumReportingSetupDense.time n (n^k) (ColorBandBounds.count n (bandSize n)) ≤
      LightDenseSetupCosts.timeBudget k n+1600 := by
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hc : ColorBandBounds.count n (bandSize n) ≤ 3*bandCount n^2 :=
    Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
  exact Nat.add_le_add_right (LightDenseSetupCosts.time_le_budget k hn hc) 1600

noncomputable section

theorem bank_time_certificate :
    PowerBound LightThreeSumReportingSetupBank.time certificateExponent := by
  change PowerBound (fun n => SharedReportingBankCosts.budget n+400) _
  exact SharedReportingBankCosts.budget_certificate.add_same (EncodedColorTime.const_certificate 400)

theorem dense_time_certificate (k : ℕ) :
    PowerBound (fun n => LightThreeSumReportingSetupDense.time n (n^k)
      (ColorBandBounds.count n (bandSize n))) certificateExponent := by
  apply powerBound_mono ((LightDenseSetupCosts.timeBudget_certificate k).add_same
    (EncodedColorTime.const_certificate 1600))
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  exact dense_time_le_budget k (by omega)

theorem setup_time_certificate (k : ℕ) :
    PowerBound (fun n => setupTime n (n^k)) certificateExponent := by
  change PowerBound (fun n => LightThreeSumReportingSetupBank.time n+
    LightThreeSumReportingSetupDense.time n (n^k) (ColorBandBounds.count n (bandSize n))+200) _
  exact (bank_time_certificate.add_same (dense_time_certificate k)).add_same
    (EncodedColorTime.const_certificate 200)

theorem time_powerBound (k : ℕ) : PowerBound (preprocessingTime k) certificateExponent := by
  change PowerBound (fun n => EncodedColorTime.preprocessingTime k n+setupTime n (n^k)+1000) _
  exact ((EncodedColorTime.pipeline_time_powerBound k).add_same (setup_time_certificate k)).add_same
    (EncodedColorTime.const_certificate 1000)

theorem time_eventually_target (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (preprocessingTime k n : ℝ) ≤ (n : ℝ)^targetExponent := by
  have hh := (time_powerBound k) (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh

theorem time_endStatementBigO (k : ℕ) :
    EndStatement.BigO (preprocessingTime k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using time_eventually_target k

end
end ThreeSum.EncodedColorReportingCosts
