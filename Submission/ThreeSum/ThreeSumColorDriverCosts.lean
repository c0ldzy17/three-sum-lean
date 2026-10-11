import Submission.ThreeSum.LightThreeSumFastDriver
import Submission.ThreeSum.LightColorScanCosts
import Submission.ThreeSum.ThreeSumParameterResourcesTime

/-! # Exact outer-driver time from the concrete per-color certificate -/

namespace ThreeSum.ThreeSumColorDriverCosts

open Scales Parameters StageBounds ArithmeticStageBounds

set_option maxHeartbeats 1800000

noncomputable section

theorem time_powerBound {T : ℕ→ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 1≤a) :
    PowerBound (fun n => LightThreeSumFastDriver.time (T n) n) a := by
  have hzero : 0≤a := by linarith
  have hparams := ThreeSumParameterResources.time_powerBound.mono_exponent ha
  have hscan := LightColorScanCosts.time_powerBound hT hzero
  change PowerBound (fun n => LightParameterInit.time n+LightColorScanHost.time (T n) n+500) a
  exact (hparams.add_same hscan).add_same ((PowerBound.const 500).mono_exponent hzero)

theorem time_certificate {T : ℕ→ℕ} (hT : PowerBound T certificateExponent) :
    PowerBound (fun n => LightThreeSumFastDriver.time (T n) n) certificateExponent :=
  time_powerBound hT (by norm_num [certificateExponent])

theorem time_eventually_target {T : ℕ→ℕ} (hT : PowerBound T certificateExponent) :
    ∀ᶠ n : ℕ in Filter.atTop, (LightThreeSumFastDriver.time (T n) n : ℝ)≤(n : ℝ)^targetExponent := by
  have hh := time_certificate hT (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh

theorem time_endStatementBigO {T : ℕ→ℕ} (hT : PowerBound T certificateExponent) :
    EndStatement.BigO (fun n => LightThreeSumFastDriver.time (T n) n) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using time_eventually_target hT

end
end ThreeSum.ThreeSumColorDriverCosts
