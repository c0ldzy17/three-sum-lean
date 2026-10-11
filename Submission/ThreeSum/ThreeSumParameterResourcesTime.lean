import Submission.ThreeSum.ThreeSumParameterResources
import Submission.ThreeSum.EncodedColorTimeScales

/-! # Charge the executed parameter initialization

The actual square-root and quotient loops are bounded by the band root and
divisor. Polynomial storage envelopes do not replace these time bounds.
-/

namespace ThreeSum.ThreeSumParameterResources

open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds
open Filter Parameters ArithmeticStageBounds

set_option maxHeartbeats 1900000
set_option maxRecDepth 14000

def timeBudget (n : ℕ) : ℕ :=
  10000*(inputBits n+1+blocks n+mu n+bandRoot n+bandDivisor n+localEnvelope n)

theorem time_le_budget (n : ℕ) : LightParameterInit.time n ≤ timeBudget n := by
  have hc := LightScales.time_bound n
  have hl := (LocalParameterBounds.time_bound (LightParameterInit.half n)).trans (local_envelope_le n)
  have hg : LightGlobalSizes.time (LightGlobalSizes.localCount n) (blockCount (inputBits n)) (mu n) ≤
      1000*(blocks n+mu n+bandRoot n+bandDivisor n+1) := by
    simpa only [LightGlobalSizes.root,LightGlobalSizes.localCount_pow,LightGlobalSizes.divisor,
      bandRoot,bandDivisor,blocks] using
      LightGlobalSizes.time_bound (LightGlobalSizes.localCount n) (blockCount (inputBits n)) (mu n)
  have hs := Nat.sqrt_le_self (inputBits n)
  have he : windowExponent (inputBits n) ≤ inputBits n+1 := by unfold windowExponent; omega
  unfold timeBudget LightParameterInit.time LightNatPower.time sqrtTime
  omega

noncomputable section

theorem timeBudget_powerBound : PowerBound timeBudget 1 := by
  have hsmall : PowerBound (fun n => inputBits n+1+blocks n+mu n) 0 :=
    ((SharedReportingCosts.bits_powerBound.add_same (PowerBound.const 1)).add_same
      EncodedColorTime.blocks_powerBound).add_same EncodedColorTime.mu_powerBound
  have hroot : PowerBound bandRoot 1 :=
    (PowerBound.of_rate bandRoot_log_rate).mono_exponent (by have hh := E_bounds.2; linarith)
  have hdiv : PowerBound bandDivisor 1 :=
    (PowerBound.of_rate bandDivisor_log_rate).mono_exponent (by norm_num)
  have hlocal := localEnvelope_powerBound.mono_exponent (by norm_num : (0 : ℝ)≤1)
  have hh := (((hsmall.mono_exponent (by norm_num : (0 : ℝ)≤1)).add_same hroot).add_same hdiv).add_same hlocal
  change PowerBound (fun n => 10000*(inputBits n+1+blocks n+mu n+bandRoot n+bandDivisor n+localEnvelope n)) 1
  simpa only [zero_add] using (PowerBound.const 10000).mul hh

theorem time_powerBound : PowerBound LightParameterInit.time 1 :=
  powerBound_mono timeBudget_powerBound (Eventually.of_forall time_le_budget)

theorem time_certificate : PowerBound LightParameterInit.time certificateExponent :=
  time_powerBound.mono_exponent (by norm_num [certificateExponent])

theorem time_endStatementBigO : EndStatement.BigO LightParameterInit.time (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  have hh := time_certificate (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa [targetExponent] using hh

end
end ThreeSum.ThreeSumParameterResources
