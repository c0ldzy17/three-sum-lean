import Submission.ThreeSum.SharedReportingCosts

/-!
# Exponent of the complete shared-catalog invocation budget

The local balanced-pair enumeration and all polynomial factors in the
concrete52-procedure constructor have exponent zero. Multiplying the
existing box ledger by this overhead therefore preserves its exponent.
This charges catalog invocations; the surrounding bank iterator is separate.
-/

namespace ThreeSum.SharedReportingCosts

open Filter Real Scales Parameters StageBounds ArithmeticStageBounds
open scoped Topology

set_option maxHeartbeats 1500000

noncomputable section

theorem bits_powerBound : PowerBound inputBits 0 := by
  have hh : PowerBound (fun n => primeWindow n^2) 0 := by
    simpa only [mul_zero] using window_powerBound.pow 2
  exact powerBound_mono hh (Eventually.of_forall fun n => by
    have h := bits_le_window_square n
    omega)

theorem half_powerBound : PowerBound half 0 :=
  powerBound_mono bits_powerBound (Eventually.of_forall fun n =>
    LightScales.microHalf_le_self (inputBits n))

theorem blocks_powerBound : PowerBound blocks 0 := by
  have hh : PowerBound (fun n => 20*inputBits n) 0 := by
    simpa only [zero_add] using (PowerBound.const 20).mul bits_powerBound
  exact powerBound_mono hh (Eventually.of_forall fun n =>
    LightScales.blockCount_le (inputBits n))

theorem local_width_powerBound : PowerBound localWidth 0 := by
  change PowerBound (fun n => 512*half n) 0
  simpa only [zero_add] using (PowerBound.const 512).mul half_powerBound

theorem width_powerBound : PowerBound width 0 := by
  change PowerBound (fun n => blocks n*localWidth n) 0
  simpa only [zero_add] using blocks_powerBound.mul local_width_powerBound

theorem overhead_powerBound : PowerBound overhead 0 := by
  have hw := width_powerBound.add_same (PowerBound.const 1)
  have hl := local_width_powerBound.add_same (PowerBound.const 1)
  have hj := blocks_powerBound.add_same (PowerBound.const 1)
  have hs : PowerBound (localSearch 257) 0 :=
    PowerBound.of_rate (localSearch_log_ratio_tendsto_zero 257)
  have ht1 : PowerBound (fun n => 100000*(width n+1)^5) 0 := by
    simpa only [mul_zero, zero_add] using (PowerBound.const 100000).mul (hw.pow 5)
  have ht2 : PowerBound (fun n => 5000*(localWidth n+1)^2*(localSearch 257 n+1)) 0 := by
    simpa only [mul_zero, zero_add] using
      ((PowerBound.const 5000).mul (hl.pow 2)).mul (hs.add_same (PowerBound.const 1))
  have ht3 : PowerBound (fun n => 1200*(blocks n+1)) 0 := by
    simpa only [zero_add] using (PowerBound.const 1200).mul hj
  have ht4 : PowerBound (fun n => 2000*(width n+1)) 0 := by
    simpa only [zero_add] using (PowerBound.const 2000).mul hw
  exact (((ht1.add_same ht2).add_same ht3).add_same ht4).add_same (PowerBound.const 1050)

theorem budget_powerBound : PowerBound budget (2-epsilon*boxSaving) := by
  change PowerBound (fun n => overhead n*boxCount n) (2-epsilon*boxSaving)
  simpa only [zero_add] using overhead_powerBound.mul boxes_powerBound

theorem budget_certificate : PowerBound budget certificateExponent :=
  budget_powerBound.mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

theorem budget_eventually_target :
    ∀ᶠ n : ℕ in atTop, (budget n : ℝ) ≤ (n : ℝ)^targetExponent := by
  have hh := budget_certificate (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh

theorem budget_endStatementBigO : EndStatement.BigO budget (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using budget_eventually_target

theorem shared_time_powerBound : PowerBound sharedTime (2-epsilon*boxSaving) :=
  powerBound_mono budget_powerBound (Eventually.of_forall shared_time_le)

end
end ThreeSum.SharedReportingCosts
