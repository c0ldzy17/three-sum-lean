import Submission.ThreeSum.EncodedColorTimeCounts

/-! # Time of constructing the retained local cover and all global key rows -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger LocalCoverBounds GlobalEncoding

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

theorem local_magnitude_le (n : ℕ) :
    LightLocalCoverMagnitude.magnitude (half n) ≤ localEnvelope n := by
  unfold LightLocalCoverMagnitude.magnitude localEnvelope LightLocalCoverInitResources.envelope
  exact Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by decide : 600000 ≤ 5000000))

noncomputable section

theorem local_schedule_powerBound : PowerBound (fun n => scheduleSize (half n)) 0 := by
  apply powerBound_mono localEnvelope_powerBound
  exact Eventually.of_forall fun n => by
    have h := (LightLocalCoverMagnitude.bounds (half n)).rounds.trans (local_magnitude_le n)
    omega

theorem local_layer_powerBound : PowerBound (fun n => outputCount (512*half n) (half n)) 0 := by
  apply powerBound_mono localEnvelope_powerBound
  exact Eventually.of_forall fun n => by
    have h := (LightLocalCoverMagnitude.bounds (half n)).maskPower.trans (local_magnitude_le n)
    have hp := Nat.pow_le_pow_right (by decide : 1 ≤ 2) (Nat.le_succ (512*half n))
    exact (Nat.choose_le_two_pow _ _).trans (hp.trans (by omega))

theorem local_cover_time_powerBound : PowerBound (fun n => LightLocalCoverInit.time (half n)) 0 :=
  powerBound_mono localEnvelope_powerBound (Eventually.of_forall fun n =>
    LightLocalCoverInitResources.time_bound (half n))

theorem global_keys_time_powerBound :
    PowerBound (fun n => LightGlobalKeys.time (half n) (blocks n)) (2*epsilon*E) := by
  have he : (0 : ℝ) ≤ 2*epsilon*E := by
    have h := E_bounds.1
    unfold epsilon
    linarith
  have hl := sum_zero local_width_powerBound (PowerBound.const 1)
  have hq := sum_zero local_layer_powerBound (PowerBound.const 1)
  have hs := sum_zero local_schedule_powerBound (PowerBound.const 1)
  have hlocal := product_zero (product_zero (product_zero (PowerBound.const 2000) hl) hq) hs
  have hj := sum_zero blocks_powerBound (PowerBound.const 1)
  have hg := keys_powerBound.add_same ((PowerBound.const 1).mono_exponent he)
  have hglobal : PowerBound (fun n => 300*(blocks n+1)*
      (LightGlobalKeys.localCount (half n)^(blocks n)+1)) (2*epsilon*E) := by
    simpa only [zero_add,LightGuardedWanted.totalKeys] using (product_zero (PowerBound.const 300) hj).mul hg
  exact powerBound_mono (((hlocal.mono_exponent he).add_same hglobal).add_same
    ((PowerBound.const 200).mono_exponent he))
    (Eventually.of_forall fun n => LightGlobalKeys.time_bound (half n) (blocks n))

theorem cover_time_powerBound :
    PowerBound (fun n => LightCoverKeys.time (half n) (blocks n)) (2*epsilon*E) := by
  have he : (0 : ℝ) ≤ 2*epsilon*E := by
    have h := E_bounds.1
    unfold epsilon
    linarith
  exact ((local_cover_time_powerBound.mono_exponent he).add_same global_keys_time_powerBound).add_same
    ((PowerBound.const 200).mono_exponent he)

theorem cover_time_certificate :
    PowerBound (fun n => LightCoverKeys.time (half n) (blocks n)) certificateExponent :=
  cover_time_powerBound.mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

end
end ThreeSum.EncodedColorTime
