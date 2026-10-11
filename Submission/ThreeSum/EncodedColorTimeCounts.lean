import Submission.ThreeSum.EncodedColorTimeScales
import Submission.ThreeSum.ThreeSumColorBudgets

/-! # Exact physical count scales for the selected-color preprocessing -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger HierarchyScales

set_option maxHeartbeats 1600000
set_option maxRecDepth 12000

noncomputable section

theorem band_powerBound : PowerBound bandSize ((E+bandShift)/5) :=
  PowerBound.of_rate MassScales.bandSize_log_rate_shift

theorem count_powerBound :
    PowerBound (fun n => ColorBandBounds.count n (bandSize n)) (2*(1-(E+bandShift)/5)) := by
  apply powerBound_mono BandPrimeCosts.owner_count_powerBound
  exact Eventually.of_forall fun n => by
    have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
    have hh := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
    exact hh.trans (Nat.le_succ _)

theorem incidence_powerBound :
    PowerBound EncodedColorStageCosts.incidenceCap (2-(E+bandShift)/5) := by
  have hh := band_powerBound.mul count_powerBound
  convert hh using 1 <;> (first | rfl | ring)

theorem keys_powerBound :
    PowerBound (fun n => LightGuardedWanted.totalKeys (half n) (blocks n)) (2*epsilon*E) := by
  have hh := (PowerBound.of_rate TrimScales.scheduleCount_log_rate).mul
    (PowerBound.of_rate typedOutputs_log_ratio_tendsto)
  have he : (0 : ℝ)+2*E/5=2*epsilon*E := by unfold epsilon; ring
  rw [he] at hh
  simpa only [half,blocks,ThreeSumColorBudgets.total_keys_eq] using hh

theorem wanted_rows_le (n : ℕ) :
    3*EncodedColorStageCosts.incidenceCap n*LightGuardedWanted.totalKeys (half n) (blocks n)/radix n ≤
      UniformStageBounds.wantedBudget n := by
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hcap : EncodedColorStageCosts.incidenceCap n ≤ bandSize n*(3*bandCount n^2) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2))
  have hc := Nat.mul_le_mul_right (LightGuardedWanted.totalKeys (half n) (blocks n))
    (Nat.mul_le_mul_left 3 hcap)
  have he : 3*(bandSize n*(3*bandCount n^2))*LightGuardedWanted.totalKeys (half n) (blocks n)=
      MassScales.wantedNumerator n := by
    rw [show LightGuardedWanted.totalKeys (half n) (blocks n)=
      TrimScales.scheduleCount n*typedOutputs n from ThreeSumColorBudgets.total_keys_eq n]
    unfold MassScales.wantedNumerator
    ring
  rw [he] at hc
  exact Nat.div_le_div_right hc

theorem wanted_rows_powerBound :
    PowerBound (fun n =>
      3*EncodedColorStageCosts.incidenceCap n*LightGuardedWanted.totalKeys (half n) (blocks n)/radix n)
      (2-(1/2+bandShift)/5) :=
  powerBound_mono UniformStageBounds.wantedBudget_powerBound (Eventually.of_forall wanted_rows_le)

theorem incidence_three_halves : PowerBound EncodedColorStageCosts.incidenceCap (3/2) :=
  incidence_powerBound.mono_exponent (by have h := E_bounds.1; unfold bandShift; linarith)

theorem count_one : PowerBound (fun n => ColorBandBounds.count n (bandSize n)) 1 :=
  count_powerBound.mono_exponent (by have h := E_bounds.1; unfold bandShift; linarith)

theorem keys_certificate :
    PowerBound (fun n => LightGuardedWanted.totalKeys (half n) (blocks n)) certificateExponent :=
  keys_powerBound.mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

theorem incidence_certificate : PowerBound EncodedColorStageCosts.incidenceCap certificateExponent :=
  incidence_three_halves.mono_exponent (by norm_num [certificateExponent])

theorem radix_certificate : PowerBound radix certificateExponent :=
  (PowerBound.of_rate radix_log_ratio_tendsto).mono_exponent (by
    have h := E_bounds.2
    unfold certificateExponent
    linarith)

theorem wanted_rows_certificate :
    PowerBound (fun n =>
      3*EncodedColorStageCosts.incidenceCap n*LightGuardedWanted.totalKeys (half n) (blocks n)/radix n)
      certificateExponent :=
  wanted_rows_powerBound.mono_exponent (by norm_num [bandShift,certificateExponent])

end
end ThreeSum.EncodedColorTime
