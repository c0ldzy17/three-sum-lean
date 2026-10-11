import Submission.ThreeSum.EncodedColorTimeCounts

/-! # Time of the actual color extraction, normalization and incidence catalog -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger HierarchyScales

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

noncomputable section

theorem band_width_powerBound :
    PowerBound (fun n => ColorBandBounds.width n (bandSize n)) 0 := by
  have hs : PowerBound (fun n => BandPartition.size n (bandSize n)) 1 :=
    powerBound_mono identity_powerBound (Eventually.of_forall fun n => BandPartition.size_le n _)
  exact clog_powerBound (((hs.add_same hs).add_same hs).add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1)))

theorem band_time_powerBound :
    PowerBound (fun n => ColorBandBounds.time n (bandSize n)) 1 := by
  have hn := identity_powerBound.add_same ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hl := sum_zero (clog_powerBound identity_powerBound) (PowerBound.const 1)
  have hw := sum_zero band_width_powerBound (PowerBound.const 1)
  have hR := (count_one.add_same identity_powerBound).add_same
    ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have h1 : PowerBound (fun n => 2100*(n+1)*(Nat.clog 2 n+1)) 1 := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 2100).mul hn).mul hl
  have h2 : PowerBound (fun n => 1000*(ColorBandBounds.count n (bandSize n)+n+1)*
      (ColorBandBounds.width n (bandSize n)+1)) 1 := by
    simpa only [zero_add,add_zero] using ((PowerBound.const 1000).mul hR).mul hw
  exact (h1.add_same h2).add_same ((PowerBound.const 400).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))

theorem raw_catalog_time_le (n : ℕ) :
    LightBandRawAColor.catalogTime n (bandSize n) ≤ 9000*(3*bandCount n^2+1)*(bandSize n+1) := by
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  have hc := Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2)
  have hb : bandCount n ≤ bandCount n^2 := Nat.le_self_pow (by decide) _
  have hsum : ColorBandBounds.count n (bandSize n)+3*BandPartition.size n (bandSize n)+1 ≤
      3*(3*bandCount n^2+1) := by
    unfold ColorBandBounds.count
    omega
  have hh := Nat.mul_le_mul_right (bandSize n+1) (Nat.mul_le_mul_left 3000 hsum)
  have he : 3000*(3*(3*bandCount n^2+1))=9000*(3*bandCount n^2+1) := by omega
  rw [he] at hh
  exact hh

theorem raw_catalog_time_powerBound :
    PowerBound (fun n => LightBandRawAColor.catalogTime n (bandSize n)) (2-(E+bandShift)/5) := by
  have he : (0 : ℝ) ≤ (E+bandShift)/5 := by
    have h := E_bounds.1
    unfold bandShift
    linarith
  have hg := band_powerBound.add_same ((PowerBound.const 1).mono_exponent he)
  have hh := ((PowerBound.const 9000).mul BandPrimeCosts.owner_count_powerBound).mul hg
  have heq : (0 : ℝ)+2*(1-(E+bandShift)/5)+(E+bandShift)/5=2-(E+bandShift)/5 := by ring
  rw [heq] at hh
  exact powerBound_mono hh (Eventually.of_forall raw_catalog_time_le)

theorem color_bands_time_powerBound :
    PowerBound (fun n => LightBandRawAColor.time (inputBits n+1) n (bandSize n)) (3/2) := by
  have hb := sum_zero (sum_zero SharedReportingCosts.bits_powerBound (PowerBound.const 1))
    (PowerBound.const 1)
  have hn := identity_powerBound.add_same ((PowerBound.const 1).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  have hlin : PowerBound (fun n => 1200*(inputBits n+1+1)*(n+1)) 1 := by
    simpa only [zero_add] using ((PowerBound.const 1200).mul hb).mul hn
  have h1 := hlin.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)
  have h2 := band_time_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)
  have h3 := raw_catalog_time_powerBound.mono_exponent (show 2-(E+bandShift)/5 ≤ (3/2 : ℝ) by
    have h := E_bounds.1; unfold bandShift; linarith)
  have h4 := (PowerBound.const 600).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2)
  exact powerBound_mono (((h1.add_same h2).add_same h3).add_same h4)
    (Eventually.of_forall fun n => LightBandRawAColor.time_bound (inputBits n+1) n (bandSize n))

theorem normalized_layout_time_powerBound :
    PowerBound (fun n => LightEncodedColorLayout.time n (bandSize n)) 1 := by
  have hh : PowerBound (fun n => 20*n+1040) 1 := by
    have h := (PowerBound.const 20).mul identity_powerBound
    simp only [zero_add] at h
    exact h.add_same ((PowerBound.const 1040).mono_exponent (by norm_num : (0 : ℝ) ≤ 1))
  apply powerBound_mono hh
  exact Eventually.of_forall fun n => by
    have h := LightSmallDivide.time_bound (n-1) (bandSize n)
    unfold LightEncodedColorLayout.time
    omega

theorem normalize_time_powerBound : PowerBound LightEncodedColorNormalize.time (3/2) :=
  (((normalized_layout_time_powerBound.mono_exponent (by norm_num : (1 : ℝ) ≤ 3/2)).add_same
    color_bands_time_powerBound).add_same
      ((PowerBound.const 1200).mono_exponent (by norm_num : (0 : ℝ) ≤ 3/2)))

theorem normalize_time_certificate : PowerBound LightEncodedColorNormalize.time certificateExponent :=
  normalize_time_powerBound.mono_exponent (by norm_num [certificateExponent])

end
end ThreeSum.EncodedColorTime
