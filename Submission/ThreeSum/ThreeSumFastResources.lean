import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedScan
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedGuardMass
import Submission.ThreeSum.LightBandRawAResources
import Submission.ThreeSum.EncodedColorStageCosts

/-! # Relative limits for the complete wanted-header loader and scan

All numeric controls come from the input size. The loader starts its reusable
scratch at `counter+4`; every retained absolute pointer is handled by its
individual allocation end rather than being included in a numeric envelope.
-/

namespace ThreeSum.ThreeSumFastResources

open Light Scales BandScales StageBounds SharedReportingBankResourceBounds

set_option maxHeartbeats 2100000
set_option maxRecDepth 15000

def headerWord (n : ℕ) : ℕ :=
  n+blocks n+half n+LightSwitchDepth.depth (blocks n)+bandSize n+radix n+
    OutputDecodeRecords.layerCount (half n)+GlobalEncoding.scheduleSize (half n)+
    ColorBandBounds.count n (bandSize n)+EncodedColorStageCosts.incidenceCap n+50

/-- Two outer call levels above the actual whole-wanted scan. -/
def need (n U : ℕ) : Light.Need :=
  ⟨(wantedScanNeed n U).word,(wantedScanNeed n U).cells,(wantedScanNeed n U).depth+2⟩

theorem terminal_depth_le (n : ℕ) : LightSwitchDepth.depth (blocks n)≤blocks n :=
  SharedReportingBankLevels.level_le le_rfl

theorem record_cap_le (n : ℕ) : ColorBandBounds.count n (bandSize n)≤3*(magnitude n)^2 :=
  (LightBandRawAResources.count_le n (bandSize n)).trans
    (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left (input_le_magnitude n) 2))

theorem incidence_cap_le (n : ℕ) : EncodedColorStageCosts.incidenceCap n≤3*(magnitude n)^3 := by
  have hh := Nat.mul_le_mul (band_le_magnitude n) (record_cap_le n)
  unfold EncodedColorStageCosts.incidenceCap
  calc
    _ ≤ magnitude n*(3*(magnitude n)^2) := hh
    _ = _ := by ring

theorem radix_le (n : ℕ) : radix n≤magnitude n := wanted_modulus_le_magnitude n

theorem header_word_le (n : ℕ) : headerWord n≤wantedEnvelope n := by
  have hn := input_le_magnitude n
  have hJ := (components n).blocksBound
  have hL := (components n).localWidthBound
  have hK := terminal_depth_le n
  have hg := band_le_magnitude n
  have hr := radix_le n
  have hl := local_layer_le_magnitude n
  have hs : GlobalEncoding.scheduleSize (half n)≤magnitude n := local_schedule_le_magnitude n
  have hR := record_cap_le n
  have hN := incidence_cap_le n
  have h2 := wanted_power_le n 2 10 (by decide)
  have h3 := wanted_power_le n 3 10 (by decide)
  have hM : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold headerWord wantedEnvelope
  omega

theorem header_slack_le (n : ℕ) : 50+2*blocks n≤wantedEnvelope n := by
  have hJ := (components n).blocksBound
  have hM : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope
  omega

theorem scan_of_ok {lim : Limits} {n U dst d : ℕ} (hok : (need n U).Ok lim dst d) :
    (wantedScanNeed n U).Ok lim dst (d+1) :=
  hok.mono le_rfl le_rfl (by dsimp only [need]; omega)

theorem step_of_ok {lim : Limits} {n U dst d count e : ℕ}
    (hcount : count≤wantedScanCount n) (he : e≤d+count+5)
    (hok : (need n U).Ok lim dst d) : (wantedNeed n U).Ok lim dst e :=
  wanted_scan_at_depth_of_ok hcount (by omega) (scan_of_ok hok)

theorem header_space_of_ok {lim : Limits} {n U counter d : ℕ}
    (hok : (need n U).Ok lim (counter+4) d) : counter+50+2*blocks n≤lim.space := by
  have hc := hok.cells
  change counter+4+wantedEnvelope n≤lim.space at hc
  have hh := header_slack_le n
  omega

theorem header_word_of_ok {lim : Limits} {n U dst d : ℕ}
    (hok : (need n U).Ok lim dst d) : (headerWord n : ℤ)≤lim.word := by
  have hh := (header_word_le n).trans (Nat.le_mul_of_pos_right _ (by omega : 0<U+1))
  exact (Int.ofNat_le.mpr hh).trans hok.word

theorem outer_depth_of_ok {lim : Limits} {n U dst d : ℕ}
    (hok : (need n U).Ok lim dst d) : d<lim.depth := by
  have hh := hok.depth
  change d+((wantedNeed n U).depth+wantedScanCount n+4+2)≤lim.depth at hh
  omega

noncomputable section

theorem poly_need : Light.PolyNeed need := by
  have he : PowerBound (fun n => 3*wantedEnvelope n) 20480 := by
    simpa only [zero_add] using (PowerBound.const 3).mul wanted_envelope_powerBound
  apply PolynomialResources.polyNeed_of_envelope he 1
  · intro n U
    simp only [need,wantedScanNeed,wantedNeed,pow_one]
    nlinarith only [Nat.zero_le (wantedEnvelope n*(U+1))]
  · intro n U
    simp only [need,wantedScanNeed,wantedNeed,pow_one]
    have hh : wantedEnvelope n≤wantedEnvelope n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith only [hh]
  · intro n U
    simp only [need,wantedScanNeed,wantedNeed,pow_one]
    have hc := wanted_scan_count_envelope n
    have hp := wanted_envelope_positive n
    have hh : 3*wantedEnvelope n≤3*wantedEnvelope n*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
    omega

end
end ThreeSum.ThreeSumFastResources
