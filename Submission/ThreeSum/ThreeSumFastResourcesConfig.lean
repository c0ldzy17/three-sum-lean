import Submission.ThreeSum.ThreeSumFastResourcesColor
import Submission.ThreeSum.EncodedColorWantedConsumerData

/-! # Actual retained counts in the complete wanted scan's limits

The physical count and dimensions are obtained from the stored normalized
color. No separate count or dimension bound is an assumption of the final
resource adapter.
-/

namespace ThreeSum.ThreeSumFastResources

open Light Scales BandScales ThreeSumWantedHostData SharedReportingBankResourceBounds

set_option maxHeartbeats 1600000
set_option maxRecDepth 15000

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem actual_count_le
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    ThreeSumWantedHostData.count n A B C hsA hsB hsC≤wantedScanCount n :=
  wanted_scan_count_le (EncodedColorWantedConsumerData.incidence_length_le_magnitude H)
    (EncodedColorWantedConsumerData.count_le_product H)

theorem config_dimensions
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    let cfg := config free n A B C hsA hsB hsC
    cfg.K≤cfg.J ∧ cfg.N≤3*(magnitude n)^3 ∧ cfg.NB≤n ∧ cfg.NC≤n := by
  obtain ⟨_,hb,hc⟩ := ThreeSumColorBudgets.normalized_lengths H
  exact ⟨terminal_depth_le n,EncodedColorWantedConsumerData.incidence_length_le_magnitude H,hb,hc⟩

/-- Limits for Scan153 at depth `d+1`, with its induction budget
`D=d+1+count` and its actual physical count as `N`. -/
theorem actual_scan_resources_of_ok {lim : Limits} {U d : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hok : (need n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d) :
    ThreeSumWantedHostData.count n A B C hsA hsB hsC+1≤lim.space ∧
      d+1+ThreeSumWantedHostData.count n A B C hsA hsB hsC+1≤lim.depth ∧
      ((ThreeSumWantedHostData.count n A B C hsA hsB hsC+4 : ℕ) : ℤ)≤lim.word := by
  have hc := actual_count_le H
  have hs := wanted_scan_count_envelope n
  have hcells := hok.cells
  change (config free n A B C hsA hsB hsC).layoutHeader+wantedEnvelope n≤lim.space at hcells
  have hd := hok.depth
  change d+(wantedEnvelope n+wantedScanCount n+4+2)≤lim.depth at hd
  exact ⟨by omega,by omega,wanted_scan_count_word hc (scan_of_ok hok)⟩

theorem actual_step_of_ok {lim : Limits} {U d e : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (he : e≤d+ThreeSumWantedHostData.count n A B C hsA hsB hsC+5)
    (hok : (need n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d) :
    (wantedNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader e :=
  step_of_ok (actual_count_le H) he hok

theorem color_step_of_ok {lim : Limits} {U d e : ℕ}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (he : e≤d+ThreeSumWantedHostData.count n A B C hsA hsB hsC+6)
    (hok : (ThreeSumFastResourcesColor.need n U).Ok lim free d) :
    (wantedNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader e :=
  actual_step_of_ok H.encoded (by omega) (ThreeSumFastResourcesColor.wanted_of_stored H hn hok)

end ThreeSum.ThreeSumFastResources
