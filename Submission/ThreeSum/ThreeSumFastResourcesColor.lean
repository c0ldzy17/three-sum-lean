import Submission.ThreeSum.ThreeSumFastResources
import Submission.ThreeSum.EncodedColorReportingResources

/-! # One affine allocation for a complete selected color

The prelude retains its source and reporting catalogs, ending with the dense
counter. The wanted scan reuses scratch beginning four cells after that
counter. The two exact resource records are combined without bounding the
absolute starting address.
-/

namespace ThreeSum.ThreeSumFastResourcesColor

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

def need (n U : ℕ) : Light.Need :=
  ⟨(EncodedColorReportingResources.need n U).word+(ThreeSumFastResources.need n U).word,
    (EncodedColorReportingResources.need n U).cells+(ThreeSumFastResources.need n U).cells,
    (EncodedColorReportingResources.need n U).depth+(ThreeSumFastResources.need n U).depth+3⟩

theorem prelude_of_ok {lim : Limits} {free n U d : ℕ}
    (H : (need n U).Ok lim free d) :
    (EncodedColorReportingResources.need n U).Ok lim free (d+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem wanted_of_ok {lim : Limits} {free ctr n U d : ℕ}
    (H : (need n U).Ok lim free d)
    (hctr : ctr+4≤free+(EncodedColorReportingResources.need n U).cells) :
    (ThreeSumFastResources.need n U).Ok lim (ctr+4) (d+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega)
    (by dsimp only [need]; omega)

theorem wanted_of_stored {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (need n U).Ok lim free d) :
    (ThreeSumFastResources.need n U).Ok lim
      (counter free n A B C hsA hsB hsC+4) (d+1) :=
  wanted_of_ok hok (EncodedColorReportingResources.counter_end_le_allocation H.encoded hn U)

theorem scan_of_stored {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (need n U).Ok lim free d) :
    (SharedReportingBankResourceBounds.wantedScanNeed n U).Ok lim
      (counter free n A B C hsA hsB hsC+4) (d+2) := by
  simpa only [Nat.add_assoc] using ThreeSumFastResources.scan_of_ok (wanted_of_stored H hn hok)

theorem header_resources_of_stored {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (need n U).Ok lim free d) :
    counter free n A B C hsA hsB hsC+50+2*blockCount (inputBits n)≤lim.space ∧
      (ThreeSumFastResources.headerWord n : ℤ)≤lim.word ∧ d+1<lim.depth := by
  have hw := wanted_of_stored H hn hok
  exact ⟨ThreeSumFastResources.header_space_of_ok hw,
    ThreeSumFastResources.header_word_of_ok hw,ThreeSumFastResources.outer_depth_of_ok hw⟩

/-- The outer color call can load the counter at the returned source header plus14. -/
theorem counter_read_resources_of_stored {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0<n) (hok : (need n U).Ok lim free d) :
    EncodedColorPipelineData.finish free n A B C hsA hsB hsC+15≤lim.space ∧
      counter free n A B C hsA hsB hsC+4≤lim.space := by
  have hw := wanted_of_stored H hn hok
  have hc := hw.cells
  have hp := report_le_counter free n A B C hsA hsB hsC
  unfold reportBase at hp
  omega

theorem outer_depth_of_ok {lim : Limits} {free n U d : ℕ}
    (H : (need n U).Ok lim free d) : d<lim.depth := by
  have hd := H.depth
  dsimp only [need] at hd
  omega

noncomputable section

theorem poly_need : Light.PolyNeed need := by
  obtain ⟨sa,ka,ha⟩ := EncodedColorReportingResources.poly_need
  obtain ⟨sb,kb,hb⟩ := ThreeSumFastResources.poly_need
  refine ⟨sa+sb+3,ka+kb,fun n U => ?_⟩
  let F := Light.polyBound (sa+sb) (ka+kb) [n,U]
  have hA := ha n U
  have hB := hb n U
  have hma : Light.polyBound sa ka [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hmb : Light.polyBound sb kb [n,U]≤F := Light.polyBound_mono (by omega) (by omega) _
  have hF : 1≤F := by
    unfold F Light.polyBound
    simp only [List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    exact Nat.mul_pos (by positivity) (by positivity)
  have he : Light.polyBound (sa+sb+3) (ka+kb) [n,U]=8*F := by
    unfold F Light.polyBound
    rw [pow_add]
    norm_num
    ring
  rw [he]
  dsimp only [need]
  exact ⟨by omega,by omega,by omega⟩

end
end ThreeSum.ThreeSumFastResourcesColor
