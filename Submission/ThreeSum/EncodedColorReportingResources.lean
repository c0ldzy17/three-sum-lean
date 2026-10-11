import Submission.ThreeSum.EncodedColorReportingData
import Submission.ThreeSum.ThreeSumReportingSetupResources

/-! # Affine resources for source construction followed by reporting setup -/

namespace ThreeSum.EncodedColorReportingResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def need (n U : ℕ) : Light.Need :=
  ⟨(EncodedColorResources.need n U).word+(ThreeSumReportingSetupResources.need n U).word,
    (EncodedColorResources.need n U).cells+(ThreeSumReportingSetupResources.need n U).cells,
    (EncodedColorResources.need n U).depth+(ThreeSumReportingSetupResources.need n U).depth+2⟩

theorem source_of_ok {lim : Limits} {free n U d : ℕ}
    (H : (need n U).Ok lim free d) : (EncodedColorResources.need n U).Ok lim free (d+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega) (by dsimp only [need]; omega)

theorem setup_of_ok {lim : Limits} {free report n U d : ℕ}
    (H : (need n U).Ok lim free d)
    (hreport : report ≤ free+(EncodedColorResources.need n U).cells) :
    (ThreeSumReportingSetupResources.need n U).Ok lim report (d+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega) (by dsimp only [need]; omega)

theorem counter_end_le_allocation {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hn : 0 < n) (U : ℕ) :
    counter free n A B C hsA hsB hsC+4 ≤ free+(need n U).cells := by
  have hr := EncodedColorReportingData.report_le_source_allocation H hn U
  have hc := ThreeSumReportingSetupResources.counter_le H U
  have hd : 4 ≤ (SharedReportingBankResourceBounds.denseNeed n U).cells := by
    change 4 ≤ SharedReportingBankResourceBounds.denseCells n U
    unfold SharedReportingBankResourceBounds.denseCells
    omega
  dsimp only [need,ThreeSumReportingSetupResources.need]
  omega

noncomputable section

theorem poly_need : Light.PolyNeed need := by
  obtain ⟨sa,ka,ha⟩ := EncodedColorResources.poly_need
  obtain ⟨sb,kb,hb⟩ := ThreeSumReportingSetupResources.poly_need
  refine ⟨sa+sb+3,ka+kb,fun n U => ?_⟩
  let F := Light.polyBound (sa+sb) (ka+kb) [n,U]
  have hA := ha n U
  have hB := hb n U
  have hma : Light.polyBound sa ka [n,U] ≤ F := Light.polyBound_mono (by omega) (by omega) _
  have hmb : Light.polyBound sb kb [n,U] ≤ F := Light.polyBound_mono (by omega) (by omega) _
  have hF : 1 ≤ F := by
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
end ThreeSum.EncodedColorReportingResources
