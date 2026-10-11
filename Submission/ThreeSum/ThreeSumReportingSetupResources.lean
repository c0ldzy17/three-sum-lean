import Submission.ThreeSum.ThreeSumReportingSetupData
import Submission.ThreeSum.SharedReportingBankResourceBoundsDenseScales

/-! # Compose the two actual reporting allocations at an arbitrary free pointer -/

namespace ThreeSum.ThreeSumReportingSetupResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

def need (n U : ℕ) : Light.Need :=
  ⟨(SharedReportingBankResourceBounds.need n U).word+(SharedReportingBankResourceBounds.denseNeed n U).word,
    (SharedReportingBankResourceBounds.need n U).cells+(SharedReportingBankResourceBounds.denseNeed n U).cells,
    (SharedReportingBankResourceBounds.need n U).depth+(SharedReportingBankResourceBounds.denseNeed n U).depth+3⟩

theorem counter_le {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) (U : ℕ) :
    counter free n A B C hsA hsB hsC ≤ reportBase free n A B C hsA hsB hsC+
      (SharedReportingBankResourceBounds.need n U).cells := by
  obtain ⟨_,hB,hC⟩ := ThreeSumColorBudgets.normalized_lengths H
  exact (le_max_right _ _).trans (SharedReportingBankResourceBounds.space_le
    (free := reportBase free n A B C hsA hsB hsC) (h := microHalf (inputBits n))
    (J := blockCount (inputBits n)) (g := bandSize n) hB hC)

theorem bank_of_ok {lim : Limits} {n U report d : ℕ}
    (H : (need n U).Ok lim report d) :
    (SharedReportingBankResourceBounds.need n U).Ok lim report (d+2) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega) (by dsimp only [need]; omega)

theorem dense_of_ok {lim : Limits} {n U report dst d : ℕ}
    (H : (need n U).Ok lim report d)
    (hdst : dst ≤ report+(SharedReportingBankResourceBounds.need n U).cells) :
    (SharedReportingBankResourceBounds.denseNeed n U).Ok lim dst (d+1) :=
  H.mono (by dsimp only [need]; omega) (by dsimp only [need]; omega) (by dsimp only [need]; omega)

noncomputable section

theorem poly_need : Light.PolyNeed need := by
  obtain ⟨sa,ka,ha⟩ := SharedReportingBankResourceBounds.poly_need
  obtain ⟨sb,kb,hb⟩ := SharedReportingBankResourceBounds.dense_poly_need
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
  simp only [need]
  exact ⟨by omega,by omega,by omega⟩

end
end ThreeSum.ThreeSumReportingSetupResources
