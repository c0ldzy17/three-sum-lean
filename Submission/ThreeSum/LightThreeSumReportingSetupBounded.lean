import Submission.ThreeSum.LightThreeSumReportingSetup
import Submission.ThreeSum.ThreeSumReportingSetupResources
import Submission.ThreeSum.SharedReportingBankResourceBoundsDenseHost

/-! # The concrete reporting preparation under one polynomial resource contract -/

namespace ThreeSum.ThreeSumReportingSetupResources

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 1000000

theorem program_meets {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hR : 4 ≤ radix n) (hx : ∀ i, |x i| ≤ (U : ℤ))
    (hok : (need n U).Ok lim (reportBase free n A B C hsA hsB hsC) d) :
    Meets lim LightThreeSumReportingSetup.program 97 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC] μ
      (LightThreeSumReportingSetup.time n U
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length)
      (fun r ν => r=(counter free n A B C hsA hsB hsC : ℤ) ∧
        ThreeSumReportingSetupData.Stored ν free n color x A B C hsA hsB hsC ∧
        Kept μ ν (reportBase free n A B C hsA hsB hsC)) := by
  have hbank := bank_of_ok hok
  have hdense := dense_of_ok hok (counter_le H U)
  obtain ⟨hs,hw,hd⟩ := SharedReportingBankResourceBounds.dense_actual_resources_of_ok hdense
  exact LightThreeSumReportingSetup.program_meets H Hparams hparams hR hbank hs hw
    (by omega) hx

end ThreeSum.ThreeSumReportingSetupResources
