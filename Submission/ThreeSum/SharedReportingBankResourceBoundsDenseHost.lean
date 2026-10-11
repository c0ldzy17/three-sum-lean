import Submission.ThreeSum.SharedReportingBankResourceBoundsDenseScales
import Submission.ThreeSum.LightThreeSumReportingSetupDense

/-! # Actual header-loaded dense initialization under its proved Need -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Scales BandScales

set_option maxHeartbeats 1600000
set_option maxRecDepth 16000

theorem dense_word_eq (n U : ℕ) : denseWord n U=LightThreeSumReportingSetupDense.word n U := rfl

theorem dense_actual_resources_of_ok {lim : Limits} {dst n U d : ℕ}
    (hok : (denseNeed n U).Ok lim dst d) :
    LightWeightedScore.space (dst+4) (ArithmeticStageBounds.maxMod n) (bandSize n) U ≤ lim.space ∧
    (LightThreeSumReportingSetupDense.word n U : ℤ) ≤ lim.word ∧
      d+Nat.clog 2 (ArithmeticStageBounds.maxMod n)+8 ≤ lim.depth := by
  simpa only [dense_word_eq] using dense_resources_of_ok hok

theorem dense_program_meets {lim : Limits} {d : ℕ} {μ : ℕ→ℤ} {free n params U dst : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19≤free)
    (hR : 4≤radix n)
    (hprior : ThreeSumReportingSetupData.reportBase free n A B C hsA hsB hsC≤dst)
    (hx : ∀ i, |x i|≤(U : ℤ)) (hok : (denseNeed n U).Ok lim dst d) :
    Meets lim LightThreeSumReportingSetupDense.program 20 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,dst] μ
      (LightThreeSumReportingSetupDense.time n U
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length)
      (fun r ν => r=(dst : ℤ) ∧
        LightDenseSetup.Stored ν dst
          (GlobalEncoding.representationCap (microHalf (inputBits n)) (blockCount (inputBits n)))
          (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC) ∧
        EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧ Kept μ ν dst) := by
  obtain ⟨hs,hw,hd⟩ := dense_actual_resources_of_ok hok
  exact LightThreeSumReportingSetupDense.program_meets H Hparams hparams hok.space hR hprior hs hw hd hx

end ThreeSum.SharedReportingBankResourceBounds
