import Submission.ThreeSum.ThreeSumFastResourcesConfig
import Submission.ThreeSum.LightThreeSumWantedHost

/-! # The actual154 wanted-header loader from its concrete Need

The executable loader and its exact scan call remain unchanged. Its
numeric controls and relative address bounds follow from the resource
record used by the complete selected-color program.
-/

namespace ThreeSum.ThreeSumFastResources

open Light Scales ThreeSumReportingSetupData ThreeSumWantedHostData

set_option maxHeartbeats 1900000
set_option maxRecDepth 17000

theorem header_word_eq (n : ℕ) : headerWord n=LightThreeSumWantedHost.word n := rfl

theorem program_meets {lim : Limits} {d T U : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19≤free)
    (hok : (need n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d)
    (hscan : Meets lim LightReportingWantedScan.program 152 (d+1)
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    Meets lim LightThreeSumWantedHost.program 153 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        counter free n A B C hsA hsB hsC] μ (T+4000) Q := by
  apply LightThreeSumWantedHost.program_meets H Hparams hparams hok.space (outer_depth_of_ok hok)
    (header_space_of_ok hok) _ hscan
  simpa only [header_word_eq] using header_word_of_ok hok

theorem color_program_meets {lim : Limits} {d T U : ℕ} {μ : ℕ→ℤ} {free n params : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19≤free)
    (hn : 0<n) (hok : (ThreeSumFastResourcesColor.need n U).Ok lim free d)
    (hscan : Meets lim LightReportingWantedScan.program 152 (d+2)
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (ThreeSumWantedHostData.count n A B C hsA hsB hsC)) μ T Q) :
    Meets lim LightThreeSumWantedHost.program 153 (d+1)
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC,
        counter free n A B C hsA hsB hsC] μ (T+4000) Q :=
  program_meets H Hparams hparams (ThreeSumFastResourcesColor.wanted_of_stored H hn hok) hscan

end ThreeSum.ThreeSumFastResources
