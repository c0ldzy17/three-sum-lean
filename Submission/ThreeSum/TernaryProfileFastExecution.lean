import Submission.ThreeSum.TernaryProfileRuntime
import Submission.ThreeSum.TernaryColoredExecution

noncomputable section
namespace ThreeSum.TernaryConcreteProfile.Profile
open Light LightTernaryFastProgramProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

/-- Every coloring invokes the literal proved colored solver on the actual
global backend, input segment, and six-cell coloring record. -/
theorem fastExecution (P : Profile κ) :
    TernarySolverEndBridge.FastExecution P.program P.main κ P.cutoff P.fastTime P.need :=by
  intro lim src n free depth x μ hcutoff hn hsrc hneed hinput hbound
  have hrun:=TernaryFastProgramResources.meets_of_color
    (colorMain:=TernaryExecutable.colorMain (p:=P.p) P.K)
    (colorTime:=P.colorTime n) P.color P.colorNeed x μ
    P.M_gt_one P.radix_gt_one hn (by omega) hneed
    (fun c hc ν₀ hreceipt i hi ν hkeep hfields dd hd =>
      TernaryColoredExecution.meets P x μ ν₀ ν hi hcutoff hsrc hreceipt hkeep hfields hd hinput hbound)
  simpa only [Profile.program,TernaryExecutable.program,Profile.main,TernaryExecutable.main,
    LightTernaryFastProgram.mainEntry,Profile.color,TernaryExecutable.color_length,Profile.fastTime] using hrun

end ThreeSum.TernaryConcreteProfile.Profile
