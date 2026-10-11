import Submission.ThreeSum.LightEncodedColorReportingPipeline
import Submission.ThreeSum.ThreeSumFastResourcesHost
import Submission.ThreeSum.LightReportingWantedScanStored
import Submission.ThreeSum.ThreeSumWantedHostDecision
import Submission.ThreeSum.ThreeSumWantedHostScanCosts

/-!
# Execute a complete selected color of the original input

The fixed355 prelude prepares the actual encoding and shared source bank.
The fixed154 header caller then executes the physical wanted scan. Their
verified semantic and time connections yield the original color witness.
-/

namespace ThreeSum.LightThreeSumColor

open Light Scales BandScales ThreeSumReportingSetupData
open ThreeSumWantedHostConditions SharedTraversalCosts

set_option maxHeartbeats 2800000
set_option maxRecDepth 18000

def body (pPrelude pWanted : ℕ) : Stmt :=
  .call pPrelude [v 0,v 1,v 2,v 3,v 4] 5 ;;
  .set 6 (M (v 5 +' k 14)) ;;
  .call pWanted [v 1,v 2,v 4,v 5,v 6] 0

def joined : Program := ReportingHostRelocation.program
  LightEncodedColorReportingPipeline.program LightThreeSumWantedHost.program

def program : Program := joined++[body 354 508]

theorem program_length : program.length=510 := rfl

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {src n params row free k d : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n→ℤ)
    (hn : Ready k n) (hsrc : src+n≤free) (hparams : params+19≤free) (hrow : row+6≤free)
    (hok : (ThreeSumFastResourcesColor.need n (n^k)).Ok lim free d)
    (hread : Seg μ src (List.ofFn x)) (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 509 d [src,n,params,row,free] μ (colorBudget k n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ ColorClassLists.witness color x) ∧ Kept μ ξ free) := by
  have hw := hok.space
  have hd := ThreeSumFastResourcesColor.outer_depth_of_ok hok
  apply Meets.of_body (p := 509) (by rfl : program[509]?=some (body 354 508))
  unfold body colorBudget
  have hPrelude := ((LightEncodedColorReportingPipeline.program_meets (d := d+1)
    color x hn.positive hn.radix hsrc hparams hrow
    (ThreeSumFastResourcesColor.prelude_of_ok hok) hread hx hparameters hcolor).append
      (LightThreeSumWantedHost.program.map (ReportingHostRelocation.relocate 355))).append [body 354 508]
  simp only [LightEncodedColorReportingPipeline.time] at hPrelude
  light_call hPrelude with header ν ⟨hout,hkeepPrelude⟩
  obtain ⟨A,hsA,B,hsB,C,hsC,hheader,H⟩ := hout
  let sourceHeader := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let ctr := counter free n A B C hsA hsB hsC
  have hheader' : header=(sourceHeader : ℤ) := hheader
  have hctrRead : ν (sourceHeader+14)=(ctr : ℤ) := EncodedColorReportingData.counter_read H
  obtain ⟨hsourceSpace,hctrSpace⟩ := ThreeSumFastResourcesColor.counter_read_resources_of_stored
    H hn.positive hok
  change sourceHeader+15≤lim.space at hsourceSpace
  change ctr+4≤lim.space at hctrSpace
  have hsourceWord : (sourceHeader : ℤ)+14≤lim.word := by
    have hh := (Int.ofNat_le.mpr (show sourceHeader+14≤lim.space by omega)).trans hw
    exact_mod_cast hh
  have hctrWord : (ctr : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (show ctr≤lim.space by omega)).trans hw
  have hsourceNat : ((sourceHeader : ℤ)+14).toNat=sourceHeader+14 := by omega
  light_set (ctr : ℕ) using hheader',hctrRead,hsourceNat
  have paramsν : Seg ν params (LightParameterInit.values n) :=
    hparameters.of_kept hkeepPrelude (by change params+19≤free; exact hparams)
  have hScan := LightReportingWantedScanStored.program_meets_of_radix H hx hn.radix
    (ThreeSumFastResourcesColor.scan_of_stored H hn.positive hok)
  have hWanted := ThreeSumFastResources.color_program_meets H paramsν hparams hn.positive hok hScan
  have hWantedTime := hWanted.mono_time
    (Nat.add_le_add_right (ThreeSumWantedHostCosts.physical_scan_time_le H.encoded hn hx) 4000)
  have hWantedCall := (ReportingHostRelocation.meets hWantedTime
    LightEncodedColorReportingPipeline.program).append [body 354 508]
  light_call hWantedCall using hheader',sourceHeader,ctr with result ξ ⟨hbool,hresult,_,hkeepScan⟩
  have hwitness := ThreeSumWantedHostDecision.accepted_iff_witness H.encoded hn hx
  have hkept := EncodedColorWantedConsumerData.kept_counter hkeepScan
  have hp := (prefix_le_report free n A B C hsA hsB hsC).1
  have hc := report_le_counter free n A B C hsA hsB hsC
  exact ⟨hbool,hresult.trans hwitness,fun a ha =>
    (hkept a (by change a<counter free n A B C hsA hsB hsC; omega)).trans (hkeepPrelude a ha)⟩

end ThreeSum.LightThreeSumColor
