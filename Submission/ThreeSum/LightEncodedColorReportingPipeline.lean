import Submission.ThreeSum.LightThreeSumReportingSetupBounded
import Submission.ThreeSum.EncodedColorReportingResources
import Submission.ThreeSum.EncodedColorReportingCosts

/-!
# Original selected color through the shared reporting and dense prelude

The literal355-procedure program runs the existing source pipeline and then
the reporting setup. It returns the original source header; all normalized
lists and occurrence-shared catalogs are retained in the same payload.
-/

namespace ThreeSum.LightEncodedColorReportingPipeline

open Light Scales BandScales ThreeSumReportingSetupData EncodedColorNormalizedData

set_option maxHeartbeats 2600000
set_option maxRecDepth 17000

/-- Original array, length, parameter header, selected color row, free address. -/
def body (pSource pReporting : ℕ) : Stmt :=
  .call pSource [v 0,v 1,v 2,v 3,v 4] 5 ;;
  .call pReporting [v 1,v 2,v 4,v 5] 6 ;;
  .set 0 (v 5)

def joined : Program := ReportingHostRelocation.program
  LightEncodedColorPipeline.program LightThreeSumReportingSetup.program

def program : Program := joined++[body 255 353]

theorem program_length : program.length=355 := rfl

def time (n U : ℕ) : ℕ := EncodedColorReportingCosts.time n U

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {src n params row free U d : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hok : (EncodedColorReportingResources.need n U).Ok lim free d)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 354 d [src,n,params,row,free] μ (time n U)
      (fun r ν => EncodedColorReportingData.Output ν free n color x r ∧ Kept μ ν free) := by
  have sourceNeed := EncodedColorReportingResources.source_of_ok hok
  have hw := hok.space
  have hd : d < lim.depth := by have hh := sourceNeed.depth; omega
  have hfreeSpace : free ≤ lim.space := by have hh := hok.cells; omega
  apply Meets.of_body (p := 354) (by rfl : program[354]?=some (body 255 353))
  unfold body time EncodedColorReportingCosts.time
  have hSource := ((EncodedColorResources.program_meets (d := d+1) (μ := μ)
    color x hn hR hsrc hparams hrow sourceNeed hread hbound hparameters hcolor).append
      (LightThreeSumReportingSetup.program.map (ReportingHostRelocation.relocate 256))).append [body 255 353]
  light_call hSource with out μ₁ ⟨source₁,keepSource⟩
  obtain ⟨A,hsA,B,hsB,C,hsC,hout,encoded₁⟩ := source₁
  let header := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let report := reportBase free n A B C hsA hsB hsC
  let rs := BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
  have hout' : out=(header : ℤ) := hout
  have hreport := EncodedColorReportingData.report_le_source_allocation encoded₁ hn U
  change report ≤ free+(EncodedColorResources.need n U).cells at hreport
  have hreportSpace : report ≤ lim.space := hreport.trans sourceNeed.cells
  have hheader : header+8=report := rfl
  have hheaderWord : (header : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show header ≤ lim.space by omega)).trans hw
  have hprefix := (prefix_le_report free n A B C hsA hsB hsC).1
  change free+8 ≤ report at hprefix
  have setupNeed := EncodedColorReportingResources.setup_of_ok hok hreport
  have params₁ : Seg μ₁ params (LightParameterInit.values n) := hparameters.of_kept keepSource (by
    simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,
      LightLocalCounts.values,LightGlobalSizes.values] using hparams)
  obtain ⟨ha,hb,hc⟩ := ThreeSumColorBudgets.normalized_lengths encoded₁
  have hcount : rs.length ≤ ColorBandBounds.count n (bandSize n) :=
    EncodedColorNormalizedData.records_length_le ha hb hc
  have hSetup := (ReportingHostRelocation.meets
    (ThreeSumReportingSetupResources.program_meets (d := d+1) (μ := μ₁)
      encoded₁ params₁ hparams hR hbound setupNeed) LightEncodedColorPipeline.program).append [body 255 353]
  have hSetupTime : LightThreeSumReportingSetup.time n U rs.length ≤ EncodedColorReportingCosts.setupTime n U :=
    EncodedColorReportingCosts.setup_time_le hcount
  have hSetupBound := hSetup.mono_time hSetupTime
  light_call hSetupBound using hout',rs with ctr ν ⟨hctr,stored,keepSetup⟩
  light_set (header : ℕ) using hout'
  exact ⟨⟨A,hsA,B,hsB,C,hsC,rfl,stored⟩,
    fun i hi => (keepSetup i (by change i < report; omega)).trans (keepSource i hi)⟩

end ThreeSum.LightEncodedColorReportingPipeline
