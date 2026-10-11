import Submission.ThreeSum.LightThreeSumReportingSetupBank
import Submission.ThreeSum.LightThreeSumReportingSetupDense

/-!
# Execute both reporting preparations from the original encoded-color payload

The shared catalog bank is constructed once. Its returned free pointer is
passed directly to dense initialization, which reads the original arrays,
actual candidate records, selected modulus and prime pool from memory.
-/

namespace ThreeSum.LightThreeSumReportingSetup

open Light Scales BandScales ArithmeticStageBounds ThreeSumReportingSetupData

set_option maxHeartbeats 1800000
set_option maxRecDepth 15000

def body (pBank pDense : ℕ) : Stmt :=
  .call pBank [v 0,v 1,v 2,v 3] 4 ;;
  .call pDense [v 0,v 1,v 2,v 3,v 4] 0

def joined : Program := ReportingHostRelocation.program
  LightThreeSumReportingSetupBank.program LightThreeSumReportingSetupDense.program

def program : Program := joined++[body 75 96]

theorem program_length : program.length=98 := rfl

def time (n U R : ℕ) : ℕ := LightThreeSumReportingSetupBank.time n+
  LightThreeSumReportingSetupDense.time n U R+200

theorem program_meets {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hR : 4 ≤ radix n)
    (hbank : (SharedReportingBankResourceBounds.need n U).Ok lim
      (reportBase free n A B C hsA hsB hsC) (d+2))
    (hspace : LightWeightedScore.space (counter free n A B C hsA hsB hsC+4)
      (maxMod n) (bandSize n) U ≤ lim.space)
    (hword : (LightThreeSumReportingSetupDense.word n U : ℤ) ≤ lim.word)
    (hdepth : d+Nat.clog 2 (maxMod n)+9 ≤ lim.depth)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 97 d
      [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC] μ
      (time n U (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length)
      (fun r ν => r=(counter free n A B C hsA hsB hsC : ℤ) ∧
        ThreeSumReportingSetupData.Stored ν free n color x A B C hsA hsB hsC ∧
        Kept μ ν (reportBase free n A B C hsA hsB hsC)) := by
  let out := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let report := reportBase free n A B C hsA hsB hsC
  let ctr := counter free n A B C hsA hsB hsC
  let rs := BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC
  have hw := hbank.space
  have hctr : ctr+4 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change ctr+4+(Nat.log 2 (maxMod n+1)+2) ≤ lim.space at hh
    omega
  have hr := report_le_counter free n A B C hsA hsB hsC
  change report+9 ≤ ctr at hr
  have hf := (prefix_le_report free n A B C hsA hsB hsC).1
  change free+8 ≤ report at hf
  have ho : out+8=report := rfl
  have hnWord : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show n ≤ LightThreeSumReportingSetupDense.word n U by
      unfold LightThreeSumReportingSetupDense.word; omega)).trans hword
  change Meets lim program 97 d [n,params,free,out] μ (time n U rs.length) _
  apply Meets.of_body (p := 97) (by rfl : program[97]?=some (body 75 96))
  unfold body time
  have hBank := ((LightThreeSumReportingSetupBank.program_meets (d := d+1) (μ := μ)
    H Hparams hparams (by simpa only [Nat.add_assoc] using hbank)).append
      (LightThreeSumReportingSetupDense.program.map (ReportingHostRelocation.relocate 76))).append [body 75 96]
  light_call hBank using LightThreeSumReportingSetupBank.time,LightThreeSumReportingSetupDense.time
    with result μ₁ ⟨hresult,H₁,catalog₁,keepBank⟩
  have hresult' : result=(ctr : ℤ) := hresult
  have params₁ : Seg μ₁ params (LightParameterInit.values n) := Hparams.of_kept keepBank (by
    simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,
      LightLocalCounts.values,LightGlobalSizes.values] using (show params+19 ≤ report by omega))
  have hDense := (ReportingHostRelocation.meets
    (LightThreeSumReportingSetupDense.program_meets (d := d+1) (μ := μ₁) (dst := ctr)
      H₁ params₁ hparams hw hR (by omega) hspace hword (by omega) hx)
      LightThreeSumReportingSetupBank.program).append [body 75 96]
  light_call hDense using hresult',LightThreeSumReportingSetupBank.time,LightThreeSumReportingSetupDense.time,rs
    with final ν ⟨hfinal,dense₂,H₂,keepDense⟩
  have catalog₂ : Catalog ν free n A B C hsA hsB hsC :=
    SharedReportingBankHeader.Stored.of_kept catalog₁ keepDense le_rfl
  exact ⟨hfinal,⟨H₂,catalog₂,dense₂⟩,fun i hi => (keepDense i (by omega)).trans (keepBank i hi)⟩

end ThreeSum.LightThreeSumReportingSetup
