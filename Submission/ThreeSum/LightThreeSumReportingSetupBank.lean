import Submission.ThreeSum.ThreeSumReportingSetupData

/-! # Run shared reporting precomputation from the encoded color header -/

namespace ThreeSum.LightThreeSumReportingSetupBank

open Light Scales BandScales ThreeSumReportingSetupData

set_option maxHeartbeats 2100000
set_option maxRecDepth 14000

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

/-- Input length, parameter header, normalized header, encoded result header. -/
def body (pBank : ℕ) : Stmt :=
  .set 4 (M (v 1 +' k 1)) ;;
  .set 5 (M (v 1 +' k 3)) ;;
  .set 6 (M (v 3 +' k 3)) ;;
  .set 7 (v 6 +' k 3) ;;
  .set 8 (M (v 3 +' k 4)) ;;
  .set 9 (M (v 3 +' k 5)) ;;
  .call pBank [v 4,v 5,v 6,v 7,v 8,v 9] 0

def program : Program := LightSharedReportingHost.program++[body 74]

theorem program_length : program.length=76 := rfl

def time (n : ℕ) : ℕ := SharedReportingBankCosts.budget n+400

theorem program_meets {lim : Limits} {d : ℕ} {μ : ℕ → ℤ} {free n params U : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (Hparams : Seg μ params (LightParameterInit.values n)) (hparams : params+19 ≤ free)
    (hok : (SharedReportingBankResourceBounds.need n U).Ok lim
      (reportBase free n A B C hsA hsB hsC) (d+1)) :
    Meets lim program 75 d [n,params,free,EncodedColorPipelineData.finish free n A B C hsA hsB hsC]
      μ (time n) (fun r ν => r=(counter free n A B C hsA hsB hsC : ℤ) ∧
        EncodedColorPipelineData.Stored ν free n color x A B C hsA hsB hsC ∧
        Catalog ν free n A B C hsA hsB hsC ∧ Kept μ ν (reportBase free n A B C hsA hsB hsC)) := by
  let out := EncodedColorPipelineData.finish free n A B C hsA hsB hsC
  let report := reportBase free n A B C hsA hsB hsC
  let control := EncodedColorPipelineData.controls free n A B C hsA hsB hsC
  let pair := LightSourceControlsHost.sourceBase control
  let bank := EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  let h := microHalf (inputBits n)
  let J := blockCount (inputBits n)
  obtain ⟨_,hB,hC⟩ := ThreeSumColorBudgets.normalized_lengths H
  have R := SharedReportingBankResourceBounds.resources_of_ok hB hC hok
  have hw := hok.space
  have hd : d < lim.depth := by have hh := hok.depth; omega
  have hreport : report+9 ≤ lim.space := by
    have hh := (le_max_left _ _).trans R.space
    change report+9+LightPascal.tableSize (512*h) ≤ lim.space at hh
    omega
  have hprefix := (prefix_le_report free n A B C hsA hsB hsC).1
  change free+8 ≤ report at hprefix
  obtain ⟨_,_,_,_,hcontrol,hbank⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  change control+3 ≤ out at hcontrol
  change bank+5 ≤ out at hbank
  have hpairs := SourceBandPairData.ordered pair B.length C.length (bandSize n) (BlockSourceEncoding.modulus h J)
  obtain ⟨_,hpairEnd,_⟩ := SourceFiniteData.source_ends control B.length C.length (bandSize n) h J (mu n)
  change SourceBandPairData.next pair B.length C.length (bandSize n) (BlockSourceEncoding.modulus h J) ≤ out at hpairEnd
  have hpair : pair+8 ≤ out := by
    unfold SourceBandPairData.leftBase at hpairs
    omega
  have hHWord : (h : ℤ) ≤ lim.word := by
    have hh : h ≤ 2^(512*h+1) :=
      (Nat.lt_two_pow_self (n := h)).le.trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (Int.ofNat_le.mpr hh).trans R.powers
  have hJWord : (J : ℤ) ≤ lim.word := by
    apply (Int.ofNat_le.mpr (show J ≤ LightSwitchDepth.word J by unfold LightSwitchDepth.word; omega)).trans R.depthWord
  have hcut : 2*h*J=mu n := BlockSourceSharing.cutoff_eq n
  have controls := H.sources.controls
  have banks := H.sources.banks
  rw [← hcut] at controls banks
  obtain ⟨_,_,_,readControl,readBank,readReport,_,_⟩ := H.heads_read
  change μ (out+3)=(control : ℤ) at readControl
  change μ (out+4)=(bank : ℤ) at readBank
  change μ (out+5)=(report : ℤ) at readReport
  obtain ⟨_,readH,readJ,_,_,_,_⟩ := EncodedColorParameterData.reads Hparams
  change μ (params+1)=(h : ℤ) at readH
  change μ (params+3)=(J : ℤ) at readJ
  have par1 : ((params : ℤ)+1).toNat=params+1 := by omega
  have par3 : ((params : ℤ)+3).toNat=params+3 := by omega
  have out3 : ((out : ℤ)+3).toNat=out+3 := by omega
  have out4 : ((out : ℤ)+4).toNat=out+4 := by omega
  have out5 : ((out : ℤ)+5).toNat=out+5 := by omega
  have outReport : out+8=report := rfl
  change Meets lim program 75 d [n,params,free,out] μ (time n) _
  apply Meets.of_body (p := 75) (by rfl : program[75]?=some (body 74))
  unfold body time
  light_set (h : ℕ) using readH,par1
  light_set (J : ℕ) using readJ,par3
  light_set (control : ℕ) using readControl,out3
  light_set (pair : ℕ) using LightSourceControlsHost.sourceBase,pair
  light_set (bank : ℕ) using readBank,out4
  light_set (report : ℕ) using readReport,out5
  have hcall := (SharedReportingBankResourceBounds.program_meets (d := d+1) (μ := μ)
    (controls := control) (pairHeader := pair) (bankHeader := bank) (free := report)
    hB hC controls H.sources.buckets banks (by omega) (by omega) le_rfl
    (by change SourceBandBankData.finish bank B.length C.length (bandSize n) h J (2*h*J) ≤ report
        rw [hcut]
        change out ≤ report
        omega) hok).append [body 74]
  light_call hcall using SharedReportingBankResourceBounds.half,SharedReportingBankResourceBounds.blocks,h,J
    with result ν ⟨hresult,hcatalog,hkeep⟩
  exact ⟨hresult,H.of_kept hkeep le_rfl,hcatalog,hkeep⟩

end ThreeSum.LightThreeSumReportingSetupBank
