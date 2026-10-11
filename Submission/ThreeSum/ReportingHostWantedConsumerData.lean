import Submission.ThreeSum.EncodedColorWantedConsumerRetention
import Submission.ThreeSum.ReportingHostWantedDecision
import Submission.ThreeSum.LightReportingWantedRecordNeed

/-! # Physical labels and original-fiber semantics for the retained consumer -/

namespace ThreeSum.ReportingHostWantedConsumerData

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedOriginal ReportingHostWantedPhysical SharedReportingBankResourceBounds
open ReportingHostFrontierLayout

set_option maxHeartbeats 2300000
set_option maxRecDepth 16000

theorem cut_eq_mu (n : ℕ) : LightBlockQuery.sourceCut (half n) (blocks n)=mu n := by
  unfold LightBlockQuery.sourceCut half blocks mu totalSize microSize microHalf
  ring

theorem depth_le_blocks (n : ℕ) : LightSwitchDepth.depth (blocks n)≤blocks n := by
  unfold LightSwitchDepth.depth
  omega

abbrev Label (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :=
  Wanted (half n) (blocks n) (AType A.length (bandSize n) (records n A B C hsA hsB hsC))

def fiber (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) :=
  localItems (half n) (blocks n) A.length B.length C.length (bandSize n)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (records n A B C hsA hsB hsC)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w

def labelMass (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) : ℕ := rootMass (fiber n A B C hsA hsB hsC w) w

def labelHit (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) : Prop :=
  Terminal (half n) (blocks n) A.length B.length C.length (bandSize n)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (records n A B C hsA hsB hsC)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) w (LightSwitchDepth.depth (blocks n))

def recordTime (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (w : Label n A B C hsA hsB hsC) (output old threshold : ℕ) : ℕ :=
  LightReportingWanted.time (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC)
    (left (records n A B C hsA hsB hsC) (fun j => B.getD j 0) w)
    (right (records n A B C hsA hsB hsC) (fun j => C.getD j 0) w)
    (leftCount (records n A B C hsA hsB hsC) B.length w)
    (rightCount (records n A B C hsA hsB hsC) C.length w) old threshold
    (fiber n A B C hsA hsB hsC w) w
    (ReportingHostWantedRecordData.catalogs A.length B.length C.length (bandSize n)
      (config free n A B C hsA hsB hsC).report (half n) (blocks n)
      (records n A B C hsA hsB hsC) w output) (LightSwitchDepth.depth (blocks n))

def rawIndex (μ : ℕ→ℤ) (cfg : LightReportingWantedDispatch.Config) (slot : ℕ) : ℕ :=
  (μ (cfg.pairs+2*slot)).toNat

def outputIndex (μ : ℕ→ℤ) (cfg : LightReportingWantedDispatch.Config) (slot : ℕ) : ℕ :=
  (μ (cfg.pairs+2*slot+1)).toNat

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

def slot (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    Fin (μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)).toNat :=
  ⟨s.val,by rw [count_read H,Int.toNat_natCast]; exact s.isLt⟩

def label (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) : Label n A B C hsA hsB hsC :=
  wantedAt H.wanted (slot H s)

theorem label_position (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    (label H s).1.val=rawIndex μ (config free n A B C hsA hsB hsC) s.val %
      (config free n A B C hsA hsB hsC).N := by
  have hh := wantedAt_position H.wanted (slot H s)
  calc
    (label H s).1.val = _ := hh
    _ = _ := by
      simp only [slot,rawIndex,DenseGuardWanted.leftIndex,config,incidences,values_length]

theorem label_output (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    (label H s).2.2=LightOutputDecodeOriginal.output (half n) (blocks n)
      (outputIndex μ (config free n A B C hsA hsB hsC) s.val) := by
  have hh := wantedAt_output H.wanted (slot H s)
  calc
    (label H s).2.2 = _ := hh
    _ = _ := by
      simp only [slot,outputIndex,DenseGuardWanted.rightIndex,config,incidences,values_length,half,blocks]

theorem slot_indices (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    rawIndex μ (config free n A B C hsA hsB hsC) s.val<3*(config free n A B C hsA hsB hsC).N ∧
      outputIndex μ (config free n A B C hsA hsB hsC) s.val<OutputDecodeRecords.localCount (half n)^blocks n := by
  exact DenseGuardWanted.output_bounds H.wanted (slot H s).isLt

theorem slot_reads (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    let cfg := config free n A B C hsA hsB hsC
    μ (cfg.pairs+2*s.val)=(rawIndex μ cfg s.val : ℤ) ∧
      μ (cfg.pairs+2*s.val+1)=(outputIndex μ cfg s.val : ℤ) := by
  obtain ⟨i,j,_,_,hi,hj,_⟩ := WantedRecordCoverage.output_pair H.wanted (slot H s).isLt
  change μ ((config free n A B C hsA hsB hsC).pairs+2*s.val)=(i : ℤ) at hi
  change μ ((config free n A B C hsA hsB hsC).pairs+2*s.val+1)=(j : ℤ) at hj
  simp [rawIndex,outputIndex,hi,hj]

theorem label_key (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (s : Fin (count n A B C hsA hsB hsC)) :
    globalModulus (half n) (blocks n) ∣
      valueAt A.length (bandSize n) (records n A B C hsA hsB hsC) (fun j => A.getD j 0) (label H s).1.val %
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      lift (label H s).2.1*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-globalKey (label H s).2.2 := by
  have hm : globalModulus (half n) (blocks n)=(radix n : ℤ) := by
    simp only [globalModulus,Scales.radix,Scales.localRadix,Nat.cast_pow,half,blocks]
  rw [hm]
  exact wantedAt_key H.wanted (slot H s)

end ThreeSum.ReportingHostWantedConsumerData
