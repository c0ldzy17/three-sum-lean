import Submission.ThreeSum.EncodedColorPipelineRetention
import Submission.ThreeSum.ThreeSumColorBudgets
import Submission.ThreeSum.SharedReportingBankResourceBoundsHost

/-! # Exact retained addresses for reporting one encoded original color -/

namespace ThreeSum.ThreeSumReportingSetupData

open Light Scales BandScales EncodedColorNormalizedData

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

def reportBase (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  EncodedColorPipelineData.finish free n A B C hsA hsB hsC+8

def counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  SharedReportingBankHeader.finish (reportBase free n A B C hsA hsB hsC)
    (microHalf (inputBits n)) (blockCount (inputBits n)) B.length C.length (bandSize n)

def shift (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℤ :=
  RawAKeyLists.selected (radix n) (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (incidences n A B C hsA hsB hsC) (microHalf (inputBits n)) (blockCount (inputBits n))

def Catalog (μ : ℕ → ℤ) (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop :=
  SharedReportingBankHeader.Stored μ (reportBase free n A B C hsA hsB hsC)
    (microHalf (inputBits n)) (blockCount (inputBits n)) B.length C.length (bandSize n)
    (fun j => B.getD j 0) (fun j => C.getD j 0)
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC) (shift n A B C hsA hsB hsC)

structure Stored (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1))
    (x : Fin n → ℤ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : Prop where
  encoded : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC
  catalog : Catalog μ free n A B C hsA hsB hsC
  dense : LightDenseSetup.Stored μ (counter free n A B C hsA hsB hsC)
    (GlobalEncoding.representationCap (microHalf (inputBits n)) (blockCount (inputBits n)))
    (ThreeSumColorBudgets.falseScore n A B C hsA hsB hsC)

theorem report_le_counter (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    reportBase free n A B C hsA hsB hsC+9 ≤ counter free n A B C hsA hsB hsC :=
  (SharedReportingBankHeader.records_le_payload ..).trans
    (SharedReportingBankHeader.payload_le_finish ..)

theorem prefix_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    free+8 ≤ reportBase free n A B C hsA hsB hsC ∧
    EncodedColorPipelineData.coverBase free n ≤ reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,hf,hc,_,hs,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  unfold reportBase
  omega

theorem cover_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightCoverKeyData.keyEnd (EncodedColorPipelineData.coverBase free n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ reportBase free n A B C hsA hsB hsC := by
  obtain ⟨_,_,_,hw,hs,_⟩ := EncodedColorPipelineData.ordered free n A B C hsA hsB hsC
  have he : EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length=
      LightCoverKeyData.keyEnd (EncodedColorPipelineData.coverBase free n)
        (microHalf (inputBits n)) (blockCount (inputBits n))+3*(incidences n A B C hsA hsB hsC).length := rfl
  unfold reportBase
  omega

theorem pool_end_le_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    EncodedColorPrimeData.poolBase (EncodedColorLayout.prime free n (bandSize n))+
      LightPrimePool.size (primeWindow n) ≤ reportBase free n A B C hsA hsB hsC := by
  have hp := (prefix_le_report free n A B C hsA hsB hsC).2
  have hs := LightPrimePool.size_le (primeWindow n)
  unfold EncodedColorPipelineData.coverBase EncodedColorLayout.cover
    EncodedColorPrimeData.nextFree EncodedColorPrimeData.prefixBase at hp
  omega

end ThreeSum.ThreeSumReportingSetupData
