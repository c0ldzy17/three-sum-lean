import Submission.ThreeSum.ThreeSumReportingSetupData
import Submission.ThreeSum.LightReportingWantedScan

/-! # The wanted consumer's configuration from the actual retained color payload -/

namespace ThreeSum.ThreeSumWantedHostData

open Light Scales BandScales ThreeSumReportingSetupData EncodedColorNormalizedData

local instance (n : ℕ) : NeZero (radix n) := ⟨Nat.ne_of_gt (radix_pos n)⟩

def recordCount (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length

def count (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  WantedResidueKeys.total (radix n)
    (LightGuardedWanted.left (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
      (incidences n A B C hsA hsB hsC))
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (shift n A B C hsA hsB hsC)

def config (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    LightReportingWantedDispatch.Config where
  layoutHeader := counter free n A B C hsA hsB hsC+4
  J := blockCount (inputBits n)
  h := microHalf (inputBits n)
  K := LightSwitchDepth.depth (blockCount (inputBits n))
  N := (incidences n A B C hsA hsB hsC).length
  NB := B.length
  NC := C.length
  cover := EncodedColorPipelineData.coverBase free n
  counter := counter free n A B C hsA hsB hsC
  pairs := LightWantedSetup.pairBase
    (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)
    (3*(incidences n A B C hsA hsB hsC).length)
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n))) (radix n)
  layerCount := OutputDecodeRecords.layerCount (microHalf (inputBits n))
  scheduleSize := GlobalEncoding.scheduleSize (microHalf (inputBits n))
  masks := LightCoverKeys.afterCover (EncodedColorPipelineData.coverBase free n) (microHalf (inputBits n))
  vals := EncodedColorLayout.vals free n (bandSize n)
  owners := LightBandRawA.ownerBase (EncodedColorLayout.vals free n (bandSize n))
    (recordCount n A B C hsA hsB hsC) (bandSize n)
  records := EncodedColorLayout.rec free n (bandSize n)
  pair := EncodedColorPipelineData.controls free n A B C hsA hsB hsC+3
  bank := EncodedColorPipelineData.bankHeader free n A B C hsA hsB hsC
  srcB := EncodedColorLayout.bv free n
  srcC := EncodedColorLayout.cv free n
  report := reportBase free n A B C hsA hsB hsC
  modulus := radix n

theorem recordCount_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    recordCount n A B C hsA hsB hsC=
      BandPartition.size B.length (bandSize n)*BandPartition.size C.length (bandSize n)+
      BandPartition.size A.length (bandSize n)*BandPartition.size B.length (bandSize n)+
      BandPartition.size A.length (bandSize n)*BandPartition.size C.length (bandSize n) := by
  simp only [recordCount,BandRawA.sortedRecords,BandCandidateRows.records_length]
  rfl

theorem count_read {μ : ℕ→ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)=
      (count n A B C hsA hsB hsC : ℤ) := H.wanted.1

theorem pairs_read {μ : ℕ→ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length+1)=
      ((config free n A B C hsA hsB hsC).pairs : ℤ) := H.wanted.2.1

end ThreeSum.ThreeSumWantedHostData
