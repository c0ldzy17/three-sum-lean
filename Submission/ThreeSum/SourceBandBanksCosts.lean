import Submission.ThreeSum.LightSourceBandBanksProgram
import Submission.ThreeSum.SourceBandPairCosts

/-! # Exact shared construction counts and finite encoder charge -/

namespace ThreeSum.SourceBandBanksCosts

open Scales TrimScales StageBounds CostLedger BandScales SubsetAddress

def familyCount (NL NR g h J : ℕ) : ℕ :=
  2*SourceBandPairSlices.count NL NR g*LightBlockSourceCatalog.count h J

def stageCells (NL NR g h J cut : ℕ) : ℕ :=
  familyCount NL NR g h J*LightBlockSourceBatchLayout.family (J*(512*h)) cut

theorem stageCells_eq (NL NR g h J cut : ℕ) :
    stageCells NL NR g h J cut=
      2*SourceBandPairSlices.count NL NR g*LightBlockSourceCatalog.count h J*
        (J*(512*h)+1)*downsetCap (J*(512*h)) cut := by
  unfold stageCells familyCount LightBlockSourceBatchLayout.family
  ring

theorem count_le_bandCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandPairSlices.count NL NR (bandSize n) ≤ bandCount n :=
  max_le (SourceBandCosts.size_le_bandCount hNL) (SourceBandCosts.size_le_bandCount hNR)

theorem familyCount_le {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    familyCount NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      2*bandCount n*scheduleCount n := by
  unfold familyCount
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount]
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 (count_le_bandCount hNL hNR))

theorem stageCells_le_encoderCount {NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    stageCells NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      (256*mu n+1)*(mu n+1)*encoderCount n := by
  have hf := familyCount_le hNL hNR
  unfold stageCells
  rw [BlockSourceSharing.width_eq]
  have hm := Nat.mul_le_mul_right (LightBlockSourceBatchLayout.family (256*mu n) (mu n)) hf
  have he : 2*bandCount n*scheduleCount n*LightBlockSourceBatchLayout.family (256*mu n) (mu n)=
      BlockSourceCatalogCosts.stageCellCount n := by
    unfold BlockSourceCatalogCosts.stageCellCount
    rw [BlockSourceCatalogCosts.stageFamilyCount_eq]
  exact (hm.trans_eq he).trans (BlockSourceCatalogCosts.stageCellCount_le_encoderCount n)

theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < bandCount n := by
  have hp := (bandCount_mul_bounds n).1
  by_contra h
  have hz : bandCount n=0 := by omega
  rw [hz,Nat.mul_zero] at hp
  omega

theorem time_le_encoderCount {NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandBanks.time NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+1300)*
        encoderCount n+1220 := by
  have hcount := count_le_bandCount hNL hNR
  have hpos := bandCount_pos hn
  have hrows := Nat.le_mul_of_pos_left
    (LightSourceOccurrenceArray.time
      (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
      (blockCount (inputBits n))) hpos
  have hbatch := Nat.mul_le_mul_right
    (LightBlockSourceBatch.time
      (LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n)))
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)) hcount
  have ht : LightSourceBandBanks.time NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      BlockSourceCatalogCosts.work n+1300*bandCount n+1220 := by
    unfold LightSourceBandBanks.time LightSourceBandBankBatch.time LightSourceBandBankStep.time
      BlockSourceCatalogCosts.work LightBlockSourceCatalog.time
    nlinarith
  have hw := BlockSourceCatalogCosts.work_le_encoderCount n
  have hb := SourceBandCosts.bands_le_encoderCount n
  nlinarith

theorem overhead_bound (h J : ℕ) : LightBlockSourceRetainedHost.space 0 h J ≤
    J+2*(J*(512*h))+(J*(512*h)+1)^2+
      Nat.log 2 ((512*h)*LocalCoverBounds.localPrime h+1)+
      Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+20 := by
  unfold LightBlockSourceRetainedHost.space LightSourcePreparation.space LightBlockSourceHashes.space
    LightSourceMaskFlags.space LightSourceRetainedStages.space LightPascal.tableSize
  omega

theorem span_eq (h J cut : ℕ) : SourceBandBankLayout.span h J cut=
    LightBlockSourceCatalog.count h J*(LightBlockSourceBatchLayout.stride (J*(512*h)) cut+2)+
      downsetCap (J*(512*h)) cut+J*(512*h)+2+LightBlockSourceRetainedHost.space 0 h J := by
  unfold SourceBandBankLayout.span
  have h := SourceBandBankLayout.host_space_add
    (LightBlockSourceBatchLayout.work 0 (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) 0 h J
  simp only [Nat.add_zero] at h
  rw [h,BlockSourceCatalogCosts.work_address]
  omega

theorem finish_eq (base NL NR g h J cut : ℕ) :
    SourceBandBankData.finish base NL NR g h J cut=
      base+5+SourceBandPairSlices.count NL NR g*SourceBandBankLayout.span h J cut := rfl

def storageFactor (n : ℕ) : ℕ :=
  (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)+mu n+256*mu n+3+
    LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))

theorem span_count_le_encoderCount {G n : ℕ} (hG : G ≤ bandCount n) :
    G*SourceBandBankLayout.span (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      storageFactor n*encoderCount n := by
  have hslot : G*scheduleCount n*(LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2) ≤
      (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*encoderCount n := by
    apply le_trans (b := BlockSourceCatalogCosts.catalogCells n)
    · calc
        _ ≤ bandCount n*scheduleCount n*(LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2) :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hG)
        _ ≤ bandCount n*scheduleCount n*(blockCount (inputBits n)+LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2) :=
          Nat.mul_le_mul_left _ (by omega)
        _ = _ := rfl
    · exact BlockSourceCatalogCosts.catalogCells_le_encoderCount n
  have hGF : G*fullOutputs n ≤ encoderCount n :=
    (Nat.mul_le_mul_right _ hG).trans (SourceBandCosts.bands_outputs_le_encoderCount n)
  have hGK : G*downsetCap (256*mu n) (mu n) ≤ (mu n+1)*encoderCount n := by
    calc
      _ ≤ G*((mu n+1)*fullOutputs n) := Nat.mul_le_mul_left _ (BlockSourceSharing.downset_le_fullOutputs n)
      _ = (mu n+1)*(G*fullOutputs n) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hGF
  have hGE := hG.trans (SourceBandCosts.bands_le_encoderCount n)
  have hother := Nat.mul_le_mul_right
    (256*mu n+2+LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))) hGE
  calc
    _ = G*scheduleCount n*(LightBlockSourceBatchLayout.stride (256*mu n) (mu n)+2)+
        G*downsetCap (256*mu n) (mu n)+
        G*(256*mu n+2+LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))) := by
      rw [span_eq,BlockSourceCatalogCosts.count_eq_scheduleCount,BlockSourceSharing.width_eq]
      ring
    _ ≤ (blockCount (inputBits n)+2*(256*mu n)+7)*(256*mu n+2)*encoderCount n+
        (mu n+1)*encoderCount n+
        encoderCount n*(256*mu n+2+LightBlockSourceRetainedHost.space 0 (microHalf (inputBits n)) (blockCount (inputBits n))) :=
      Nat.add_le_add (Nat.add_le_add hslot hGK) hother
    _ = _ := by unfold storageFactor; ring

theorem finish_le_encoderCount {base NL NR n : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    SourceBandBankData.finish base NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+5+storageFactor n*encoderCount n := by
  rw [finish_eq]
  exact Nat.add_le_add_left (span_count_le_encoderCount (count_le_bandCount hNL hNR)) _

theorem space_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandBanks.space base NL NR (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+storageFactor n*encoderCount n+Nat.log 2 (scheduleCount n+1)+7 := by
  have hf := finish_le_encoderCount (base := base) hNL hNR
  have hs := span_count_le_encoderCount (G := 1) (show 1 ≤ bandCount n from bandCount_pos hn)
  simp only [Nat.one_mul] at hs
  unfold LightSourceBandBanks.space LightOutputDecodeDigits.space
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount]
  omega

end ThreeSum.SourceBandBanksCosts
