import Submission.ThreeSum.LightSourceBandHostProgram
import Submission.ThreeSum.SourceBandBanksCosts

/-! # Finite resource charge of the actual original-array source host -/

namespace ThreeSum.SourceBandHostCosts

open Scales TrimScales StageBounds CostLedger BandScales

theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+5205)*encoderCount n+4859 := by
  have hp := SourceBandPairCosts.time_le_encoderCount (p := p) (U := U) (D := D) hn hNL hNR
  have hb := SourceBandBanksCosts.time_le_encoderCount hn hNL hNR
  unfold LightSourceBandHost.time
  nlinarith

theorem scheduleCount_le_encoderCount {n : ℕ} (hn : 0 < n) : scheduleCount n ≤ encoderCount n := by
  have hf : 0 < fullOutputs n :=
    (typedOutputs_pos n).trans_le (SourceBandCosts.typedOutputs_le_fullOutputs n)
  have hs : scheduleCount n ≤ tableCount n := Nat.le_mul_of_pos_right _ hf
  exact hs.trans (SourceBandPairCosts.tableCount_le_encoderCount hn)

theorem occurrenceRows_le_encoderCount {n : ℕ} (hn : 0 < n) :
    LightBlockSourceCatalog.count (microHalf (inputBits n)) (blockCount (inputBits n))*blockCount (inputBits n) ≤
      blockCount (inputBits n)*encoderCount n := by
  rw [BlockSourceCatalogCosts.count_eq_scheduleCount]
  have h := Nat.mul_le_mul_right (blockCount (inputBits n)) (scheduleCount_le_encoderCount hn)
  simpa only [Nat.mul_comm] using h

theorem bankHeader_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) ≤
      base+(29+blockCount (inputBits n))*encoderCount n+9 := by
  have hp := SourceBandPairCosts.next_le_encoderCount (base := base) hn hNL hNR
  have hr := occurrenceRows_le_encoderCount hn
  unfold LightSourceBandHost.bankHeader LightSourceBandHost.occurrenceBase
  nlinarith

theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+14 := by
  have hh := bankHeader_le_encoderCount (base := base) hn hNL hNR
  have hb := SourceBandBanksCosts.finish_le_encoderCount
    (base := LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n))) hNL hNR
  unfold LightSourceBandHost.finish
  nlinarith

theorem space_le_encoderCount {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+
        Nat.log 2 (scheduleCount n+1)+
        max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+16 := by
  have hp := SourceBandPairCosts.next_le_encoderCount (base := base) hn hNL hNR
  have hh := bankHeader_le_encoderCount (base := base) hn hNL hNR
  have hb := SourceBandBanksCosts.space_le_encoderCount
    (base := LightSourceBandHost.bankHeader base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n))) hn hNL hNR
  unfold LightSourceBandHost.space
  apply max_le
  · unfold LightSourceBandPair.space LightSourceResidues.space
    nlinarith
  · have hm : 0 ≤ max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2) := Nat.zero_le _
    nlinarith only [hh,hb,hm]

end ThreeSum.SourceBandHostCosts
