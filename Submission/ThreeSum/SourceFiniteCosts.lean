import Submission.ThreeSum.SourceControlCosts

/-! # Uniform original-size budgets for the finite normalized source host -/

namespace ThreeSum.SourceFiniteCosts

open Scales TrimScales StageBounds CostLedger BandScales

def time (n p U D : ℕ) : ℕ :=
  (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
    2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
    SourceControlCosts.factor (microHalf (inputBits n)) (blockCount (inputBits n))+5705)*encoderCount n+4859

def space (base n p U D : ℕ) : ℕ :=
  base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n+
      (256*mu n+1)^2+(256*mu n+1))*encoderCount n+
    Nat.log 2 (scheduleCount n+1)+
    max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19

def finish (base n : ℕ) : ℕ :=
  base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17

def word (n p U D : ℕ) : ℕ :=
  LightSourceControlsHost.word n n (bandSize n) p
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D

theorem word_mono {NL NR NL' NR' g p h J cut U D : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightSourceControlsHost.word NL NR g p h J cut U D ≤
      LightSourceControlsHost.word NL' NR' g p h J cut U D := by
  have hs := SourceBandBankLayout.word_mono (h := h) (J := J) hl hr
  unfold LightSourceControlsHost.word LightSourceBandHost.word LightSourceBandPair.word
    LightSourceBandStep.word LightSourceBandBanks.word LightSourceBandBankStep.word
  omega

theorem time_le {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ time n p U D :=
  SourceControlCosts.time_le_encoderCount hn hNL hNR

theorem space_le {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ space base n p U D :=
  SourceControlCosts.space_le_encoderCount hn hNL hNR

theorem finish_le {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤ finish base n :=
  SourceControlCosts.finish_le_encoderCount hn hNL hNR

theorem word_le {NL NR n p U D : ℕ} (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.word NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤ word n p U D :=
  word_mono hNL hNR

end ThreeSum.SourceFiniteCosts
