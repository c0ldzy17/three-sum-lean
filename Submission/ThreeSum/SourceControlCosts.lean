import Submission.ThreeSum.LightSourceControlsHostProgram

/-! # Finite cost of computed source controls and their full host -/

namespace ThreeSum.SourceControlCosts

open Scales TrimScales StageBounds CostLedger BandScales

def factor (h J : ℕ) : ℕ :=
  1400*(J*(512*h)+1)^2+20*J+
    14*Nat.log 2 ((512*h)*LocalCoverBounds.localPrime h+1)+
    14*Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+2044

theorem time_bound (h J : ℕ) : LightSourceControls.time h J ≤ factor h J := by
  have hd := LightDownsetSize.time_bound (J*(512*h))
  unfold LightSourceControls.time LightNatPower.time Light.log2Time factor
  omega

theorem span_word_bound {J W K S logP logE : ℕ} (hS : 0 < S) :
    SourceControlLayout.word J W K S logP logE ≤
      9*SourceControlLayout.span J W K S logP logE+30 := by
  have hstride : SourceControlLayout.stride W K ≤ S*SourceControlLayout.stride W K :=
    Nat.le_mul_of_pos_left _ hS
  have hstridePos : 0 < SourceControlLayout.stride W K := by unfold SourceControlLayout.stride; omega
  have hScount : S ≤ S*SourceControlLayout.stride W K := Nat.le_mul_of_pos_right _ hstridePos
  have hJ : J ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_succ _).trans (le_max_right _ _)
  have hP : logP ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_add_right _ _).trans ((le_max_right _ _).trans (le_max_left _ _))
  have hE : logE ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_add_right _ _).trans ((le_max_right _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  have hquad : (W+1)^2 ≤ SourceControlLayout.scratch J W logP logE :=
    (Nat.le_add_right _ _).trans ((le_max_left _ _).trans ((le_max_left _ _).trans (le_max_left _ _)))
  unfold SourceControlLayout.word SourceControlLayout.span
  omega

theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.time NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      (LightBlockSourceCatalogProgram.factor (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)+
        2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
        factor (microHalf (inputBits n)) (blockCount (inputBits n))+5705)*encoderCount n+4859 := by
  have hs := SourceBandHostCosts.time_le_encoderCount (p := p) (U := U) (D := D) hn hNL hNR
  have hc := time_bound (microHalf (inputBits n)) (blockCount (inputBits n))
  have he : 0 < encoderCount n := hn.trans_le (SourceBandCosts.input_le_encoderCount n)
  have hm := Nat.le_mul_of_pos_right
    (factor (microHalf (inputBits n)) (blockCount (inputBits n))+500) he
  unfold LightSourceControlsHost.time
  nlinarith

theorem finish_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.finish base NL NR (bandSize n)
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n)*encoderCount n+17 := by
  have hs := SourceBandHostCosts.finish_le_encoderCount (base := base+3) hn hNL hNR
  unfold LightSourceControlsHost.finish LightSourceControlsHost.sourceBase
  omega

theorem space_le_encoderCount {base NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceControlsHost.space base NL NR (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U D ≤
      base+(29+blockCount (inputBits n)+SourceBandBanksCosts.storageFactor n+
          (256*mu n+1)^2+(256*mu n+1))*encoderCount n+
        Nat.log 2 (scheduleCount n+1)+
        max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2)+19 := by
  have hs := SourceBandHostCosts.space_le_encoderCount (base := base+3) (p := p) (U := U) (D := D) hn hNL hNR
  have he : 0 < encoderCount n := hn.trans_le (SourceBandCosts.input_le_encoderCount n)
  have hp := Nat.le_mul_of_pos_right ((256*mu n+1)^2+(256*mu n+1)) he
  have hlog : 0 ≤ Nat.log 2 (scheduleCount n+1) := Nat.zero_le _
  have hlogs : 0 ≤ max (Nat.log 2 (U+1)+2) (Nat.log 2 (p+D+1)+2) := Nat.zero_le _
  unfold LightSourceControlsHost.space LightSourceControlsHost.sourceBase
  apply max_le
  · unfold LightSourceControls.space LightPascal.tableSize
    rw [BlockSourceSharing.width_eq]
    nlinarith
  · nlinarith

end ThreeSum.SourceControlCosts
