import Submission.ThreeSum.LightSourceBandPair

/-! # Finite cost of both actual original-band catalogs and empty padding -/

namespace ThreeSum.SourceBandPairCosts

open Scales TrimScales StageBounds CostLedger BandScales SourceBandPairData

theorem time_bound (NL NR g p m U D : ℕ) (hg : 0 < g) :
    LightSourceBandPair.time NL NR g p m U D ≤
      1016*(NL+NR)*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+
      (BandPartition.size NL g+BandPartition.size NR g)*(233*m+1713)+13*m+3139 := by
  have hl := LightSourceBandSetup.time_bound NL g p m U D hg
  have hr := LightSourceBandSetup.time_bound NR g p m U D hg
  unfold LightSourceBandPair.time Light.fillTime
  nlinarith

theorem next_bound (base NL NR g m : ℕ) (hg : 0 < g) :
    next base NL NR g m ≤ base+4*(NL+NR)+
      (BandPartition.size NL g+BandPartition.size NR g)*(3*m+7)+m+9 := by
  have hl := SourceBandLayout.work_bound (leftBase base) NL g m hg
  have hr := SourceBandLayout.work_bound (rightBase base NL g m) NR g m hg
  change rightBase base NL g m ≤ _ at hl
  change zeroBase base NL NR g m ≤ _ at hr
  unfold next leftBase at *
  nlinarith

theorem tableCount_le_encoderCount {n : ℕ} (hn : 0 < n) : tableCount n ≤ encoderCount n := by
  have hb : 0 < bandCount n := by
    have hp := (bandCount_mul_bounds n).1
    by_contra h
    have hz : bandCount n=0 := by omega
    rw [hz,Nat.mul_zero] at hp
    omega
  calc
    _ ≤ bandCount n*tableCount n := Nat.le_mul_of_pos_left _ hb
    _ ≤ 2*(bandCount n*tableCount n) := Nat.le_mul_of_pos_left _ (by omega)
    _ = _ := by unfold tableCount encoderCount; ring

theorem modulus_le_encoderCount {n : ℕ} (hn : 0 < n) :
    BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ encoderCount n :=
  (SourceBandCosts.modulus_le_tableCount n).trans (tableCount_le_encoderCount hn)

theorem time_le_encoderCount {NL NR n p U D : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    LightSourceBandPair.time NL NR (bandSize n) p
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) U D ≤
      (2032*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+3905)*encoderCount n+3139 := by
  have hl := SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNL
  have hr := SourceBandCosts.time_le_encoderCount (p := p) (U := U) (D := D) hNR
  have hm := modulus_le_encoderCount hn
  unfold LightSourceBandPair.time Light.fillTime
  nlinarith

theorem next_le_encoderCount {base NL NR n : ℕ} (hn : 0 < n) (hNL : NL ≤ n) (hNR : NR ≤ n) :
    next base NL NR (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n))) ≤
      base+29*encoderCount n+9 := by
  have hl := SourceBandCosts.persistent_space_le_encoderCount (base := leftBase base) hNL
  have hr := SourceBandCosts.persistent_space_le_encoderCount
    (base := rightBase base NL (bandSize n)
      (BlockSourceEncoding.modulus (microHalf (inputBits n)) (blockCount (inputBits n)))) hNR
  have hm := modulus_le_encoderCount hn
  change rightBase base NL (bandSize n) _ ≤ _ at hl
  change zeroBase base NL NR (bandSize n) _ ≤ _ at hr
  unfold next leftBase at *
  omega

end ThreeSum.SourceBandPairCosts
