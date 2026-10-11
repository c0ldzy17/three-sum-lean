import Submission.ThreeSum.EncodedColorResourceScale

/-! # Finite space and word bounds for the actual retained source constructors -/

namespace ThreeSum.EncodedColorResources

open Scales BandScales ArithmeticStageBounds StageBounds GlobalEncoding LocalCoverBounds
open SubsetAddress CostLedger TrimScales

set_option maxHeartbeats 2600000
set_option maxRecDepth 13000

theorem width_eq (n : ℕ) : width n=256*mu n := BlockSourceSharing.width_eq n

theorem encoder_le (n : ℕ) : encoderCount n ≤ 2*(scale n)^3 := by
  have hn : n ≤ scale n := by have h := (scale_bounds n).2.1; omega
  have hb : bandCount n ≤ n :=
    (ceilDiv_le_iff_le_mul (bandSize_pos n)).mpr (Nat.le_mul_of_pos_left _ (bandSize_pos n))
  have hs : scheduleCount n ≤ scale n := by
    simpa only [half,blocks,BlockSourceCatalogCosts.count_eq_scheduleCount] using (powers n).2.1
  have hf : fullOutputs n ≤ scale n := by
    have hp : 2^(width n) ≤ scale n :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (powers n).1
    rw [width_eq] at hp
    exact (Nat.choose_le_two_pow _ _).trans hp
  unfold encoderCount
  have hh := Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (hb.trans hn)) hs) hf
  nlinarith only [hh]

theorem source_scratch_le (n : ℕ) :
    LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ 10*(scale n)^2 := by
  have hb := (scale_bounds n).1
  have hW := (dimensions n).1
  have hJ := (dimensions n).2.1
  have hL : 512*half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hP : localPrime (half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  have hLP := Nat.mul_le_mul hL hP
  have hlogP := (Nat.log_le_self 2 ((512*half n)*localPrime (half n)+1))
  have hlogE := (Nat.log_le_self 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1))
  have hE := endpoint_le n
  have hq := Nat.pow_le_pow_left hW 2
  have hs := SourceBandBanksCosts.overhead_bound (half n) (blocks n)
  change LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤
    blocks n+2*width n+(width n+1)^2+Nat.log 2 ((512*half n)*localPrime (half n)+1)+
      Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+20 at hs
  nlinarith only [hb,hW,hJ,hLP,hlogP,hlogE,hE,hq,hs]

theorem source_storage_le (n : ℕ) : SourceBandBanksCosts.storageFactor n ≤ 50*(scale n)^2 := by
  have hb := (scale_bounds n).1
  have hW := (dimensions n).1
  have hJ := (dimensions n).2.1
  have hcut := (dimensions n).2.2.1
  have hs := source_scratch_le n
  have hproduct := Nat.mul_le_mul
    (show blocks n+2*width n+7 ≤ 3*scale n+7 by omega)
    (show width n+2 ≤ scale n+1 by omega)
  unfold SourceBandBanksCosts.storageFactor
  rw [← width_eq]
  change (blocks n+2*width n+7)*(width n+2)+mu n+width n+3+
    LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ _
  nlinarith only [hb,hW,hJ,hcut,hs,hproduct]

theorem source_finish_bound (base n : ℕ) : SourceFiniteCosts.finish base n ≤ base+200*(scale n)^5 := by
  have hb := (scale_bounds n).1
  have hJ := (dimensions n).2.1
  have hstorage := source_storage_le n
  have hfactor : 29+blocks n+SourceBandBanksCosts.storageFactor n ≤ 60*(scale n)^2 := by
    nlinarith only [hb,hJ,hstorage]
  have hmul := Nat.mul_le_mul hfactor (encoder_le n)
  unfold SourceFiniteCosts.finish
  change base+(29+blocks n+SourceBandBanksCosts.storageFactor n)*encoderCount n+17 ≤ _
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  nlinarith only [hmul,hb,hp5]

theorem source_space_bound (base n U : ℕ) :
    SourceFiniteCosts.space base n (maxMod n) U (radix n) ≤ base+200*(scale n)^5+U := by
  have hb := (scale_bounds n).1
  have hW := (dimensions n).1
  have hJ := (dimensions n).2.1
  have hP := (scale_bounds n).2.2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hstorage := source_storage_le n
  have hquad := Nat.pow_le_pow_left hW 2
  have hfactor : 29+blocks n+SourceBandBanksCosts.storageFactor n+(width n+1)^2+(width n+1) ≤
      60*(scale n)^2 := by nlinarith only [hb,hJ,hW,hstorage,hquad]
  have hmul := Nat.mul_le_mul hfactor (encoder_le n)
  have hS : scheduleCount n ≤ scale n := by
    simpa only [half,blocks,BlockSourceCatalogCosts.count_eq_scheduleCount] using (powers n).2.1
  have hlogS := Nat.log_le_self 2 (scheduleCount n+1)
  have hlogU := Nat.log_le_self 2 (U+1)
  have hlogP := Nat.log_le_self 2 (maxMod n+radix n+1)
  have hmax : max (Nat.log 2 (U+1)+2) (Nat.log 2 (maxMod n+radix n+1)+2) ≤ U+2*scale n+3 := by omega
  unfold SourceFiniteCosts.space
  rw [← width_eq]
  change base+(29+blocks n+SourceBandBanksCosts.storageFactor n+(width n+1)^2+(width n+1))*encoderCount n+
    Nat.log 2 (scheduleCount n+1)+max (Nat.log 2 (U+1)+2) (Nat.log 2 (maxMod n+radix n+1)+2)+19 ≤ _
  have hp5 : scale n ≤ (scale n)^5 := Nat.le_self_pow (by decide) _
  nlinarith only [hb,hmul,hmax,hS,hlogS,hp5]

theorem source_span_le (n : ℕ) : SourceBandBankLayout.span (half n) (blocks n) (mu n) ≤ 100*(scale n)^3 := by
  have hm : SharedReportingBankResourceBounds.magnitude n+1 ≤ scale n := by unfold scale; omega
  have hs := SharedReportingBankResourceBounds.source_span_le_magnitude n
  rw [show 2*SharedReportingBankResourceBounds.half n*SharedReportingBankResourceBounds.blocks n=mu n from
    BlockSourceSharing.cutoff_eq n] at hs
  exact hs.trans (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left hm 3))

theorem source_controls_word_le (n : ℕ) : LightSourceControls.word (half n) (blocks n) (mu n) ≤ 200*(scale n)^3 := by
  have hb := (scale_bounds n).1
  have hW := (dimensions n).1
  have hJ := (dimensions n).2.1
  have hcut := (dimensions n).2.2.1
  have H := local_bounds n
  have hL := H.width
  have hP := H.prime
  have hS := H.rounds
  have hocc := (powers n).2.1
  have hPP := (powers n).2.2.1
  have hmod := modulus_le n
  have hE := endpoint_le n
  have hpow := (powers n).1
  have hpow0 : 2^(width n) ≤ scale n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hpow
  have hK := (SharedReportingBankResourceBounds.downset_le_pow (width n) (mu n)).trans hpow0
  have hstrideProd := Nat.mul_le_mul hW hK
  have hstride : SourceControlLayout.stride (width n) (downsetCap (width n) (mu n)) ≤ 10*(scale n)^2 := by
    unfold SourceControlLayout.stride
    nlinarith only [hb,hW,hK,hstrideProd]
  have hLP := Nat.mul_le_mul (show 512*half n ≤ scale n by omega) (show localPrime (half n) ≤ scale n by omega)
  have hlogP := Nat.log_le_self 2 ((512*half n)*localPrime (half n)+1)
  have hlogE := Nat.log_le_self 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)
  have hquad := Nat.pow_le_pow_left hW 2
  have hspan := source_span_le n
  have hspanWord : LightSourceControls.spanWord (half n) (blocks n) (mu n) ≤ 150*(scale n)^3 := by
    unfold LightSourceControls.spanWord SourceControlLayout.word
    rw [SourceControlLayout.span_eq]
    change SourceBandBankLayout.span (half n) (blocks n) (mu n)+
      SourceControlLayout.stride (width n) (downsetCap (width n) (mu n))+blocks n+width n+
      downsetCap (width n) (mu n)+LightBlockSourceCatalog.count (half n) (blocks n)+
      Nat.log 2 ((512*half n)*localPrime (half n)+1)+
      Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+(width n+1)^2+30 ≤ _
    nlinarith only [hb,hspan,hstride,hJ,hW,hK,hocc,hlogP,hlogE,hLP,hE,hquad]
  have hwp := Nat.mul_le_mul hW hpow
  have hSwhole := schedule_power_le n
  unfold LightSourceControls.word
  change LightSourceControls.spanWord (half n) (blocks n) (mu n)+(width n+1)*2^(width n+1)+
    (scheduleSize (half n)+1)^(blocks n+1)+2*((512*half n)*localPrime (half n)+1)+
    2*(LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+
    localPrime (half n)^(blocks n)*localPrime (half n)+blocks n+512*half n+localPrime (half n)+
    mu n+scheduleSize (half n)+BlockSourceEncoding.modulus (half n) (blocks n)+width n+50 ≤ _
  nlinarith only [hb,hspanWord,hwp,hSwhole,hLP,hE,hPP,hJ,hL,hP,hcut,hS,hmod,hW]

theorem retained_source_word_le (n : ℕ) : LightBlockSourceRetainedHost.word n n (half n) (blocks n) ≤ 50*(scale n)^2 := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hW := (dimensions n).1
  have H := local_bounds n
  have hL := H.width
  have hP := H.prime
  have hcap := H.cap
  have hlocal := H.maskPower
  have hpow := (powers n).1
  have hPP := (powers n).2.2.1
  have hmod := modulus_le n
  have hE := endpoint_le n
  have hV : (512*half n).choose (half n) ≤ scale n := by
    have hp0 : 2^(512*half n) ≤ scale n :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (by omega : 2^(512*half n+1) ≤ scale n)
    exact (Nat.choose_le_two_pow _ _).trans hp0
  have hpow0 : 2^(width n) ≤ scale n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hpow
  have hcoeff := Nat.mul_le_mul hPP hP
  have hglobal := Nat.mul_le_mul hW hPP
  have hrow := Nat.mul_le_mul hL hP
  have hLP := Nat.mul_le_mul (show 512*half n ≤ scale n by omega) (show localPrime (half n) ≤ scale n by omega)
  have hwp := Nat.mul_le_mul hW hpow
  have hnp := Nat.mul_le_mul hpow0 (show n ≤ scale n by omega)
  unfold LightBlockSourceRetainedHost.word LightSourcePreparation.word LightBlockSourceHashes.word
    LightBlockCoefficients.word LightOneHot.word LightSourceMaskFlags.word LightSourceRowFlag.word
    LightSourceRowScan.word LightSourceRetainedStages.word
  rw [pow_succ (localPrime (half n)) (blocks n)]
  dsimp only [width] at hW hpow hglobal hwp hnp
  nlinarith only [hb,hn,hW,hL,hP,hcap,hpow,hmod,hE,hV,hcoeff,hglobal,hrow,hLP,hwp,hnp]

theorem source_word_bound (n U : ℕ) :
    SourceFiniteCosts.word n (maxMod n) U (radix n) ≤ 200*(scale n)^3+4*U := by
  have hb := (scale_bounds n).1
  have hn := (scale_bounds n).2.1
  have hJ := (dimensions n).2.1
  have hg := (dimensions n).2.2.2.1
  have hM := (dimensions n).2.2.2.2
  have hP := (scale_bounds n).2.2.2.2.1
  have hmod := modulus_le n
  have hS := (local_bounds n).rounds
  have hocc := (powers n).2.1
  have hcontrols := source_controls_word_le n
  have hretained := retained_source_word_le n
  have hbank : LightSourceBandBanks.word n n (half n) (blocks n) ≤ 60*(scale n)^2 := by
    unfold LightSourceBandBanks.word LightSourceBandBankStep.word LightOutputDecodeDigits.word
    apply max_le <;> nlinarith only [hb,hn,hJ,hS,hocc,hretained]
  unfold SourceFiniteCosts.word LightSourceControlsHost.word LightSourceBandHost.word
    LightSourceBandPair.word LightSourceBandStep.word LightSourceResidues.word
  change max (LightSourceControls.word (half n) (blocks n) (mu n))
    (max (max (4*U+8*maxMod n+4*radix n+4*BlockSourceEncoding.modulus (half n) (blocks n)+32+n+bandSize n+2)
      (4*U+8*maxMod n+4*radix n+4*BlockSourceEncoding.modulus (half n) (blocks n)+32+n+bandSize n+2)+16)
      (LightSourceBandBanks.word n n (half n) (blocks n))) ≤ _
  simp only [max_self]
  apply max_le
  · omega
  · apply max_le <;> nlinarith only [hb,hn,hg,hM,hP,hmod,hbank]

end ThreeSum.EncodedColorResources
