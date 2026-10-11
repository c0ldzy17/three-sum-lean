import Submission.ThreeSum.SharedReportingBankResourceBounds
import Submission.ThreeSum.LightLocalCoverMagnitude

/-! # Finite scale bounds for every shared-bank resource component -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Scales Light SubsetAddress SharedReportingBankLayout SharedReportingBankHeader

set_option maxHeartbeats 3000000
set_option maxRecDepth 14000

def half (n : ℕ) : ℕ := microHalf (inputBits n)
def blocks (n : ℕ) : ℕ := blockCount (inputBits n)
def magnitude (n : ℕ) : ℕ := 2^(2048*(inputBits n+1))
def polynomialPart (n : ℕ) : ℕ := 5000*(magnitude n+1)^5*(n+1)^2
def envelope (n : ℕ) : ℕ := polynomialPart n+(magnitude n)^64
def scaledWord (n : ℕ) : ℕ := word (half n) (blocks n) n (BandScales.bandSize n)
def scaledExtent (n : ℕ) : ℕ := extent (half n) (blocks n) n
def scaledDepth (n : ℕ) : ℕ := depth (half n) (blocks n)

structure Components (n : ℕ) : Prop where
  positive : 1 ≤ magnitude n
  localWidthBound : 512*half n+1 ≤ magnitude n
  blocksBound : blocks n+1 ≤ magnitude n
  levelsBound : levels (blocks n)+1 ≤ magnitude n
  widthBound : width (half n) (blocks n)+1 ≤ magnitude n
  prefixBound : prefixCount (half n) (blocks n) ≤ magnitude n
  localPower : 2^(512*half n+1) ≤ magnitude n
  pairsPower : 2^(2*(512*half n)) ≤ magnitude n
  widthPower : 2^(width (half n) (blocks n)+1) ≤ magnitude n
  indexPower : 2^(2*width (half n) (blocks n)) ≤ magnitude n
  occurrence : LightBlockSourceCatalog.count (half n) (blocks n) ≤ magnitude n
  prime : LocalCoverBounds.localPrime (half n) ≤ magnitude n
  primePower : LocalCoverBounds.localPrime (half n)^(blocks n)*LocalCoverBounds.localPrime (half n) ≤ magnitude n
  radixPower : (2^(512*half n)+1)^(blocks n) ≤ magnitude n
  switchBase : blocks n+2*half n*blocks n+1001 ≤ magnitude n
  depthWord : LightSwitchDepth.word (blocks n) ≤ magnitude n

theorem primitive_bounds (n : ℕ) :
    half n ≤ inputBits n ∧ blocks n ≤ 20*inputBits n ∧
    2*half n*blocks n ≤ inputBits n ∧
    width (half n) (blocks n) ≤ 256*inputBits n := by
  have hh := LightScales.microHalf_le_self (inputBits n)
  have hj := LightScales.blockCount_le (inputBits n)
  have ht := LightScales.totalSize_le_self (inputBits n)
  change blocks n*(2*half n) ≤ inputBits n at ht
  refine ⟨hh,hj,by nlinarith,?_⟩
  unfold width localWidth
  nlinarith

theorem linear_le_magnitude (n : ℕ) : 2048*(inputBits n+1) ≤ magnitude n := by
  have hh : inputBits n+1 ≤ 2^(inputBits n) := Nat.lt_two_pow_self
  calc
    _ ≤ 2048*2^(inputBits n) := Nat.mul_le_mul_left _ hh
    _ = 2^(inputBits n+11) := by rw [pow_add]; norm_num; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem components (n : ℕ) : Components n := by
  obtain ⟨hh,hJ,ht,hW⟩ := primitive_bounds n
  have hlin := linear_le_magnitude n
  have hk := levels_le (blocks n)
  have hprod : half n*blocks n ≤ inputBits n := by nlinarith
  have raise (e : ℕ) (he : e ≤ 2048*(inputBits n+1)) : 2^e ≤ magnitude n :=
    Nat.pow_le_pow_right (by decide) he
  refine ⟨by exact Nat.two_pow_pos _,by omega,by omega,by omega,by omega,?_,?_,?_,?_,?_,?_,?_,?_,?_,by omega,?_⟩
  · unfold prefixCount
    apply raise
    have he : 2*((blocks n+1)*(512*half n))=
        2*width (half n) (blocks n)+2*(512*half n) := by unfold width localWidth; ring
    rw [he]
    omega
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · exact raise _ (by omega)
  · have hs := LightLocalCoverMagnitude.rounds_bound (half n)
    calc
      _ ≤ (2^(1029*half n+16))^(blocks n) := Nat.pow_le_pow_left hs _
      _ = 2^((1029*half n+16)*blocks n) := by rw [pow_mul]
      _ ≤ _ := raise _ (by nlinarith)
  · exact (LocalParameterBounds.prime_bound (half n)).trans (raise _ (by omega))
  · rw [← pow_succ]
    calc
      _ ≤ (2^(514*half n+2))^(blocks n+1) := Nat.pow_le_pow_left (LocalParameterBounds.prime_bound (half n)) _
      _ = 2^((514*half n+2)*(blocks n+1)) := by rw [pow_mul]
      _ ≤ _ := raise _ (by nlinarith)
  · calc
      _ ≤ (2^(512*half n+1))^(blocks n) :=
        Nat.pow_le_pow_left (LightLocalCoverMagnitude.succ_pow_bound le_rfl) _
      _ = 2^((512*half n+1)*blocks n) := by rw [pow_mul]
      _ ≤ _ := raise _ (by
        have he : (512*half n+1)*blocks n=width (half n) (blocks n)+blocks n := by unfold width localWidth; ring
        rw [he]
        omega)
  · unfold LightSwitchDepth.word
    omega

theorem band_le_magnitude (n : ℕ) : BandScales.bandSize n ≤ magnitude n := by
  have hB := SourceBandCosts.bandSize_le_fullOutputs n
  have hfull : TrimScales.fullOutputs n ≤ 2^(width (half n) (blocks n)) := by
    rw [show width (half n) (blocks n)=256*mu n from BlockSourceSharing.width_eq n]
    exact Nat.choose_le_two_pow _ _
  exact (hB.trans hfull).trans ((Nat.pow_le_pow_right (by decide) (by omega : width (half n) (blocks n) ≤
    width (half n) (blocks n)+1)).trans (components n).widthPower)

theorem prefix_storage_le_magnitude (n : ℕ) :
    prefixStorage (half n) (blocks n) ≤ (magnitude n+1)^2 := by
  have H := components n
  have hmul := Nat.mul_le_mul (H.levelsBound.trans (Nat.le_succ _)) (Nat.add_le_add_right H.prefixBound 1)
  simpa only [prefixStorage,pow_two] using hmul

theorem source_span_le_magnitude (n : ℕ) :
    SourceBandBankLayout.span (half n) (blocks n) (2*half n*blocks n) ≤ 100*(magnitude n+1)^3 := by
  have H := components n
  have hW := H.widthBound
  have hL := H.localWidthBound
  have hJ := H.blocksBound
  have hS := H.occurrence
  have hP := H.prime
  have hPP := H.primePower
  have hM := H.positive
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hcap := (downset_le_pow (width (half n) (blocks n)) (2*half n*blocks n)).trans hpower
  have hlogP : Nat.log 2 ((512*half n)*LocalCoverBounds.localPrime (half n)+1) ≤ (magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show 512*half n ≤ magnitude n by omega) hP
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hlogE : Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1) ≤ (magnitude n+1)^2 := by
    have hm := Nat.mul_le_mul (show width (half n) (blocks n) ≤ magnitude n by omega) hPP
    unfold LightBlockSourceBuild.endpointBound
    change Nat.log 2 (width (half n) (blocks n)*
      (LocalCoverBounds.localPrime (half n)^(blocks n)*LocalCoverBounds.localPrime (half n))+1) ≤ _
    exact (Nat.log_le_self _ _).trans (by nlinarith)
  have hscratch := SourceBandBanksCosts.overhead_bound (half n) (blocks n)
  change LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤
    blocks n+2*width (half n) (blocks n)+(width (half n) (blocks n)+1)^2+
    Nat.log 2 ((512*half n)*LocalCoverBounds.localPrime (half n)+1)+
    Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)+20 at hscratch
  have hquad := Nat.pow_le_pow_left hW 2
  have hwork : LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ 30*(magnitude n+1)^2 := by
    nlinarith
  have hstride : LightBlockSourceBatchLayout.stride (width (half n) (blocks n)) (2*half n*blocks n)+2 ≤
      12*(magnitude n+1)^2 := by
    have hfamily := Nat.mul_le_mul hW hcap
    unfold LightBlockSourceBatchLayout.stride LightBlockSourceBatchLayout.family
    nlinarith
  have hprod := Nat.mul_le_mul hS hstride
  rw [SourceBandBanksCosts.span_eq]
  change LightBlockSourceCatalog.count (half n) (blocks n)*
    (LightBlockSourceBatchLayout.stride (width (half n) (blocks n)) (2*half n*blocks n)+2)+
    downsetCap (width (half n) (blocks n)) (2*half n*blocks n)+width (half n) (blocks n)+2+
    LightBlockSourceRetainedHost.space 0 (half n) (blocks n) ≤ _
  nlinarith

theorem cell_le_magnitude (n : ℕ) : cellBound (half n) (blocks n) ≤ 20*(magnitude n+1)^3 := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hN := H.prefixBound
  have hE := H.pairsPower
  have hS := prefix_storage_le_magnitude n
  have hlocal : 2^(512*half n) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.localPower
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans H.widthPower
  have hquad := Nat.pow_le_pow_left hW 2
  have hbox := Nat.mul_le_mul (Nat.mul_le_mul hN hW) hpower
  unfold cellBound
  nlinarith

theorem scaled_extent_le (n : ℕ) : scaledExtent n ≤ polynomialPart n := by
  have H := components n
  have hK : levels (blocks n) ≤ magnitude n+1 := by have hh := H.levelsBound; omega
  have hc := cell_le_magnitude n
  have hp4 : magnitude n+1 ≤ (magnitude n+1)^4 := Nat.le_self_pow (by decide) _
  have hlevels := Nat.mul_le_mul hK hc
  have hterm : 5*levels (blocks n)+levels (blocks n)*cellBound (half n) (blocks n) ≤
      25*(magnitude n+1)^4 := by nlinarith
  have hrows := Nat.mul_le_mul (H.occurrence.trans (Nat.le_succ _))
    (show n*n ≤ (n+1)^2 by nlinarith)
  have hprod : LightBlockSourceCatalog.count (half n) (blocks n)*n*n*
      (5*levels (blocks n)+levels (blocks n)*cellBound (half n) (blocks n)) ≤
      25*(magnitude n+1)^5*(n+1)^2 := by
    have hh := Nat.mul_le_mul hrows hterm
    nlinarith only [hh]
  have hquad : (512*half n+1)^2 ≤ (magnitude n+1)^5 := by
    simpa only [Nat.succ_eq_add_one] using
      (Nat.pow_le_pow_left (H.localWidthBound.trans (Nat.le_succ _)) 2).trans
        (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 5))
  have hp : 1 ≤ (magnitude n+1)^5 := Nat.one_le_pow _ _ (by omega)
  have hinit : 9+(512*half n+1)^2 ≤ 10*(magnitude n+1)^5 := by omega
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hinit' := hinit.trans (Nat.le_mul_of_pos_right _ hn)
  unfold scaledExtent extent polynomialPart
  calc
    _ ≤ 10*(magnitude n+1)^5*(n+1)^2+25*(magnitude n+1)^5*(n+1)^2 :=
      Nat.add_le_add hinit' hprod
    _ = 35*(magnitude n+1)^5*(n+1)^2 := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide : 35 ≤ 5000))

theorem scaled_depth_le (n : ℕ) : scaledDepth n ≤ polynomialPart n := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hK := H.levelsBound
  have hp : magnitude n+1 ≤ (magnitude n+1)^5 := Nat.le_self_pow (by decide) _
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hm := Nat.le_mul_of_pos_right (5000*(magnitude n+1)^5) hn
  unfold scaledDepth depth polynomialPart
  nlinarith

theorem scaled_word_le (n : ℕ) : scaledWord n ≤ envelope n := by
  have H := components n
  have hM := H.positive
  have hL := H.localWidthBound
  have hW := H.widthBound
  have hJ := H.blocksBound
  have hK := H.levelsBound
  have hN := H.prefixBound
  have hC := H.occurrence
  have hP := H.localPower
  have hE := H.pairsPower
  have hWP := H.widthPower
  have hIP := H.indexPower
  have hD := H.depthWord
  have hG := band_le_magnitude n
  have hS := prefix_storage_le_magnitude n
  have hspan := source_span_le_magnitude n
  have hpower : 2^(width (half n) (blocks n)) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hWP
  have hlocal : 2^(512*half n) ≤ magnitude n :=
    (Nat.pow_le_pow_right (by decide) (by omega)).trans hP
  have hv := Nat.mul_le_mul hlocal H.radixPower
  have hkeyMul := Nat.mul_le_mul hlocal hv
  have hkeys : LightRadixKeys.word (2^(512*half n)) (2^(512*half n)) (blocks n) ≤
      (magnitude n)^3+2*magnitude n+1 := by
    unfold LightRadixKeys.word LightRadixRows.word
    nlinarith
  have hindexMul := Nat.mul_le_mul (Nat.pow_le_pow_left hpower 2) (Nat.add_le_add_right hIP 1)
  have hindex : LightReportingSortedCatalog.word (width (half n) (blocks n))
      (2^(2*width (half n) (blocks n))) ≤ (magnitude n)^2*(magnitude n+1)+3*magnitude n+2 := by
    unfold LightReportingSortedCatalog.word LightReportingPackKeys.word
    omega
  have hwidth := Nat.mul_le_mul hW hWP
  have hv1 := Nat.mul_le_mul hpower hG
  have hv2 := Nat.mul_le_mul hv1 hv1
  have hv3 := Nat.mul_le_mul hpower hv2
  have hcontrol := Nat.mul_le_mul_right n hC
  have hswitch := Nat.pow_le_pow_left H.switchBase 64
  let R := (magnitude n+1)^5*(n+1)^2
  have hn : 1 ≤ (n+1)^2 := Nat.one_le_pow _ _ (by omega)
  have hp : 1 ≤ (magnitude n+1)^5 := Nat.one_le_pow _ _ (by omega)
  have dominates {e : ℕ} (he : e ≤ 5) : (magnitude n+1)^e ≤ R :=
    (Nat.pow_le_pow_right (by omega) he).trans (Nat.le_mul_of_pos_right _ hn)
  have smaller {e : ℕ} (he : e ≤ 5) : (magnitude n)^e ≤ R :=
    (Nat.pow_le_pow_left (Nat.le_succ _) e).trans (dominates he)
  have oneR : 1 ≤ R := by simpa only [pow_zero] using dominates (e := 0) (by decide)
  have magR : magnitude n ≤ R := by simpa only [pow_one] using smaller (e := 1) (by decide)
  have nquad : n ≤ (n+1)^2 := by nlinarith only [Nat.zero_le n]
  have nR : n ≤ R := nquad.trans (Nat.le_mul_of_pos_left _ hp)
  have mnR : magnitude n*n ≤ R := Nat.mul_le_mul
    ((Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)) nquad
  have controlR := hcontrol.trans mnR
  have storageR := hS.trans (dominates (e := 2) (by decide))
  have spanR := hspan.trans (Nat.mul_le_mul_left 100 (dominates (e := 3) (by decide)))
  have cubeR := smaller (e := 3) (by decide)
  have keysR : LightRadixKeys.word (2^(512*half n)) (2^(512*half n)) (blocks n) ≤ 4*R := by omega
  have indexProductR : (magnitude n)^2*(magnitude n+1) ≤ R := by
    calc
      _ ≤ (magnitude n+1)^2*(magnitude n+1) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (Nat.le_succ _) 2)
      _ = (magnitude n+1)^3 := by ring
      _ ≤ R := dominates (by decide)
  have indexR : LightReportingSortedCatalog.word (width (half n) (blocks n))
      (2^(2*width (half n) (blocks n))) ≤ 6*R := by omega
  have widthR : (width (half n) (blocks n)+1)*2^(width (half n) (blocks n)+1) ≤ R := by
    exact hwidth.trans (by simpa only [pow_two] using smaller (e := 2) (by decide))
  have valuesR : 2^(width (half n) (blocks n))*
      ((2^(width (half n) (blocks n))*BandScales.bandSize n)*
       (2^(width (half n) (blocks n))*BandScales.bandSize n)) ≤ R := by
    exact hv3.trans (by simpa only [show magnitude n*((magnitude n*magnitude n)*(magnitude n*magnitude n))=
      (magnitude n)^5 by ring] using smaller (e := 5) (by decide))
  unfold scaledWord word envelope
  apply Nat.add_le_add _ hswitch
  rw [show polynomialPart n=5000*R by dsimp [R,polynomialPart]; ring]
  unfold control stateWord
  omega

end ThreeSum.SharedReportingBankResourceBounds
