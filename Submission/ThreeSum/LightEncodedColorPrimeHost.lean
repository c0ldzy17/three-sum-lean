import Submission.ThreeSum.LightEncodedColorNormalize
import Submission.ThreeSum.EncodedColorPrimeReadyData

/-! # Original selected color to its retained common prime and physical arrays -/

namespace ThreeSum.LightEncodedColorPrimeHost

open Light Scales BandScales ArithmeticStageBounds ColorClassLists EncodedColorLayout

set_option maxHeartbeats 3200000
set_option maxRecDepth 15000

def body (pNormalize pPrime : ℕ) : Stmt :=
  .call pNormalize [v 0,v 1,v 2,v 3,v 4] 5 ;;
  .set 6 (v 5 +' k 1) ;;
  .set 7 (M (v 4)) ;;
  .set 8 (M (v 4 +' k 1)) ;;
  .set 9 (M (v 4 +' k 2)) ;;
  .set 10 (M (v 4 +' k 3)) ;;
  .set 11 (M (v 4 +' k 4)) ;;
  .set 12 (M (v 4 +' k 5)) ;;
  .set 13 (M (v 4 +' k 6)) ;;
  .set 14 (M (v 2 +' k 17)) ;;
  .set 15 (M (v 2 +' k 14)) ;;
  .set 16 (M (v 2 +' k 18)) ;;
  .call pPrime [v 7,v 8,v 9,v 10,v 11,v 12,v 14,v 13,v 15,v 16,v 6] 17 ;;
  .set 0 (v 6)

def joined : Program := ReportingHostRelocation.program LightEncodedColorNormalize.program LightEncodedColorPrime.program
def program : Program := joined ++ [body 45 70]

theorem program_length : program.length=72 := rfl

def time (k n : ℕ) : ℕ := LightEncodedColorNormalize.time n+BandPrimeCosts.timeBudget k n+1760

def space (free k n : ℕ) : ℕ := max (LightEncodedColorNormalize.space free n)
  (LightEncodedColorPrimeCore.space (prime free n (bandSize n)) (maxMod n) (bandSize n)
    (radix n) (primeWindow n) (n^k))

def word (k n : ℕ) : ℕ := max (LightEncodedColorNormalize.word n (n^k))
  (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) (n^k))+
    bandSize n+radix n+primeWindow n+100

def depth (n : ℕ) : ℕ := max
  (LightBandRawAColor.depth (inputBits n+1) n (bandSize n)+3)
  (Nat.clog 2 (maxMod n)+11)

def inputTime (n U : ℕ) : ℕ := LightEncodedColorNormalize.time n+
  LightEncodedColorPrime.time (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U+600

def inputSpace (free n U : ℕ) : ℕ := max (LightEncodedColorNormalize.space free n)
  (LightEncodedColorPrimeCore.space (prime free n (bandSize n)) (maxMod n) (bandSize n)
    (radix n) (primeWindow n) U)

def inputWord (n U : ℕ) : ℕ := max (LightEncodedColorNormalize.word n U)
  (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U)+
    bandSize n+radix n+primeWindow n+100

variable {lim : Limits} {d : ℕ}

theorem program_meets_input {μ : ℕ → ℤ} {src n params row free U : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : inputSpace free n U ≤ lim.space) (hword : (inputWord n U : ℤ) ≤ lim.word)
    (hd : d+depth n ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 71 d [src,n,params,row,free] μ (inputTime n U)
      (fun r ν => r=(prime free n (bandSize n) : ℤ) ∧
        EncodedColorPrimeReadyData.Output ν free n color x ∧ Kept μ ν free) := by
  have hsNorm : LightEncodedColorNormalize.space free n ≤ lim.space := (le_max_left _ _).trans hspace
  have hsPrime : LightEncodedColorPrimeCore.space (prime free n (bandSize n)) (maxMod n) (bandSize n)
      (radix n) (primeWindow n) U ≤ lim.space := (le_max_right _ _).trans hspace
  have hwNorm : (LightEncodedColorNormalize.word n U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show _ ≤ inputWord n U by unfold inputWord; omega)).trans hword
  have hwPrime : (LightEncodedColorPrime.word (maxMod n) n n n (bandSize n) (radix n) (primeWindow n) U : ℤ) ≤
      lim.word := (Int.ofNat_le.mpr (show _ ≤ inputWord n U by unfold inputWord; omega)).trans hword
  have hsmall (z : ℕ) (hz : z ≤ inputWord n U) : (z : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hz).trans hword
  have hG := hsmall (bandSize n) (by unfold inputWord; omega)
  have hM := hsmall (radix n) (by unfold inputWord; omega)
  have hY := hsmall (primeWindow n) (by unfold inputWord; omega)
  have hdNorm : d+1+LightBandRawAColor.depth (inputBits n+1) n (bandSize n)+2 ≤ lim.depth := by
    unfold depth at hd; omega
  have hdPrime : d+1+Nat.clog 2 (maxMod n)+10 ≤ lim.depth := by unfold depth at hd; omega
  have hmeta : prime free n (bandSize n)+6 ≤ lim.space := by
    have hh := (le_max_left _ _).trans hsPrime
    unfold LightPrimePool.space EncodedColorPrimeData.poolBase at hh
    omega
  have hfree := free_le_prime free n (bandSize n)
  have hEnd : normalizedEnd free n (bandSize n)+1 ≤ lim.space := by
    change prime free n (bandSize n) ≤ lim.space
    omega
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords⟩ := normalized_ends free n (bandSize n)
  have add1 : ((free : ℤ)+1).toNat=free+1 := by omega
  have add2 : ((free : ℤ)+2).toNat=free+2 := by omega
  have add3 : ((free : ℤ)+3).toNat=free+3 := by omega
  have add4 : ((free : ℤ)+4).toNat=free+4 := by omega
  have add5 : ((free : ℤ)+5).toNat=free+5 := by omega
  have add6 : ((free : ℤ)+6).toNat=free+6 := by omega
  have par14 : ((params : ℤ)+14).toNat=params+14 := by omega
  have par17 : ((params : ℤ)+17).toNat=params+17 := by omega
  have par18 : ((params : ℤ)+18).toNat=params+18 := by omega
  apply Meets.of_body (p := 71) (by rfl : program[71]?=some (body 45 70))
  unfold body inputTime
  have hNorm := ((LightEncodedColorNormalize.program_meets (d := d+1) (μ := μ) (src := src) (params := params)
    (row := row) (free := free) color x hw hn hsrc hparams hrow hsNorm hwNorm hdNorm hread hbound hparameters hcolor).append
      (LightEncodedColorPrime.program.map (ReportingHostRelocation.relocate 46))).append [body 45 70]
  light_call hNorm with ptr μ₁ ⟨hptr,⟨heads,A,hsA,B,hsB,C,hsC,hcount,normalized⟩,keptNorm⟩
  have params₁ := hparameters.of_kept keptNorm (by
    simpa [LightParameterInit.values,LightScales.values,LightLocalParameters.values,LightLocalCounts.values,
      LightGlobalSizes.values] using hparams)
  obtain ⟨_,_,_,_,readM,readG,readY⟩ := EncodedColorParameterData.reads params₁
  obtain ⟨readA,readAE,readB,readBE,readC,readCE,readRec,_⟩ := EncodedColorNormalizedData.heads_read heads
  light_set (prime free n (bandSize n) : ℕ) using hptr,prime
  light_set (av free n : ℕ) using readA
  light_set (ae free n : ℕ) using readAE,add1
  light_set (bv free n : ℕ) using readB,add2
  light_set (be free n : ℕ) using readBE,add3
  light_set (cv free n : ℕ) using readC,add4
  light_set (ce free n : ℕ) using readCE,add5
  light_set (rec free n (bandSize n) : ℕ) using readRec,add6
  light_set (bandSize n : ℕ) using readG,par17
  light_set (radix n : ℕ) using readM,par14
  light_set (primeWindow n : ℕ) using readY,par18
  have ha := length_classList_le color x 0 1
  have hb := length_classList_le color x 1 1
  have hc := length_classList_le color x 2 (-1)
  have hnA := normalized.2.1.2.1.trans ha
  have hnB := normalized.2.2.1.2.1.trans hb
  have hnC := normalized.2.2.2.1.2.1.trans hc
  have hactualCount := EncodedColorPrimeCosts.count_mono (g := bandSize n) hnA hnB hnC
  have hcapacity : LightEncodedColorPrime.count n n n (bandSize n)=ColorBandBounds.count n (bandSize n) := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  rw [hcapacity] at hactualCount
  have hactualWord := (Int.ofNat_le.mpr (EncodedColorPrimeCosts.word_mono
    (maxMod := maxMod n) (M := radix n) (y := primeWindow n) (U := U) hnA hnB hnC)).trans hwPrime
  have hPrime := (ReportingHostRelocation.meets
    (LightEncodedColorPrime.program_meets (d := d+1) (μ := μ₁) (free := prime free n (bandSize n))
      hw (lt_of_lt_of_le (by decide : 0 < 2) (primeWindow_ge_two n))
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by have hh := Nat.mul_le_mul_left 4 hactualCount; omega) hsPrime hactualWord hdPrime
      (LightColorBands.class_bounded color x 0 1 (by norm_num) hbound)
      (LightColorBands.class_bounded color x 1 1 (by norm_num) hbound)
      (LightColorBands.class_bounded color x 2 (-1) (by norm_num) hbound) normalized
      (BandPrimeScales.resource_modulus_bound hR)) LightEncodedColorNormalize.program).append [body 45 70]
  have hPrimeBound := hPrime.mono_time (EncodedColorPrimeCosts.time_mono hnA hnB hnC)
  light_call hPrimeBound with p ν ⟨hp,primes,keptPrime⟩
  light_set (prime free n (bandSize n) : ℕ)
  have normalized' := normalized.keep keptPrime ha hb hc hav hae hbv hbe hcv hce htables hrecords
    (by change normalizedEnd free n (bandSize n) ≤ prime free n (bandSize n); unfold prime; omega)
  refine ⟨rfl,⟨?_,A,hsA,B,hsB,C,hsC,?_,normalized',primes⟩,?_⟩
  · exact heads.of_kept keptPrime (by simpa [normalizedHeads] using hfree)
  · exact (keptPrime _ (by unfold prime; omega)).trans hcount
  · intro i hi
    exact (keptPrime i (by omega)).trans (keptNorm i hi)


theorem program_meets {μ : ℕ → ℤ} {src n params row free k : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hR : 4 ≤ radix n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : space free k n ≤ lim.space) (hword : (word k n : ℤ) ≤ lim.word)
    (hd : d+depth n ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (n^k : ℕ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 71 d [src,n,params,row,free] μ (time k n)
      (fun r ν => r=(prime free n (bandSize n) : ℤ) ∧
        EncodedColorPrimeReadyData.Output ν free n color x ∧ Kept μ ν free) := by
  have ht := EncodedColorPrimeCosts.time_le_budget (nA := n) (nB := n) (nC := n) k hn le_rfl le_rfl le_rfl
  exact (program_meets_input color x hw hn hR hsrc hparams hrow hspace hword hd hread hbound
    hparameters hcolor).mono_time (by unfold inputTime time; omega)

end ThreeSum.LightEncodedColorPrimeHost
