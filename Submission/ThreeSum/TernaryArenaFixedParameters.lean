import Submission.ThreeSum.TernaryArenaSignedSelection
import Submission.ThreeSum.TernaryPairedCarryBudget
import Submission.ThreeSum.TernaryPairedCollisionRate
import Submission.ThreeSum.TernaryPairedNativeDrift
import Submission.ThreeSum.LightTernaryDimensions

noncomputable section
namespace ThreeSum.TernaryArenaFixedParameters
open Filter TernaryCoverScale TernaryOversizePrime TernaryOversizeRates
open TernaryOversizeOverhead TernarySignedPadding TernaryArenaBudgetExistence
open TernaryPairedCollisionRate TernaryLocalParameters
open scoped Topology
set_option maxHeartbeats 3000000

def familyLength (K m : ℕ) : ℕ := (nativeFamily K m (selectedMoment K)).length

def determinantBound (K radix : ℕ) : ℕ := (2*K).factorial*radix^(2*K)

theorem native_drift {K m F : ℕ} (hK : 0<K) (hF : (9*F)^4≤outputSize m) :
    (9*pairFactor m F K)^4*(outputSize m)^(4*K+3)≤((nativePrime K m)^(2*K))^4 := by
  have hh := TernaryPairedNativeDrift.paired_native_drift K (outputSize m)
    (TernaryEntropyRates.partitionCap m) (inflation K m) (nativePrime K m) F
    (inflation_lower hK m)
    (show outputSize m*TernaryEntropyRates.partitionCap m*(inflation K m)^2≤(nativePrime K m)^2 by
      simpa only [inflatedThreshold,threshold,outputSize,TernaryEntropyRates.partitionCap] using nativePrime_lower K m) hF
  simpa only [pairFactor,outputSize,TernaryEntropyRates.partitionCap,mul_assoc] using hh

theorem familyLength_pos {K : ℕ} (hK : 0<K) (m : ℕ) : 0<familyLength K m := by
  unfold familyLength
  rw [native_family_length]
  unfold inflatedFrequency
  have hf := TernaryCoverCapParameters.frequencyFactor_gt_one m
  have hs := inflation_pos hK m
  positivity

theorem pairFactor_pos {K m F : ℕ} (hF : 0<F) : 0<9*pairFactor m F K := by
  have hM := outputSize_pos m
  unfold pairFactor
  change 0<9*(F*outputSize m*(2^(fixedPi m 1)*3^(fixedPi m 2))^K)
  positivity

/-- Fixed parameters satisfy the exact integer paired drift, along with
all preprocessing, collision, and principal-time margins. -/
theorem exists_parameters {K : ℕ} (hK : 100000000≤K) {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*pairFactor m (familyLength K m) K)^4*(outputSize m)^(4*K+3)≤((nativePrime K m)^(2*K))^4 ∧
      9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) := by
  obtain ⟨t,m,ht,hN,hg,ho,hc,hd,hp,hF,hp9,hcharge⟩ :=
    TernaryPairedCollisionRate.simultaneous_parameters hK hκ c d N
  exact ⟨t,m,ht,hN,hg,ho,hc,hd,hp,native_drift (by omega : 0<K) hF,hp9,hcharge⟩

theorem micro_four {K : ℕ} (hK : 0<K) : 4*microAllowance K<1 := by
  have hk : (1 : ℝ)≤K := by exact_mod_cast hK
  have hpos : (0 : ℝ)<K := by exact_mod_cast hK
  unfold microAllowance
  have hs : (1 : ℝ)≤(K : ℝ)^2 := by nlinarith
  have hd : (0 : ℝ)<100*(K : ℝ)^2 := by positivity
  rw [show (4 : ℝ)*(1/(100*(K : ℝ)^2))=4/(100*(K : ℝ)^2) by ring]
  apply (div_lt_iff₀ hd).mpr
  nlinarith

/-- For the literal padded digit length, the actual requester/carry count
has the required fourth-power initial bound. All constants precede the input. -/
theorem cutoff {K m radix : ℕ} (hK : 0<K) (hm : 0<m) (hb : 1<radix)
    {κ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m radix κ<microAllowance K)
    (U : ℕ→ℕ) (hU : ∀n,1<n→(U n : ℝ)≤(n : ℝ)^κ) :
    ∃n0 : ℕ,∀n≥n0,
      let r := radixLength m n
      let J := paddedLength radix (U n) r
      1<n ∧ r<J ∧ 4*U n<radix^J ∧ n^2≤(outputSize m)^r ∧
      (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
      ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
        (determinantBound K radix)^8*n^(8*K+5) := by
  have hcarryEvent := TernaryPairedCarryBudget.initial_digit_carry_eventually (K := K) hm hb hκ hcarry (micro_four hK) U hU
  have he : ∀ᶠ n : ℕ in atTop,
      1<n ∧ (2^(paddedLength radix (U n) (radixLength m n)))^4*
        (paddedLength radix (U n) (radixLength m n)+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n := by
    filter_upwards [eventually_gt_atTop (1 : ℕ),hcarryEvent,eventually_gt_atTop ((determinantBound K radix)^8)] with n hn hc hd
    exact ⟨hn,hc,hd⟩
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp he
  refine ⟨n0,?_⟩
  intro n hn r J
  obtain ⟨hn1,hc,hd⟩ := hn0 n hn
  refine ⟨hn1,padded_length_proper radix (U n) r,padded_length_capacity hb (U n) r,?_,hc,hd,?_⟩
  · exact Nat.le_pow_clog (by have := outputSize_ge_sixteen hm;omega) (n^2)
  · intro nA hnA
    have ht : nA*2^J≤n*2^J := Nat.mul_le_mul_right _ hnA
    have hh := TernaryPairedInitialBudget.target_count_fourth_bound K (J+2) radix n (2^J)
      (nA*2^J) 1 ht (by simpa only [one_mul] using hc)
    simpa only [LightTernaryInitialBudgets.initial,LightTernaryInitialBudgets.determinantBound,
      determinantBound,one_mul] using hh

/-- The cutoff is phrased in exactly the dimensions produced by the actual
prelude, with its computed magnitude bound n^κ. -/
theorem natural_cutoff {K m radix : ℕ} (hK : 0<K) (hm : 0<m) (hb : 1<radix) (κ : ℕ)
    (hcarry : carryExponent m radix (κ : ℝ)<microAllowance K) :
    ∃n0 : ℕ,∀n≥n0,
      let r := LightTernaryDimensions.r (outputSize m) n
      let J := LightTernaryDimensions.J (outputSize m) radix n (n^κ)
      1<n ∧ r<J ∧ 4*n^κ<radix^J ∧ n^2≤(outputSize m)^r ∧
      (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
      ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
        (determinantBound K radix)^8*n^(8*K+5) := by
  have hh := cutoff hK hm hb (κ := (κ : ℝ)) (by positivity) hcarry (fun n => n^κ) (by
    intro n hn
    simp only [Nat.cast_pow,Real.rpow_natCast,le_refl])
  simpa only [LightTernaryDimensions.r,LightTernaryDimensions.J,radixLength] using hh

theorem native_factor_pos {K : ℕ} (hK : 0<K) (m : ℕ) : 0<9*pairFactor m (familyLength K m) K :=
  pairFactor_pos (familyLength_pos hK m)

def InputGuards (K m radix κ n : ℕ) : Prop :=
  let r := LightTernaryDimensions.r (outputSize m) n
  let J := LightTernaryDimensions.J (outputSize m) radix n (n^κ)
  1<n ∧ r<J ∧ 4*n^κ<radix^J ∧ n^2≤(outputSize m)^r ∧
  (2^J)^4*(J+2)^(8*K)≤n ∧ (determinantBound K radix)^8<n ∧
  ∀nA≤n, (LightTernaryInitialBudgets.initial K radix n J (nA*2^J))^4≤
    (determinantBound K radix)^8*n^(8*K+5)

/-- A single fixed choice, before any input is inspected, provides every
paired, original-collision, signed-preprocessing and terminal guard. -/
theorem simultaneous_cutoff {K : ℕ} (hK : 100000000≤K) (κ c d N : ℕ) :
    ∃t m n0 : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) (κ : ℝ)<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*pairFactor m (familyLength K m) K)^4*(outputSize m)^(4*K+3)≤((nativePrime K m)^(2*K))^4 ∧
      9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) ∧
      ∀n≥n0,InputGuards K m (2^t) κ n := by
  obtain ⟨t,m,ht,hN,hg,ho,hc,hd,hp,hdrift,hp9,hcharge⟩ :=
    exists_parameters hK (κ := (κ : ℝ)) (by positivity) c d N
  have hb : 1<2^t := by
    have hh := Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (show 1≤t by omega)
    norm_num at hh
    omega
  obtain ⟨n0,hn0⟩ := natural_cutoff (by omega : 0<K) hg.1 hb κ hc
  exact ⟨t,m,n0,ht,hN,hg,ho,hc,hd,hp,hdrift,hp9,hcharge,hn0⟩

/-- The actual source/tag coefficient bound fits the fixed word radix;
this follows from the existing minor guard, without another parameter choice. -/
theorem radix_tag_bound {K m radix : ℕ} (hK : 0<K) (hb : 1≤radix)
    (hminor : (2*K).factorial*radix^(2*K)<nativePrime K m) :
    radix≤2*(4^fixedLength m)+1 := by
  have hs : radix^2≤radix^(2*K) := Nat.pow_le_pow_right hb (by omega)
  have hf : radix^(2*K)≤(2*K).factorial*radix^(2*K) := by
    have hh := Nat.mul_le_mul_right (radix^(2*K)) (Nat.factorial_pos (2*K))
    simpa only [Nat.succ_eq_add_one,Nat.zero_add,one_mul] using hh
  have he : 2^(4*fixedLength m+2)=4*(4^fixedLength m)^2 := by
    calc
      _=2^2*((2^2)^fixedLength m)^2 := by
        rw [←pow_mul,←pow_mul,←pow_add]
        congr 1
        ring
      _=_ := by norm_num
  have hp : nativePrime K m≤4*(4^fixedLength m)^2 := by
    rw [←he]
    exact native_crude_upper hK m
  have hh := (hs.trans hf).trans_lt (hminor.trans_le hp)
  by_contra h
  have hge : 2*(4^fixedLength m)≤radix := by omega
  have hsq : 4*(4^fixedLength m)^2≤radix^2 := by
    simpa only [mul_pow,show (2 : ℕ)^2=4 by decide] using Nat.pow_le_pow_left hge 2
  omega

end ThreeSum.TernaryArenaFixedParameters
