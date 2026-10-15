import Submission.ThreeSum.TernaryOversizeRates
import Submission.ThreeSum.TernaryRadixOverhead

/-! The non-S^4 part of the literal family, raw-cap and carry multiplicity. -/
noncomputable section
namespace ThreeSum.TernaryOversizeOverhead
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open TernaryLocalParameters TernaryCoverLocal TernaryOversizePrime TernaryOversizeRates
open TernaryCoverFrequency TernaryCoverCapParameters
open scoped Topology
set_option maxHeartbeats 1000000

theorem native_crude_upper {K : ℕ} (hK : 0 < K) (m : ℕ) :
    nativePrime K m ≤ 2^(4*fixedLength m+2) := by
  have hM := vertices_upper (fixedLength m) (fixedPi m)
  have hR : partitionCap m ≤ 3^fixedLength m := by
    have hp := Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) (fixedPi m 1)
    have ht : fixedPi m 1+fixedPi m 2 ≤ fixedLength m := by have := fixedPi_total m; omega
    exact (Nat.mul_le_mul_right _ hp).trans (by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) ht)
  have hS : inflation K m ≤ 3^fixedLength m :=
    (rootCeiling_le hK (outputSize_pos m)).trans hM
  have hb : nativePrime K m^2 ≤ 16*(3^fixedLength m)^4 := by
    have h := nativePrime_upper hK m
    have hh := Nat.mul_le_mul_left 16 (Nat.mul_le_mul (Nat.mul_le_mul hM hR) (Nat.pow_le_pow_left hS 2))
    exact h.trans (by simpa only [inflatedThreshold,threshold,partitionCap,← pow_add,
      show (3^fixedLength m)*(3^fixedLength m)=(3^fixedLength m)^2 by ring] using hh)
  have hp : nativePrime K m ≤ 4*(3^fixedLength m)^2 := by nlinarith
  calc
    _ ≤ 4*(3^fixedLength m)^2 := hp
    _ ≤ 4*((2^2)^fixedLength m)^2 := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (Nat.pow_le_pow_left (by decide) _) 2)
    _ = _ := by rw [← pow_mul,← pow_mul,show (4 : ℕ)=2^2 by norm_num,← pow_add]; congr 1; ring

theorem native_source_cap_upper (K m : ℕ) :
    sourceCap m (nativePrime K m) ≤ 2^(2*fixedLength m+4) := by
  have hp := (nativePrime_prime K m).pos
  have hv : (fieldVertices (fixedLength m) (nativePrime K m) (fixedAlpha m)).card ≤ 3^fixedLength m :=
    Finset.card_image_le.trans (vertices_upper _ _)
  have h1 : 1 ≤ 3^fixedLength m := Nat.one_le_pow _ _ (by decide)
  have hcap : sourceCap m (nativePrime K m) ≤ 16*3^fixedLength m := by
    apply (ceilDiv_le_iff_le_mul hp).mpr
    have hV := Nat.mul_le_mul_left (3^fixedLength m) hp
    change 8*(nativePrime K m+_) ≤ nativePrime K m*(16*3^fixedLength m)
    nlinarith
  exact hcap.trans (by
    have hh := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by decide : (3 : ℕ) ≤ 2^2) (fixedLength m))
    simpa only [← pow_mul,show (16 : ℕ)=2^4 by norm_num,← pow_add,
      show 4+2*fixedLength m=2*fixedLength m+4 by omega] using hh)

theorem native_cap_exponent_bound {K : ℕ} (hK : 0 < K) (m k : ℕ) :
    k*capExponent (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
      20*fixedLength m+8*k^2+26+k := by
  have hp := log2_le_of_le_pow (native_crude_upper hK m)
  have hB := log2_le_of_le_pow (native_source_cap_upper K m)
  have hb : capBudget (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
      20*fixedLength m+8*k^2+26 := by unfold capBudget; omega
  have hd := Nat.div_mul_le_self (capBudget (nativePrime K m) (sourceCap m (nativePrime K m)) k+k-1) k
  rw [Nat.mul_comm] at hd
  unfold capExponent
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

def baseFrequency (K m : ℕ) : ℕ := frequencyFactor m*(Nat.log2 (nativePrime K m^2)+1)
def baseFactor (K k c d m : ℕ) : ℕ :=
  (max 1 c)*(fixedLength m+1)^d*baseFrequency K m*
    rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k

theorem frequency_factor_upper (m : ℕ) : frequencyFactor m ≤ 2^42*(fixedLength m+1)^6 := by
  have hD : TernaryPartitionCount.partitionLoss (7930175*m) (978249*m) ≤ (fixedLength m+1)^3 := by
    unfold TernaryPartitionCount.partitionLoss fixedLength
    have h1 : 2*(7930175*m)+1 ≤ 100000000*m+1 := by omega
    have h2 : 3*(978249*m)+1 ≤ 100000000*m+1 := by omega
    have h3 : 2*(978249*m)+1 ≤ 100000000*m+1 := by omega
    simpa only [pow_succ,pow_zero,one_mul] using Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  unfold frequencyFactor
  have h3 : (3 : ℕ)^16 ≤ 2^32 := by norm_num
  calc
    _ ≤ 4*2^32*(16*(fixedLength m+1)^3)^2 :=
      Nat.mul_le_mul (Nat.mul_le_mul_left 4 h3) (Nat.pow_le_pow_left (Nat.mul_le_mul_left 16 hD) 2)
    _ = _ := by rw [mul_pow,← pow_mul]; norm_num; ring

theorem baseFrequency_upper {K : ℕ} (hK : 0 < K) (m : ℕ) :
    baseFrequency K m ≤ 2^235*(m+1)^7 := by
  have hp2 : nativePrime K m^2 ≤ 2^(8*fixedLength m+4) := by
    have h := Nat.pow_le_pow_left (native_crude_upper hK m) 2
    simpa only [← pow_mul,show (4*fixedLength m+2)*2=8*fixedLength m+4 by omega] using h
  have hl := log2_le_of_le_pow hp2
  have ht : Nat.log2 (nativePrime K m^2)+1 ≤ 16*(fixedLength m+1) := by omega
  have hL : fixedLength m+1 ≤ 2^27*(m+1) := by unfold fixedLength; norm_num; omega
  calc
    _ ≤ (2^42*(fixedLength m+1)^6)*(16*(fixedLength m+1)) := Nat.mul_le_mul (frequency_factor_upper m) ht
    _ = 2^46*(fixedLength m+1)^7 := by norm_num; ring
    _ ≤ 2^46*(2^27*(m+1))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 7)
    _ = _ := by rw [mul_pow,← pow_mul,← mul_assoc,← pow_add]

def rateUpper (k c d m : ℕ) : ℝ :=
  (Real.log (max 1 c : ℝ)+(235+27*(d : ℝ))*Real.log 2+
    (d+7 : ℕ)*Real.log (m+1 : ℝ))/((fixedLength m : ℝ)*Real.log 2)+
  20/(k : ℝ)+(8*(k : ℝ)^2+26+k)*Real.log 2/((k : ℝ)*((fixedLength m : ℝ)*Real.log 2))

theorem baseFactor_pos (K k c d m : ℕ) : 0 < baseFactor K k c d m := by
  have hc : 0 < max 1 c := lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left _ _)
  have hF := frequencyFactor_gt_one m
  have hτ := rawThreshold_pos (nativePrime K m) (sourceCap m (nativePrime K m)) k
  unfold baseFactor baseFrequency
  positivity

theorem baseFactor_rate_bound {K k m : ℕ} (hK : 0 < K) (hk : 0 < k) (hm : 0 < m) (c d : ℕ) :
    Real.log (baseFactor K k c d m : ℝ)/((fixedLength m : ℝ)*Real.log 2) ≤ rateUpper k c d m := by
  have hL : fixedLength m+1 ≤ 2^27*(m+1) := by unfold fixedLength; norm_num; omega
  have hp := Nat.mul_le_mul (Nat.mul_le_mul_left (max 1 c) (Nat.pow_le_pow_left hL d)) (baseFrequency_upper hK m)
  have hpoly : (max 1 c)*(fixedLength m+1)^d*baseFrequency K m ≤
      (max 1 c)*2^(235+27*d)*(m+1)^(d+7) := by
    convert hp using 1 <;> rw [mul_pow,← pow_mul,pow_add] <;> ring
  have hbound := Nat.mul_le_mul_right (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k) hpoly
  have hpos : 0 < (baseFactor K k c d m : ℝ) := by exact_mod_cast baseFactor_pos K k c d m
  have hboundN : baseFactor K k c d m ≤ (max 1 c)*2^(235+27*d)*(m+1)^(d+7)*
      rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k := hbound
  have hboundR : (baseFactor K k c d m : ℝ) ≤
      (((max 1 c)*2^(235+27*d)*(m+1)^(d+7)*
        rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ) := by exact_mod_cast hboundN
  have hlog := Real.log_le_log hpos hboundR
  have hc : (0 : ℝ) < max 1 c := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < (1 : ℕ)) (le_max_left 1 c)
  have hmp : (0 : ℝ) < (m+1 : ℕ) := by positivity
  have htpos : (0 : ℝ) < rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k := by
    exact_mod_cast rawThreshold_pos (nativePrime K m) (sourceCap m (nativePrime K m)) k
  rw [Nat.cast_mul,Nat.cast_mul,Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,
    Real.log_mul (by positivity) (by positivity),Real.log_mul (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),Real.log_pow,Real.log_pow] at hlog
  have hτ : Real.log (rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℝ)=
      (capExponent (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℝ)*Real.log 2 := by
    unfold rawThreshold
    rw [Nat.cast_pow,Real.log_pow]
    norm_num
  rw [hτ] at hlog
  have he : (k : ℝ)*(capExponent (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℝ) ≤
      20*(fixedLength m : ℝ)+8*(k : ℝ)^2+26+k := by exact_mod_cast native_cap_exponent_bound hK m k
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hd := denominator_pos hm
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  apply (div_le_iff₀ hd).mpr
  unfold rateUpper
  field_simp [hkR.ne',hLen,log_two_pos.ne']
  push_cast
  push_cast at hlog
  have hlogk := mul_le_mul_of_nonneg_right hlog hkR.le
  have hh := mul_le_mul_of_nonneg_right he log_two_pos.le
  nlinarith

theorem rateUpper_tendsto {k : ℕ} (hk : 0 < k) (c d : ℕ) :
    Tendsto (rateUpper k c d) atTop (𝓝 (20/(k : ℝ))) := by
  have hconst := denominator_atTop.const_div_atTop
    (Real.log (max 1 c : ℝ)+(235+27*(d : ℝ))*Real.log 2)
  have hlog := (BinomialEntropy.logarithmic_error_tendsto_zero (by decide : 0 < (1 : ℕ))).div_const
    (100000000*Real.log 2)
  have hlog' : Tendsto (fun m : ℕ => Real.log (m+1 : ℝ)/((fixedLength m : ℝ)*Real.log 2)) atTop (𝓝 0) := by
    convert hlog using 1
    · funext m
      simp only [fixedLength,Nat.cast_mul,Nat.cast_ofNat,one_mul,div_eq_mul_inv,mul_inv_rev]
      ring
    · simp
  have htail := denominator_atTop.const_div_atTop ((8*(k : ℝ)^2+26+k)*Real.log 2/(k : ℝ))
  have h := ((hconst.add (hlog'.const_mul ((d+7 : ℕ) : ℝ))).add_const (20/(k : ℝ))).add htail
  convert h using 1
  · funext m
    unfold rateUpper
    ring
  · simp

def overheadCharge (k c d m : ℕ) : ℝ := 2*rateUpper k c d m/outputRate m
theorem overhead_charge_tendsto {k : ℕ} (hk : 0 < k) (c d : ℕ) :
    Tendsto (overheadCharge k c d) atTop (𝓝 (40/((k : ℝ)*Hpi))) := by
  have h := ((rateUpper_tendsto hk c d).const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h using 1
  · rfl
  · ring

def selectedMoment (K : ℕ) : ℕ := 100000000*K^2
def microAllowance (K : ℕ) : ℝ := 1/(100*(K : ℝ)^2)

theorem selectedMoment_pos {K : ℕ} (hK : 0 < K) : 0 < selectedMoment K := by
  unfold selectedMoment
  positivity

theorem moment_limit_lt_allowance {K : ℕ} (hK : 0 < K) :
    40/((selectedMoment K : ℝ)*Hpi) < microAllowance K := by
  have hkR : (0 : ℝ) < K := by exact_mod_cast hK
  have hH : (4/5 : ℝ) < Hpi := by linarith [Hpi_bounds.1]
  unfold selectedMoment microAllowance
  push_cast
  apply (div_lt_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [mul_pos (sq_pos_of_pos hkR) (sub_pos.mpr hH)]

theorem small_overhead_eventually {K : ℕ} (hK : 0 < K) (c d : ℕ) :
    ∀ᶠ m : ℕ in atTop, overheadCharge (selectedMoment K) c d m < microAllowance K :=
  (overhead_charge_tendsto (selectedMoment_pos hK) c d).eventually
    (gt_mem_nhds (moment_limit_lt_allowance hK))

theorem common_fixed_block {K : ℕ} (hK : 100000000 ≤ K) (c d N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m < microAllowance K := by
  have hk : 0 < K := by omega
  have h : ∀ᶠ m : ℕ in atTop, N ≤ m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m < microAllowance K := by
    filter_upwards [eventually_ge_atTop N,goodBlock_eventually hK,small_overhead_eventually hk c d] with m hm hg ho
    exact ⟨hm,hg,ho⟩
  exact h.exists

theorem base_factor_prefix_bound {K k m n j : ℕ} (hK : 0 < K) (hk : 0 < k)
    (hm : 0 < m) (hn : 1 < n) (hj : j ≤ radixLength m n) (c d : ℕ) :
    (baseFactor K k c d m : ℝ)^j ≤ (baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hB := baseFactor_pos K k c d m
  have hBr : 0 < (baseFactor K k c d m : ℝ) := by exact_mod_cast hB
  have ha : 0 ≤ Real.log (baseFactor K k c d m : ℝ) := Real.log_nonneg (by exact_mod_cast hB)
  have hb := TernaryPrincipalDimensions.prefix_dimension_bound hM hn hj ha
    (pow_pos hBr _).le (by rw [Real.log_pow] : Real.log ((baseFactor K k c d m : ℝ)^j) ≤
      (j : ℝ)*Real.log (baseFactor K k c d m : ℝ))
  rw [Real.exp_log hBr] at hb
  have hRate := baseFactor_rate_bound hK hk hm c d
  have hln := (div_le_iff₀ (denominator_pos hm)).mp hRate
  have he := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hln (by norm_num : (0 : ℝ) ≤ 2))
    (TernaryPrincipalDimensions.output_log_pos hm).le
  have heq : 2*(rateUpper k c d m*((fixedLength m : ℝ)*Real.log 2))/Real.log (outputSize m : ℝ)=
      overheadCharge k c d m := by
    unfold overheadCharge outputRate
    have hLen : (fixedLength m : ℝ) ≠ 0 := by
      have hh : 0 < fixedLength m := by unfold fixedLength; positivity
      exact_mod_cast hh.ne'
    field_simp [TernaryPrincipalDimensions.output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring
  rw [heq] at he
  exact hb.trans (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) he) hBr.le)

/-- This is the actual repeated polynomial-carry, noninflation-family and
raw-cap factor, with its fixed prefactor absorbed by the strict margin. -/
theorem base_factor_eventually {K k m : ℕ} (hK : 0 < K) (hk : 0 < k) (hm : 0 < m)
    (c d : ℕ) {ε : ℝ} (he : overheadCharge k c d m < ε) :
    ∀ᶠ n : ℕ in atTop,
      ((baseFactor K k c d m)^(radixLength m n) : ℝ) ≤ (n : ℝ)^ε := by
  have h := TernaryRadixOverhead.polynomial_dimension_budget hm 1 (baseFactor K k c d m)
    (overheadCharge k c d m) ε (by norm_num) (Nat.cast_nonneg _) he 0
    (fun n => (baseFactor K k c d m : ℝ)^(radixLength m n))
    (fun n hn => base_factor_prefix_bound hK hk hm hn le_rfl c d)
  simpa only [pow_zero,mul_one,one_mul,Nat.cast_pow] using h

theorem paired_drift_with_slack {K : ℕ} (hK : 100 ≤ K) :
    -1/(K : ℝ)+8/(K : ℝ)^2+20*(K : ℝ)*microAllowance K < 0 := by
  have hk : (100 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : (0 : ℝ) < K := by linarith
  unfold microAllowance
  field_simp [hp.ne']
  nlinarith

theorem final_margin {K : ℕ} (hK : 100000000 ≤ K) :
    softCertificate+microAllowance K < targetExponent := by
  have hk : (100000000 : ℝ) ≤ K := by exact_mod_cast hK
  have hp : (0 : ℝ) < K := by linarith
  have hδ : microAllowance K < (1/10000 : ℝ) := by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  norm_num [softCertificate,targetExponent] at *
  linarith

/-- The exact full native-family length splits into the separately priced
S^4 part and the base factor that includes tau and every carry choice. -/
theorem native_family_factor_bound (K k c d m b : ℕ)
    (hb : b ≤ c*(fixedLength m+1)^d) :
    b*(nativeFamily K m k).length*
      rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k ≤
        (inflation K m)^4*baseFactor K k c d m := by
  have hc : b ≤ (max 1 c)*(fixedLength m+1)^d :=
    hb.trans (Nat.mul_le_mul_right _ (le_max_right _ _))
  have h := Nat.mul_le_mul_right
    ((nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k) hc
  rw [native_family_length] at h
  rw [native_family_length]
  unfold inflatedFrequency baseFactor baseFrequency at *
  convert h using 1 <;> ring

theorem repeated_native_family_factor_bound (K k c d m b r : ℕ)
    (hb : b ≤ c*(fixedLength m+1)^d) :
    (b*(nativeFamily K m k).length*
      rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^r ≤
        (inflation K m)^(4*r)*(baseFactor K k c d m)^r := by
  have h := Nat.pow_le_pow_left (native_family_factor_bound K k c d m b hb) r
  simpa only [mul_pow,← pow_mul] using h

end ThreeSum.TernaryOversizeOverhead
