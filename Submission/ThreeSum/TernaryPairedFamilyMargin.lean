import Submission.ThreeSum.TernaryPairedNativeDrift
import Submission.ThreeSum.TernarySignedParameters

noncomputable section
namespace ThreeSum.TernaryPairedFamilyMargin
open Filter Real TernaryOversizeOverhead TernaryOversizeRates TernaryOversizePrime
open TernaryEntropyRates TernaryLocalParameters TernaryCoverScale TernaryParameters
open scoped Topology
set_option maxHeartbeats 1000000

def baseRate (m : ℕ) : ℝ :=
  (Real.log 9+235*Real.log 2+7*Real.log (m+1 : ℝ))/((fixedLength m : ℝ)*Real.log 2)

theorem baseRate_tendsto : Tendsto baseRate atTop (𝓝 0) := by
  have hc := denominator_atTop.const_div_atTop (Real.log 9+235*Real.log 2)
  have hl := (BinomialEntropy.logarithmic_error_tendsto_zero (by decide : 0<(1 : ℕ))).div_const
    (100000000*Real.log 2)
  have hl' : Tendsto (fun m : ℕ => Real.log (m+1 : ℝ)/((fixedLength m : ℝ)*Real.log 2)) atTop (𝓝 0) := by
    convert hl using 1
    · funext m
      simp only [fixedLength,Nat.cast_mul,Nat.cast_ofNat,one_mul,div_eq_mul_inv,mul_inv_rev]
      ring
    · simp
  convert hc.add (hl'.const_mul 7) using 1
  · funext m
    unfold baseRate
    ring
  · simp

theorem family_log_bound {K m : ℕ} (hK : 0<K) (hm : 0<m) (k : ℕ) :
    Real.log (9*(nativeFamily K m k).length : ℝ)/((fixedLength m : ℝ)*Real.log 2) ≤
      baseRate m+4*inflationRate K m := by
  have hF : (nativeFamily K m k).length=baseFrequency K m*(inflation K m)^4 := by
    rw [native_family_length]
    unfold baseFrequency inflatedFrequency
    ring
  have hb := baseFrequency_upper hK m
  have hb' : 9*(nativeFamily K m k).length≤9*2^235*(m+1)^7*(inflation K m)^4 := by
    rw [hF]
    nlinarith [Nat.mul_le_mul_left (9*(inflation K m)^4) hb]
  have hp : 0<(nativeFamily K m k).length := by
    rw [native_family_length]
    exact Nat.mul_pos (Nat.mul_pos (by have := TernaryCoverCapParameters.frequencyFactor_gt_one m; omega)
      (pow_pos (inflation_pos hK m) 4)) (Nat.succ_pos _)
  have hlog := Real.log_le_log (by exact_mod_cast (by omega : 0<9*(nativeFamily K m k).length))
    (show (9*(nativeFamily K m k).length : ℝ)≤
      (9 : ℝ)*2^235*(m+1 : ℝ)^7*(inflation K m : ℝ)^4 by exact_mod_cast hb')
  have hmR : (0 : ℝ)<(m : ℝ)+1 := by positivity
  have hsR : (0 : ℝ) < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hexpr : Real.log ((9 : ℝ)*2^235*(m+1 : ℝ)^7*(inflation K m : ℝ)^4)=
      Real.log 9+235*Real.log 2+7*Real.log (m+1 : ℝ)+4*Real.log (inflation K m : ℝ) := by
    rw [Real.log_mul (by positivity) (pow_ne_zero _ hsR.ne'),
      Real.log_mul (by positivity) (pow_ne_zero _ hmR.ne'),
      Real.log_mul (by norm_num) (by norm_num)]
    simp only [Real.log_pow]
    norm_num
  rw [hexpr] at hlog
  apply (div_le_iff₀ (denominator_pos hm)).mpr
  have he : (baseRate m+4*inflationRate K m)*((fixedLength m : ℝ)*Real.log 2)=
      Real.log 9+235*Real.log 2+7*Real.log (m+1 : ℝ)+4*Real.log (inflation K m : ℝ) := by
    unfold baseRate inflationRate
    have hLen : (fixedLength m : ℝ)≠0 := by
      have hh : 0 < fixedLength m := by unfold fixedLength; omega
      exact_mod_cast hh.ne'
    field_simp [hLen,log_two_pos.ne']
  rw [he]
  exact hlog

theorem family_fourth_eventually {K : ℕ} (hK : 16<K) (k : ℕ) :
    ∀ᶠ m : ℕ in atTop, (9*(nativeFamily K m k).length)^4≤outputSize m := by
  have hk : 0<K := by omega
  have hlim := ((baseRate_tendsto.add ((inflation_rate_tendsto hk).const_mul 4)).const_mul 4).sub actual_output_rate
  have hneg : 4*(0+4*(Hpi/(K : ℝ)))-Hpi<0 := by
    have hkr : (16 : ℝ)<K := by exact_mod_cast hK
    have hkp : (0 : ℝ)<K := by positivity
    apply (sub_neg).mpr
    field_simp [hkp.ne']
    nlinarith [Hpi_pos]
  have hsmall := hlim.eventually (gt_mem_nhds hneg)
  filter_upwards [hsmall,eventually_gt_atTop (0 : ℕ)] with m hsmall hm
  have hb := family_log_bound hk hm k
  have hd := denominator_pos hm
  have hout := outputSize_pos m
  have hf : 0<(nativeFamily K m k).length := by
    rw [native_family_length]
    exact Nat.mul_pos (Nat.mul_pos (by have := TernaryCoverCapParameters.frequencyFactor_gt_one m; omega)
      (pow_pos (inflation_pos hk m) 4)) (Nat.succ_pos _)
  have hlog : 4*Real.log (9*(nativeFamily K m k).length : ℝ)≤Real.log (outputSize m : ℝ) := by
    unfold outputRate at hsmall
    have hh : 4*(Real.log (9*(nativeFamily K m k).length : ℝ)/((fixedLength m : ℝ)*Real.log 2)) <
        Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2) := by linarith
    have hh' := (div_lt_div_iff_of_pos_right hd).mp (show
      (4*Real.log (9*(nativeFamily K m k).length : ℝ))/((fixedLength m : ℝ)*Real.log 2)<
        Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2) by convert hh using 1 <;> ring)
    exact hh'.le
  have hr : (9*(nativeFamily K m k).length : ℝ)^4≤(outputSize m : ℝ) := by
    apply (Real.log_le_log_iff (by positivity) (by exact_mod_cast hout)).mp
    rw [Real.log_pow]
    norm_num
    exact hlog
  exact_mod_cast hr

/-- One fixed native block satisfies the exact paired drift guard together
with the original signed preprocessing and all principal exponent margins. -/
theorem simultaneous_parameters {K : ℕ} (hK : 100000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      TernarySignedPadding.carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m := by
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp (family_fourth_eventually (by omega : 16<K) (selectedMoment K))
  obtain ⟨t,m,ht,hm,hg,ho,hc,hminor,hp⟩ :=
    TernarySignedParameters.simultaneous_parameters hK hκ c d (max N N₀)
  exact ⟨t,m,ht,(le_max_left N N₀).trans hm,hg,ho,hc,hminor,hp,
    hN₀ m ((le_max_right N N₀).trans hm)⟩

end ThreeSum.TernaryPairedFamilyMargin
