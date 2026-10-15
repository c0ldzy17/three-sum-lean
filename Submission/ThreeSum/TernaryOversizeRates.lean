import Submission.ThreeSum.TernaryOversizePrime
import Submission.ThreeSum.TernaryFiniteLedger

/-! Actual oversized-field rates and the separately charged family growth. -/
noncomputable section
namespace ThreeSum.TernaryOversizeRates
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open TernaryLocalParameters TernaryOversizePrime
open scoped Topology
set_option maxHeartbeats 1000000

def inflationRate (K m : ℕ) : ℝ := Real.log (inflation K m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def nativeRate (K m : ℕ) : ℝ := Real.log (nativePrime K m : ℝ)/((fixedLength m : ℝ)*Real.log 2)

theorem denominator_atTop :
    Tendsto (fun m : ℕ => (fixedLength m : ℝ)*Real.log 2) atTop atTop := by
  have h := (tendsto_natCast_atTop_atTop (R := ℝ)).const_mul_atTop
    (mul_pos (by norm_num : (0 : ℝ) < 100000000) log_two_pos)
  convert h using 1
  funext m
  simp only [fixedLength,Nat.cast_mul]
  ring

theorem inflation_rate_bounds {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    outputRate m/K ≤ inflationRate K m ∧
      inflationRate K m ≤ outputRate m/K+Real.log 2/((fixedLength m : ℝ)*Real.log 2) := by
  have hMr : 0 < (outputSize m : ℝ) := by exact_mod_cast outputSize_pos m
  have hSr : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hl : (outputSize m : ℝ) ≤ (inflation K m : ℝ)^K := by exact_mod_cast inflation_lower hK m
  have hu : (inflation K m : ℝ)^K ≤ (2 : ℝ)^K*(outputSize m : ℝ) := by exact_mod_cast inflation_upper hK m
  have hlo := Real.log_le_log hMr hl
  have hup := Real.log_le_log (pow_pos hSr _) hu
  rw [Real.log_pow] at hlo
  rw [Real.log_pow,Real.log_mul (pow_pos (by norm_num : (0 : ℝ) < 2) _).ne' hMr.ne',Real.log_pow] at hup
  have hkR : (0 : ℝ) < K := by exact_mod_cast hK
  have hd := denominator_pos hm
  have hL : (fixedLength m : ℝ) ≠ 0 := by
    have hLp : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hLp.ne'
  unfold outputRate inflationRate
  constructor
  · apply (le_div_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne',hkR.ne']
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne',hkR.ne']
    nlinarith

theorem inflation_rate_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (inflationRate K) atTop (𝓝 (Hpi/K)) := by
  have hl := actual_output_rate.div_const (K : ℝ)
  have hu := hl.add (denominator_atTop.const_div_atTop (Real.log 2))
  have hb : ∀ᶠ m : ℕ in atTop, outputRate m/K ≤ inflationRate K m ∧
      inflationRate K m ≤ outputRate m/K+Real.log 2/((fixedLength m : ℝ)*Real.log 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact inflation_rate_bounds hK hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl (by simpa using hu)
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

theorem native_rate_bounds {K m : ℕ} (hK : 0 < K) (hm : 0 < m) :
    (outputRate m+partitionEntropy)/2+inflationRate K m ≤ nativeRate K m ∧
    nativeRate K m ≤ (outputRate m+partitionEntropy)/2+inflationRate K m+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by
  have hM : 0 < (outputSize m : ℝ) := by exact_mod_cast outputSize_pos m
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hp : 0 < (nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hlo : ((outputSize m : ℝ)*(partitionCap m : ℝ))*(inflation K m : ℝ)^2 ≤ (nativePrime K m : ℝ)^2 := by
    exact_mod_cast nativePrime_lower K m
  have hup : (nativePrime K m : ℝ)^2 ≤ 16*(((outputSize m : ℝ)*(partitionCap m : ℝ))*(inflation K m : ℝ)^2) := by
    exact_mod_cast nativePrime_upper hK m
  have hl := Real.log_le_log (mul_pos (mul_pos hM hR) (pow_pos hS _)) hlo
  have hu := Real.log_le_log (pow_pos hp 2) hup
  rw [Real.log_mul (mul_pos hM hR).ne' (pow_pos hS _).ne',Real.log_mul hM.ne' hR.ne',
    Real.log_pow,Real.log_pow,partition_log] at hl
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (mul_pos (mul_pos hM hR) (pow_pos hS _)).ne',
    Real.log_mul (mul_pos hM hR).ne' (pow_pos hS _).ne',Real.log_mul hM.ne' hR.ne',
    Real.log_pow,Real.log_pow,partition_log] at hu
  norm_num at hl hu
  have hd := denominator_pos hm
  have hL : (fixedLength m : ℝ) ≠ 0 := by
    have hLp : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hLp.ne'
  unfold outputRate nativeRate inflationRate
  constructor
  · apply (le_div_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne']
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    field_simp [hL,log_two_pos.ne']
    nlinarith

theorem native_rate_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (nativeRate K) atTop (𝓝 ((Hpi+partitionEntropy)/2+Hpi/K)) := by
  have hl := ((actual_output_rate.add_const partitionEntropy).div_const 2).add (inflation_rate_tendsto hK)
  have hu := hl.add prime_rate_error_tendsto
  have hb : ∀ᶠ m : ℕ in atTop,
      (outputRate m+partitionEntropy)/2+inflationRate K m ≤ nativeRate K m ∧
      nativeRate K m ≤ (outputRate m+partitionEntropy)/2+inflationRate K m+
        Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact native_rate_bounds hK hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl (by simpa using hu)
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

/-- The S^4 component of every selected map family is paid separately. -/
def familyCharge (K m : ℕ) : ℝ := 8*inflationRate K m/outputRate m
def bankCharge (K m : ℕ) : ℝ := 2*bankEntropy/outputRate m+familyCharge K m
def queryCharge (K m : ℕ) : ℝ := 1+2*(nativeRate K m-partitionEntropy+queryEntropy)/outputRate m+familyCharge K m
def endpointCharge (K m : ℕ) : ℝ := 2*endpointRate m/outputRate m+familyCharge K m
def histogramCharge (K m : ℕ) : ℝ := 2*nativeRate K m/outputRate m+familyCharge K m
def incidenceCharge (K m : ℕ) : ℝ := 1+2*(nativeRate K m-partitionEntropy)/outputRate m+familyCharge K m

theorem family_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (familyCharge K) atTop (𝓝 (8/(K : ℝ))) := by
  have h := ((inflation_rate_tendsto hK).const_mul 8).div actual_output_rate Hpi_pos.ne'
  convert h using 1
  · rfl
  · field_simp [Hpi_pos.ne']

theorem bank_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (bankCharge K) atTop (𝓝 (2*bankEntropy/Hpi+8/K)) :=
  TernaryFiniteLedger.bank_charge_tendsto.add (family_charge_tendsto hK)

theorem endpoint_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (endpointCharge K) atTop (𝓝 (2*Halpha/Hpi+8/K)) :=
  TernaryFiniteLedger.endpoint_charge_tendsto.add (family_charge_tendsto hK)

theorem query_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (queryCharge K) atTop (𝓝 (2-partitionEntropy/Hpi+2*queryEntropy/Hpi+10/K)) := by
  have h := ((((native_rate_tendsto hK).sub_const partitionEntropy).add_const queryEntropy).const_mul 2).div actual_output_rate Hpi_pos.ne'
  have hh := (h.const_add 1).add (family_charge_tendsto hK)
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne'] <;> ring

theorem histogram_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (histogramCharge K) atTop (𝓝 (1+partitionEntropy/Hpi+10/K)) := by
  have h := ((native_rate_tendsto hK).const_mul 2).div actual_output_rate Hpi_pos.ne'
  have hh := h.add (family_charge_tendsto hK)
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne'] <;> ring

theorem incidence_charge_tendsto {K : ℕ} (hK : 0 < K) :
    Tendsto (incidenceCharge K) atTop (𝓝 (2-partitionEntropy/Hpi+10/K)) := by
  have h := (((native_rate_tendsto hK).sub_const partitionEntropy).const_mul 2).div actual_output_rate Hpi_pos.ne'
  have hh := (h.const_add 1).add (family_charge_tendsto hK)
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne'] <;> ring

def softCertificate : ℝ := 4801/2500
def GoodBlock (K m : ℕ) : Prop := 0 < m ∧ bankCharge K m<softCertificate ∧
  queryCharge K m<softCertificate ∧ endpointCharge K m<softCertificate ∧
  histogramCharge K m<softCertificate ∧ incidenceCharge K m<softCertificate

theorem goodBlock_eventually {K : ℕ} (hK : 100000000 ≤ K) :
    ∀ᶠ m : ℕ in atTop, GoodBlock K m := by
  have hk : 0 < K := by omega
  have hkR : (0 : ℝ) < K := by exact_mod_cast hk
  have hkR' : (100000000 : ℝ) ≤ K := by exact_mod_cast hK
  have h8 : 8/(K : ℝ) < (1/10000 : ℝ) := (div_lt_iff₀ hkR).mpr (by linarith)
  have h10 : 10/(K : ℝ) < (1/10000 : ℝ) := (div_lt_iff₀ hkR).mpr (by linarith)
  obtain ⟨hB,hQ,hA,hP,hI⟩ := ledger_individual_bounds
  have he : certificateExponent+(1/10000 : ℝ)=softCertificate := by norm_num [certificateExponent,softCertificate]
  have hb : 2*bankEntropy/Hpi+8/K<softCertificate := by linarith
  have hq : 2-partitionEntropy/Hpi+2*queryEntropy/Hpi+10/K<softCertificate := by linarith
  have ha : 2*Halpha/Hpi+8/K<softCertificate := by linarith
  have hp : 1+partitionEntropy/Hpi+10/K<softCertificate := by linarith
  have hi : 2-partitionEntropy/Hpi+10/K<softCertificate := by linarith
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    (bank_charge_tendsto hk).eventually (gt_mem_nhds hb),
    (query_charge_tendsto hk).eventually (gt_mem_nhds hq),
    (endpoint_charge_tendsto hk).eventually (gt_mem_nhds ha),
    (histogram_charge_tendsto hk).eventually (gt_mem_nhds hp),
    (incidence_charge_tendsto hk).eventually (gt_mem_nhds hi)] with m hm hB hQ hA hP hI
  exact ⟨hm,hB,hQ,hA,hP,hI⟩

theorem soft_certificate_margin : targetExponent-softCertificate=(3/5000 : ℝ) := by
  norm_num [targetExponent,softCertificate]

end ThreeSum.TernaryOversizeRates
