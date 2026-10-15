import Submission.ThreeSum.TernaryOversizeOverhead

/-! Literal larger-field query volume and separately repeated S^4 family. -/
noncomputable section
namespace ThreeSum.TernaryOversizeDimensions
open Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open TernaryLocalParameters TernaryOversizePrime TernaryOversizeRates
open TernaryPrincipalDimensions TernaryDimensionBounds TernaryJointType

def querySlope (K m : ℕ) : ℝ := Real.log (nativePrime K m : ℝ)-Real.log (partitionCap m : ℝ)+
  4*Real.log (inflation K m : ℝ)+(fixedLength m : ℝ)*Real.log 2*queryEntropy
def bankSlope (K m : ℕ) : ℝ := 4*Real.log (inflation K m : ℝ)+
  (fixedLength m : ℝ)*Real.log 2*bankEntropy

theorem query_charge_eq {K m : ℕ} (hm : 0 < m) :
    1+2*querySlope K m/Real.log (outputSize m : ℝ)=TernaryOversizeRates.queryCharge K m := by
  unfold TernaryOversizeRates.queryCharge querySlope familyCharge outputRate nativeRate inflationRate
  rw [partition_log]
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  field_simp [output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring

theorem bank_charge_eq {K m : ℕ} (hm : 0 < m) :
    2*bankSlope K m/Real.log (outputSize m : ℝ)=TernaryOversizeRates.bankCharge K m := by
  unfold TernaryOversizeRates.bankCharge bankSlope familyCharge outputRate inflationRate
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  field_simp [output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring

theorem partition_le_native {K : ℕ} (hK : 0 < K) (m : ℕ) : partitionCap m ≤ nativePrime K m :=
  TernaryTypeLowerBound.partition_cap_le_prime (fixedPi m) (fixedPi_total m) (fixedPi_space m)
    (nativePrime K m) (nativePrime_base_lower hK m)

theorem query_slope_nonneg {K m : ℕ} (hK : 0 < K) (hm : 0 < m) : 0 ≤ querySlope K m := by
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hs : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have hpR : (partitionCap m : ℝ) ≤ (nativePrime K m : ℝ) := by exact_mod_cast partition_le_native hK m
  have hp := Real.log_le_log hR hpR
  unfold querySlope
  have hQ := mul_pos (denominator_pos hm) analytic_admissibility.2.1
  linarith

/-- S^4 is the nonpolynomial part of the actual native greedy family.
The remaining family factor, all polynomial carry choices and tau are in
TernaryOversizeOverhead.baseFactor. -/
theorem actual_bank_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (inflation K m : ℝ)^(4*j)*(bankSize m j : ℝ) ≤
      Real.exp (bankSlope K m)*(n : ℝ)^TernaryOversizeRates.bankCharge K m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hB : 0 < (bankSize m j : ℝ) := by exact_mod_cast bank_pos (fixedLength (j*m)) (bankCut m j)
  have hSlog : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have ha : 0 ≤ bankSlope K m := by
    unfold bankSlope
    have h := mul_pos (denominator_pos hm) analytic_admissibility.1
    linarith
  have hb := bank_log_bound m j
  have hlog : Real.log ((inflation K m : ℝ)^(4*j)*(bankSize m j : ℝ)) ≤ (j : ℝ)*bankSlope K m := by
    rw [Real.log_mul (pow_pos hS _).ne' hB.ne',Real.log_pow]
    unfold bankSlope fixedLength at *
    push_cast at *
    nlinarith
  simpa only [bank_charge_eq hm] using prefix_dimension_bound hM hn hj ha
    (mul_pos (pow_pos hS _) hB).le hlog

/-- This uses the literal p/Rbar output-fiber volume. It does not replace
that volume by M/p when the native field is larger. -/
theorem actual_query_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      (TernaryBank.nearWords Q (queryDeficit m j)).card ≤
      (Real.exp (querySlope K m)/z)*(n : ℝ)^TernaryOversizeRates.queryCharge K m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hp : 0 < (nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hnR : (0 : ℝ) < n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hz := gibbs_parameters.2.2.1
  have hratio := div_pos hp hR
  have hc : 0 < ((TernaryBank.nearWords Q (queryDeficit m j)).card : ℝ) := by exact_mod_cast near_pos Q _
  have hq := query_log_bound Q hQ
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*queryEntropy) := by unfold fixedLength; push_cast; ring
  rw [he] at hq
  have hlog : Real.log (z*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      (TernaryBank.nearWords Q (queryDeficit m j)).card) ≤ (j : ℝ)*querySlope K m := by
    rw [Real.log_mul (mul_pos (mul_pos hz (pow_pos hratio _)) (pow_pos hS _)).ne' hc.ne',
      Real.log_mul (mul_pos hz (pow_pos hratio _)).ne' (pow_pos hS _).ne',
      Real.log_mul hz.ne' (pow_pos hratio _).ne',Real.log_pow,Real.log_pow,Real.log_div hp.ne' hR.ne']
    unfold querySlope
    push_cast
    nlinarith
  have hb := prefix_dimension_bound hM hn hj (query_slope_nonneg hK hm)
    (mul_pos (mul_pos (mul_pos hz (pow_pos hratio _)) (pow_pos hS _)) hc).le hlog
  calc
    _ = ((n : ℝ)/z)*(z*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      (TernaryBank.nearWords Q (queryDeficit m j)).card) := by field_simp <;> ring
    _ ≤ ((n : ℝ)/z)*(Real.exp (querySlope K m)*(n : ℝ)^(2*querySlope K m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_pos hnR hz).le
    _ = _ := by rw [← query_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring

def tableSlope (K m t : ℕ) : ℝ := 4*Real.log (inflation K m : ℝ)+Real.log (t : ℝ)

theorem actual_table_volume {K m n j t : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (ht : 0 < t) :
    (inflation K m : ℝ)^(4*j)*(t : ℝ)^j ≤ Real.exp (tableSlope K m t)*
      (n : ℝ)^(2*tableSlope K m t/Real.log (outputSize m : ℝ)) := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have htR : 0 < (t : ℝ) := by exact_mod_cast ht
  have hSlog : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have htlog : 0 ≤ Real.log (t : ℝ) := Real.log_nonneg (by exact_mod_cast ht)
  have ha : 0 ≤ tableSlope K m t := by unfold tableSlope; positivity
  have hlog : Real.log ((inflation K m : ℝ)^(4*j)*(t : ℝ)^j) ≤ (j : ℝ)*tableSlope K m t := by
    rw [Real.log_mul (pow_pos hS _).ne' (pow_pos htR _).ne',Real.log_pow,Real.log_pow]
    unfold tableSlope
    push_cast
    nlinarith
  exact prefix_dimension_bound hM hn hj ha (mul_pos (pow_pos hS _) (pow_pos htR _)).le hlog

theorem endpoint_charge_eq {K m : ℕ} (hm : 0 < m) :
    2*tableSlope K m (endpointSize m)/Real.log (outputSize m : ℝ)=TernaryOversizeRates.endpointCharge K m := by
  unfold TernaryOversizeRates.endpointCharge tableSlope familyCharge outputRate endpointRate inflationRate
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  field_simp [output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring

theorem histogram_charge_eq {K m : ℕ} (hm : 0 < m) :
    2*tableSlope K m (nativePrime K m)/Real.log (outputSize m : ℝ)=TernaryOversizeRates.histogramCharge K m := by
  unfold TernaryOversizeRates.histogramCharge tableSlope familyCharge outputRate nativeRate inflationRate
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  field_simp [output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring

theorem actual_endpoint_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (inflation K m : ℝ)^(4*j)*(endpointSize m : ℝ)^j ≤
      Real.exp (tableSlope K m (endpointSize m))*(n : ℝ)^TernaryOversizeRates.endpointCharge K m := by
  have ht : 0 < endpointSize m := by rw [actual_endpoint_count]; exact typeCount_pos (by decide) m
  simpa only [endpoint_charge_eq hm] using actual_table_volume hK hm hn hj ht

theorem actual_histogram_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (inflation K m : ℝ)^(4*j)*(nativePrime K m : ℝ)^j ≤
      Real.exp (tableSlope K m (nativePrime K m))*(n : ℝ)^TernaryOversizeRates.histogramCharge K m := by
  simpa only [histogram_charge_eq hm] using actual_table_volume hK hm hn hj (nativePrime_prime K m).pos

def incidenceSlope (K m : ℕ) : ℝ := Real.log (nativePrime K m : ℝ)-Real.log (partitionCap m : ℝ)+
  4*Real.log (inflation K m : ℝ)

theorem incidence_charge_eq {K m : ℕ} (hm : 0 < m) :
    1+2*incidenceSlope K m/Real.log (outputSize m : ℝ)=TernaryOversizeRates.incidenceCharge K m := by
  unfold TernaryOversizeRates.incidenceCharge incidenceSlope familyCharge outputRate nativeRate inflationRate
  rw [partition_log]
  have hLen : (fixedLength m : ℝ) ≠ 0 := by
    have hh : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hh.ne'
  field_simp [output_log_pos hm |>.ne',hLen,log_two_pos.ne'] <;> ring

theorem actual_incidence_volume {K m n j : ℕ} (hK : 0 < K) (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j) ≤
      Real.exp (incidenceSlope K m)*(n : ℝ)^TernaryOversizeRates.incidenceCharge K m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hp : 0 < (nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0 < (inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hnR : (0 : ℝ) < n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hpR : (partitionCap m : ℝ) ≤ (nativePrime K m : ℝ) := by exact_mod_cast partition_le_native hK m
  have hslog : 0 ≤ Real.log (inflation K m : ℝ) := Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have hplog := Real.log_le_log hR hpR
  have ha : 0 ≤ incidenceSlope K m := by unfold incidenceSlope; linarith
  have hratio := div_pos hp hR
  have hlog : Real.log (((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)) ≤
      (j : ℝ)*incidenceSlope K m := by
    rw [Real.log_mul (pow_pos hratio _).ne' (pow_pos hS _).ne',Real.log_pow,Real.log_pow,Real.log_div hp.ne' hR.ne']
    unfold incidenceSlope
    push_cast
    nlinarith
  have hb := prefix_dimension_bound hM hn hj ha (mul_pos (pow_pos hratio _) (pow_pos hS _)).le hlog
  calc
    _ = (n : ℝ)*(((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)) := by ring
    _ ≤ (n : ℝ)*(Real.exp (incidenceSlope K m)*(n : ℝ)^(2*incidenceSlope K m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb hnR.le
    _ = _ := by rw [← incidence_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring

end ThreeSum.TernaryOversizeDimensions
