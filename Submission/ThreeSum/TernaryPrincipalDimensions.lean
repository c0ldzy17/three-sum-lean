import Submission.ThreeSum.TernaryFiniteLedger

/-! Exact radix ceiling overhang for principal physical dimensions.
These statements bound literal cardinalities, not an unassembled solver. -/
noncomputable section
namespace ThreeSum.TernaryPrincipalDimensions
open Real TernaryParameters TernaryEntropyRates TernaryDimensionBounds
open TernaryCoverScale TernaryLocalParameters TernaryFiniteLedger

theorem clog_power_upper {M n : ℕ} (hM : 1 < M) (hn : 1 < n) :
    M^(Nat.clog M (n^2)) ≤ M*n^2 := by
  have hn2 : 1 < n^2 := by nlinarith
  have hpos := Nat.clog_pos hM hn2
  have hl := Nat.pow_pred_clog_lt_self hM hn2
  have he : Nat.clog M (n^2)=(Nat.clog M (n^2)).pred+1 :=
    (Nat.succ_pred_eq_of_pos hpos).symm
  rw [he,pow_succ]
  exact (Nat.mul_le_mul_right M hl.le).trans_eq (Nat.mul_comm _ _)

theorem prefix_linear_bound {M n j : ℕ} (hM : 1 < M) (hn : 1 < n)
    (hj : j ≤ Nat.clog M (n^2)) {a : ℝ} (ha : 0 ≤ a) :
    (j : ℝ)*a ≤ a+(2*a/Real.log M)*Real.log n := by
  have hMr : (1 : ℝ) < M := by exact_mod_cast hM
  have hnr : (1 : ℝ) < n := by exact_mod_cast hn
  have hLM := Real.log_pos hMr
  have hMp : 0 < (M : ℝ) := by linarith
  have hnp : 0 < (n : ℝ) := by linarith
  have hp : (M : ℝ)^(Nat.clog M (n^2)) ≤ (M : ℝ)*(n : ℝ)^2 := by
    exact_mod_cast clog_power_upper hM hn
  have hl := Real.log_le_log (pow_pos hMp _) hp
  rw [Real.log_pow,Real.log_mul hMp.ne' (pow_pos hnp _).ne',Real.log_pow] at hl
  norm_num at hl
  have hji : (j : ℝ) ≤ Nat.clog M (n^2) := by exact_mod_cast hj
  have hh := mul_le_mul_of_nonneg_right hji hLM.le
  have hb := mul_le_mul_of_nonneg_right (hh.trans hl) ha
  have he : a+(2*a/Real.log M)*Real.log n=
      (a*Real.log M+2*a*Real.log n)/Real.log M := by field_simp
  rw [he]
  apply (le_div_iff₀ hLM).mpr
  nlinarith

theorem prefix_dimension_bound {M n j : ℕ} (hM : 1 < M) (hn : 1 < n)
    (hj : j ≤ Nat.clog M (n^2)) {a X : ℝ} (ha : 0 ≤ a) (hX : 0 ≤ X)
    (hlog : Real.log X ≤ (j : ℝ)*a) :
    X ≤ Real.exp a*(n : ℝ)^(2*a/Real.log M) := by
  rcases hX.eq_or_lt with hX | hX
  · rw [← hX]
    positivity
  have hl := hlog.trans (prefix_linear_bound hM hn hj ha)
  calc
    X=Real.exp (Real.log X) := (Real.exp_log hX).symm
    _ ≤ Real.exp (a+(2*a/Real.log M)*Real.log n) := Real.exp_le_exp.mpr hl
    _ = _ := by
      rw [Real.exp_add,Real.rpow_def_of_pos (by exact_mod_cast lt_trans Nat.zero_lt_one hn)]
      congr 2
      ring

theorem output_log_pos {m : ℕ} (hm : 0 < m) : 0 < Real.log (outputSize m : ℝ) :=
  Real.log_pos (by exact_mod_cast lt_of_lt_of_le (by decide : 1 < (16 : ℕ)) (outputSize_ge_sixteen hm))

theorem bank_charge_eq {m : ℕ} (hm : 0 < m) :
    2*((fixedLength m : ℝ)*Real.log 2*bankEntropy)/Real.log (outputSize m : ℝ)=bankCharge m := by
  unfold bankCharge outputRate
  field_simp [output_log_pos hm |>.ne',denominator_pos hm |>.ne']

theorem endpoint_charge_eq {m : ℕ} (hm : 0 < m) :
    2*Real.log (endpointSize m : ℝ)/Real.log (outputSize m : ℝ)=endpointCharge m := by
  unfold endpointCharge endpointRate outputRate
  have hL : (fixedLength m : ℝ) ≠ 0 := by unfold fixedLength; exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm).ne'
  field_simp [output_log_pos hm |>.ne',hL,log_two_pos.ne'] <;> ring

theorem histogram_charge_eq {m : ℕ} (hm : 0 < m) :
    2*Real.log (prime m : ℝ)/Real.log (outputSize m : ℝ)=histogramCharge m := by
  unfold histogramCharge primeRate outputRate
  have hL : (fixedLength m : ℝ) ≠ 0 := by unfold fixedLength; exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm).ne'
  field_simp [output_log_pos hm |>.ne',hL,log_two_pos.ne'] <;> ring

theorem actual_bank_prefix_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (bankSize m j : ℝ) ≤ Real.exp ((fixedLength m : ℝ)*Real.log 2*bankEntropy)*
      (n : ℝ)^bankCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have ha : 0 ≤ (fixedLength m : ℝ)*Real.log 2*bankEntropy := by
    exact mul_nonneg (denominator_pos hm).le analytic_admissibility.1.le
  have hlog := bank_log_bound m j
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*bankEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*bankEntropy) := by unfold fixedLength; push_cast; ring
  rw [he] at hlog
  simpa only [bank_charge_eq hm] using prefix_dimension_bound hM hn hj ha (Nat.cast_nonneg _) hlog

theorem actual_endpoint_prefix_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (endpointSize m : ℝ)^j ≤ (endpointSize m : ℝ)*(n : ℝ)^endpointCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hA : 0 < endpointSize m := by rw [actual_endpoint_count]; exact typeCount_pos (by decide) m
  have hAr : 0 < (endpointSize m : ℝ) := by exact_mod_cast hA
  have ha : 0 ≤ Real.log (endpointSize m : ℝ) := Real.log_nonneg (by exact_mod_cast hA)
  have h := prefix_dimension_bound hM hn hj ha (pow_nonneg (Nat.cast_nonneg _) j)
    (by rw [Real.log_pow] : Real.log ((endpointSize m : ℝ)^j) ≤ (j : ℝ)*Real.log (endpointSize m : ℝ))
  simpa only [Real.exp_log hAr,endpoint_charge_eq hm] using h

theorem actual_histogram_prefix_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) :
    (prime m : ℝ)^j ≤ (prime m : ℝ)*(n : ℝ)^histogramCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hp : 0 < prime m := (prime_prime m).pos
  have hpr : 0 < (prime m : ℝ) := by exact_mod_cast hp
  have ha : 0 ≤ Real.log (prime m : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have h := prefix_dimension_bound hM hn hj ha (pow_nonneg (Nat.cast_nonneg _) j)
    (by rw [Real.log_pow] : Real.log ((prime m : ℝ)^j) ≤ (j : ℝ)*Real.log (prime m : ℝ))
  simpa only [Real.exp_log hpr,histogram_charge_eq hm] using h

def incidenceSlope (m : ℕ) : ℝ := Real.log (outputSize m : ℝ)-Real.log (prime m : ℝ)
def querySlope (m : ℕ) : ℝ := incidenceSlope m+(fixedLength m : ℝ)*Real.log 2*queryEntropy

theorem incidence_slope_pos {m : ℕ} (hm : 0 < m) (hs : primeRate m < outputRate m) :
    0 < incidenceSlope m := by
  have hs' : Real.log (prime m : ℝ)/((fixedLength m : ℝ)*Real.log 2) <
    Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2) := hs
  exact sub_pos.mpr ((div_lt_div_iff_of_pos_right (denominator_pos hm)).mp hs')

theorem query_slope_pos {m : ℕ} (hm : 0 < m) (hs : primeRate m < outputRate m) :
    0 < querySlope m := by
  unfold querySlope
  exact add_pos (incidence_slope_pos hm hs)
    (mul_pos (denominator_pos hm) analytic_admissibility.2.1)

theorem query_charge_eq {m : ℕ} (hm : 0 < m) :
    1+2*querySlope m/Real.log (outputSize m : ℝ)=queryCharge m := by
  unfold queryCharge querySlope incidenceSlope outputRate primeRate
  have hL : (fixedLength m : ℝ) ≠ 0 := by unfold fixedLength; exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm).ne'
  field_simp [output_log_pos hm |>.ne',hL,log_two_pos.ne'] <;> ring

theorem incidence_charge_eq {m : ℕ} (hm : 0 < m) :
    1+2*incidenceSlope m/Real.log (outputSize m : ℝ)=incidenceCharge m := by
  unfold incidenceCharge incidenceSlope outputRate primeRate
  have hL : (fixedLength m : ℝ) ≠ 0 := by unfold fixedLength; exact_mod_cast (Nat.mul_pos (by decide : 0 < 100000000) hm).ne'
  field_simp [output_log_pos hm |>.ne',hL,log_two_pos.ne'] <;> ring

/-- The literal wanted-volume/query-dimension expression, including its
exact +1 boundary factor. A caller must separately prove that an executed
enumerator has at most this many wanted copies. -/
theorem query_dimension_expression_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m)
    (Q : TernaryJointType.TritWord (fixedLength (j*m)))
    (hQ : TernaryJointType.HasType Q (fixedPi (j*m))) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j*
      (TernaryBank.nearWords Q (queryDeficit m j)).card ≤
      (Real.exp (querySlope m)/z)*(n : ℝ)^queryCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hMr : 0 < (outputSize m : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hM
  have hpr : 0 < (prime m : ℝ) := by exact_mod_cast (prime_prime m).pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hz := gibbs_parameters.2.2.1
  have hratio := div_pos hMr hpr
  have hc : 0 < ((TernaryBank.nearWords Q (queryDeficit m j)).card : ℝ) := by
    exact_mod_cast near_pos Q (queryDeficit m j)
  have hq := query_log_bound Q hQ
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*queryEntropy) := by unfold fixedLength; push_cast; ring
  rw [he] at hq
  have hlog : Real.log (z*((outputSize m : ℝ)/prime m)^j*
      (TernaryBank.nearWords Q (queryDeficit m j)).card) ≤ (j : ℝ)*querySlope m := by
    rw [Real.log_mul (mul_pos hz (pow_pos hratio _)).ne' hc.ne',
      Real.log_mul hz.ne' (pow_pos hratio _).ne',Real.log_pow,Real.log_div hMr.ne' hpr.ne']
    unfold querySlope incidenceSlope
    nlinarith
  have hb := prefix_dimension_bound hM hn hj (query_slope_pos hm hs).le
    (mul_pos (mul_pos hz (pow_pos hratio _)) hc).le hlog
  calc
    _ = ((n : ℝ)/z)*(z*((outputSize m : ℝ)/prime m)^j*
      (TernaryBank.nearWords Q (queryDeficit m j)).card) := by field_simp <;> ring
    _ ≤ ((n : ℝ)/z)*(Real.exp (querySlope m)*(n : ℝ)^(2*querySlope m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_pos hnR hz).le
    _ = _ := by
      rw [← query_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]
      ring

theorem incidence_dimension_expression_bound {m n j : ℕ} (hm : 0 < m) (hn : 1 < n)
    (hj : j ≤ radixLength m n) (hs : primeRate m < outputRate m) :
    (n : ℝ)*((outputSize m : ℝ)/prime m)^j ≤
      Real.exp (incidenceSlope m)*(n : ℝ)^incidenceCharge m := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hMr : 0 < (outputSize m : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hM
  have hpr : 0 < (prime m : ℝ) := by exact_mod_cast (prime_prime m).pos
  have hnR : 0 < (n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hratio := div_pos hMr hpr
  have hlog : Real.log (((outputSize m : ℝ)/prime m)^j) ≤ (j : ℝ)*incidenceSlope m := by
    rw [Real.log_pow,Real.log_div hMr.ne' hpr.ne']
    rfl
  have hb := prefix_dimension_bound hM hn hj (incidence_slope_pos hm hs).le (pow_pos hratio _).le hlog
  calc
    _ ≤ (n : ℝ)*(Real.exp (incidenceSlope m)*(n : ℝ)^(2*incidenceSlope m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb hnR.le
    _ = _ := by rw [← incidence_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring

end ThreeSum.TernaryPrincipalDimensions
