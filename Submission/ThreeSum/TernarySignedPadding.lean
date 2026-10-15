import Submission.ThreeSum.TernarySignedReduction
import Submission.ThreeSum.TernaryOversizeOverhead

/-! Actual zero padding of signed digit rows, with its complete carry charge. -/
noncomputable section
namespace ThreeSum.TernarySignedPadding
open Filter Real TernarySignedReduction TernaryCoverScale
open TernaryPrincipalDimensions TernaryOversizeOverhead TernaryOversizePrime
open TernaryEntropyRates TernaryLocalParameters TernaryOversizeRates TernaryParameters
open scoped Topology

def digitLength (b U : ℕ) : ℕ := Nat.clog b (4*U+1)
def paddedLength (b U r : ℕ) : ℕ := digitLength b U+r+1

theorem padded_length_proper (b U r : ℕ) : r<paddedLength b U r := by
  unfold paddedLength
  omega

theorem padded_length_capacity {b : ℕ} (hb : 1<b) (U r : ℕ) :
    4*U<b^paddedLength b U r := by
  have h := Nat.le_pow_clog hb (4*U+1)
  have he : digitLength b U ≤ paddedLength b U r := by unfold paddedLength; omega
  exact lt_of_lt_of_le (lt_of_lt_of_le (by omega : 4*U<4*U+1) h)
    (Nat.pow_le_pow_right hb.le he)

theorem clog_power_bound {b x : ℕ} (hb : 1<b) (hx : 0<x) :
    b^(Nat.clog b x) ≤ b*x := by
  by_cases h1 : x≤1
  · rw [Nat.clog_of_right_le_one h1]
    simp only [pow_zero]
    have : x=1 := by omega
    simp [this]
    omega
  · have hx1 : 1<x := by omega
    have he : Nat.clog b x=(Nat.clog b x).pred+1 :=
      (Nat.succ_pred_eq_of_pos (Nat.clog_pos hb hx1)).symm
    rw [he,pow_succ]
    exact (Nat.mul_le_mul_right b (Nat.pow_pred_clog_lt_self hb hx1).le).trans_eq (Nat.mul_comm _ _)

theorem clog_linear_bound {b x : ℕ} (hb : 1<b) (hx : 0<x) :
    (Nat.clog b x : ℝ) ≤ 1+Real.log (x : ℝ)/Real.log (b : ℝ) := by
  have hbR : (1 : ℝ)<b := by exact_mod_cast hb
  have hbp : (0 : ℝ)<b := by linarith
  have hxp : (0 : ℝ)<x := by exact_mod_cast hx
  have hh : (b : ℝ)^(Nat.clog b x) ≤ (b : ℝ)*(x : ℝ) := by
    exact_mod_cast clog_power_bound hb hx
  have hl := Real.log_le_log (pow_pos hbp _) hh
  rw [Real.log_pow,Real.log_mul hbp.ne' hxp.ne'] at hl
  calc
    _ ≤ (Real.log (b : ℝ)+Real.log (x : ℝ))/Real.log (b : ℝ) :=
      (le_div_iff₀ (Real.log_pos hbR)).mpr hl
    _ = _ := by rw [add_div,div_self (Real.log_pos hbR).ne']

def carryExponent (m b : ℕ) (κ : ℝ) : ℝ :=
  κ*Real.log 2/Real.log (b : ℝ)+2*Real.log 2/Real.log (outputSize m : ℝ)
def carryConstant (b : ℕ) : ℝ :=
  Real.exp (3*Real.log 2+Real.log 5*Real.log 2/Real.log (b : ℝ))

theorem padded_carry_bound {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) :
    (2 : ℝ)^paddedLength b U (radixLength m n) ≤
      carryConstant b*(n : ℝ)^carryExponent m b κ := by
  have hbR : (1 : ℝ)<b := by exact_mod_cast hb
  have hLb := Real.log_pos hbR
  have hLM := output_log_pos hm
  have hnR : (1 : ℝ)<n := by exact_mod_cast hn
  have hnp : (0 : ℝ)<n := by linarith
  have hpow : (1 : ℝ)≤(n : ℝ)^κ := Real.one_le_rpow hnR.le hκ
  have hsize : (4*U+1 : ℕ)=4*U+1 := rfl
  have hsizeR : ((4*U+1 : ℕ) : ℝ)≤5*(n : ℝ)^κ := by push_cast; linarith
  have hx : (0 : ℝ)<((4*U+1 : ℕ) : ℝ) := by positivity
  have hlog := Real.log_le_log hx hsizeR
  rw [Real.log_mul (by norm_num : (5 : ℝ)≠0) (Real.rpow_pos_of_pos hnp κ).ne',
    Real.log_rpow hnp] at hlog
  have hc := clog_linear_bound hb (by omega : 0<4*U+1)
  have hr := prefix_linear_bound
    (show 1<outputSize m by have := outputSize_ge_sixteen hm; omega) hn
    (le_rfl : Nat.clog (outputSize m) (n^2)≤_)
    (by norm_num : (0 : ℝ)≤1)
  norm_num at hr
  have hratio : Real.log ((4*U+1 : ℕ) : ℝ)/Real.log (b : ℝ) ≤
      (Real.log 5+κ*Real.log (n : ℝ))/Real.log (b : ℝ) :=
    div_le_div_of_nonneg_right hlog hLb.le
  have hJ : (paddedLength b U (radixLength m n) : ℝ)*Real.log 2 ≤
      (3*Real.log 2+Real.log 5*Real.log 2/Real.log (b : ℝ))+
        carryExponent m b κ*Real.log (n : ℝ) := by
    have hj : (paddedLength b U (radixLength m n) : ℝ)=
        (Nat.clog b (4*U+1) : ℝ)+(radixLength m n : ℝ)+1 := by
      simp only [paddedLength,digitLength,Nat.cast_add,Nat.cast_one]
    rw [hj]
    have hc' : (Nat.clog b (4*U+1) : ℝ) ≤
        1+(Real.log 5+κ*Real.log (n : ℝ))/Real.log (b : ℝ) := by linarith
    change (radixLength m n : ℝ) ≤ _ at hr
    calc
      _ ≤ ((1+(Real.log 5+κ*Real.log (n : ℝ))/Real.log (b : ℝ))+
          (1+2/Real.log (outputSize m : ℝ)*Real.log (n : ℝ))+1)*Real.log 2 :=
        mul_le_mul_of_nonneg_right (by linarith only [hc',hr]) log_two_pos.le
      _ = _ := by unfold carryExponent; ring
  calc
    _ = Real.exp ((paddedLength b U (radixLength m n) : ℝ)*Real.log 2) := by
      rw [Real.exp_nat_mul,Real.exp_log (by norm_num : (0 : ℝ)<2)]
    _ ≤ Real.exp ((3*Real.log 2+Real.log 5*Real.log 2/Real.log (b : ℝ))+
        carryExponent m b κ*Real.log (n : ℝ)) := Real.exp_le_exp.mpr hJ
    _ = _ := by
      rw [Real.exp_add,Real.rpow_def_of_pos hnp]
      unfold carryConstant
      congr 2
      ring

theorem padded_catalog_bound {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) :
    ((carryCatalog (paddedLength b U (radixLength m n))).card : ℝ) ≤
      carryConstant b*(n : ℝ)^carryExponent m b κ := by
  have hh : ((carryCatalog (paddedLength b U (radixLength m n))).card : ℝ) ≤
      (2 : ℝ)^paddedLength b U (radixLength m n) := by
    exact_mod_cast carryCatalog_card (paddedLength b U (radixLength m n))
  exact hh.trans (padded_carry_bound hm hb hn hκ hU)

theorem padded_carry_eventually {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ ε : ℝ} (hκ : 0≤κ) (hε : carryExponent m b κ<ε)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      (2 : ℝ)^paddedLength b (U n) (radixLength m n) ≤ (n : ℝ)^ε := by
  have h := TernaryRadixOverhead.polynomial_dimension_budget hm 1 (carryConstant b)
    (carryExponent m b κ) ε (by norm_num) (Real.exp_pos _).le hε 0
    (fun n => (2 : ℝ)^paddedLength b (U n) (radixLength m n))
    (fun n hn => padded_carry_bound hm hb hn hκ (hU n hn))
  simpa only [pow_zero,mul_one,one_mul] using h

end ThreeSum.TernarySignedPadding
