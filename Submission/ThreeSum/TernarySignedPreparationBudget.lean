import Submission.ThreeSum.TernarySignedParameters
import Submission.ThreeSum.LightTernarySignedMatrix
import Submission.ThreeSum.LightTernaryCarryCodes
import Submission.ThreeSum.LightTernaryCarryApply

/-! Original digit preprocessing and carry enumeration fit the chosen exponent budget. -/
noncomputable section
namespace ThreeSum.TernarySignedPreparationBudget
open Filter Real Asymptotics TernarySignedPadding TernaryCoverScale
open TernaryPrincipalDimensions TernaryLocalParameters TernaryParameters
open scoped Topology

private theorem floor_log_linear_bound {b x : ℕ} (hb : 1<b) (hx : 0<x) :
    (Nat.log b x : ℝ)≤Real.log (x : ℝ)/Real.log (b : ℝ) := by
  have hbR : (1 : ℝ)<b := by exact_mod_cast hb
  have hbp : (0 : ℝ)<b := by linarith
  have hh : (b : ℝ)^(Nat.log b x)≤(x : ℝ) := by exact_mod_cast Nat.pow_log_le_self b hx.ne'
  have hl := Real.log_le_log (pow_pos hbp _) hh
  rw [Real.log_pow] at hl
  exact (le_div_iff₀ (Real.log_pos hbR)).mpr hl

def digitConstant (m b : ℕ) (κ : ℝ) : ℝ :=
  4+Real.log 5/Real.log (b : ℝ)+κ/Real.log (b : ℝ)+2/Real.log (outputSize m : ℝ)
def binaryConstant (κ : ℝ) : ℝ := 4+κ/Real.log 2

theorem digitConstant_pos {m b : ℕ} (hm : 0<m) (hb : 1<b) {κ : ℝ} (hκ : 0≤κ) :
    0<digitConstant m b κ := by
  have hLb := Real.log_pos (by exact_mod_cast hb : (1 : ℝ)<b)
  have hLM := output_log_pos hm
  have h5 : 0<Real.log 5 := Real.log_pos (by norm_num)
  unfold digitConstant
  positivity

theorem binaryConstant_pos {κ : ℝ} (hκ : 0≤κ) : 0<binaryConstant κ := by
  unfold binaryConstant
  positivity

theorem digit_logarithmic_bound {m b n U : ℕ} (hm : 0<m) (hb : 1<b) (hn : 1<n)
    {κ : ℝ} (hκ : 0≤κ) (hU : (U : ℝ)≤(n : ℝ)^κ) (hlog : 1≤Real.log (n : ℝ)) :
    (paddedLength b U (radixLength m n) : ℝ)+1≤
      digitConstant m b κ*Real.log (n : ℝ) := by
  have hLb := Real.log_pos (by exact_mod_cast hb : (1 : ℝ)<b)
  have hLM := output_log_pos hm
  have hnR : (1 : ℝ)<n := by exact_mod_cast hn
  have hnp : (0 : ℝ)<n := by linarith
  have hp : (1 : ℝ)≤(n : ℝ)^κ := Real.one_le_rpow hnR.le hκ
  have hsize : ((4*U+1 : ℕ) : ℝ)≤5*(n : ℝ)^κ := by push_cast; linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<((4*U+1 : ℕ) : ℝ)) hsize
  rw [Real.log_mul (by norm_num : (5 : ℝ)≠0) (Real.rpow_pos_of_pos hnp κ).ne',Real.log_rpow hnp] at hl
  have hc := clog_linear_bound hb (by omega : 0<4*U+1)
  have hratio := div_le_div_of_nonneg_right hl hLb.le
  have hr := prefix_linear_bound
    (show 1<outputSize m by have := outputSize_ge_sixteen hm; omega) hn
    (le_rfl : Nat.clog (outputSize m) (n^2)≤_) (by norm_num : (0 : ℝ)≤1)
  norm_num at hr
  change (radixLength m n : ℝ)≤_ at hr
  have hinit : (paddedLength b U (radixLength m n) : ℝ)+1≤
      4+Real.log 5/Real.log (b : ℝ)+
        (κ/Real.log (b : ℝ)+2/Real.log (outputSize m : ℝ))*Real.log (n : ℝ) := by
    have hJ : (paddedLength b U (radixLength m n) : ℝ)=
        (Nat.clog b (4*U+1) : ℝ)+(radixLength m n : ℝ)+1 := by
      simp only [paddedLength,digitLength,Nat.cast_add,Nat.cast_one]
    rw [hJ]
    have hh : (Nat.clog b (4*U+1) : ℝ)≤1+(Real.log 5+κ*Real.log (n : ℝ))/Real.log (b : ℝ) := by
      linarith only [hc,hratio]
    have he : 4+Real.log 5/Real.log (b : ℝ)+
        (κ/Real.log (b : ℝ)+2/Real.log (outputSize m : ℝ))*Real.log (n : ℝ)=
      (1+(Real.log 5+κ*Real.log (n : ℝ))/Real.log (b : ℝ))+
        (1+2/Real.log (outputSize m : ℝ)*Real.log (n : ℝ))+2 := by ring
    rw [he]
    linarith only [hh,hr]
  have hnon : 0≤4+Real.log 5/Real.log (b : ℝ) := by
    have h5 : 0<Real.log 5 := Real.log_pos (by norm_num)
    positivity
  have hmul := mul_le_mul_of_nonneg_left hlog hnon
  unfold digitConstant
  nlinarith only [hinit,hmul]

theorem binary_logarithmic_bound {n U : ℕ} (hn : 1<n) {κ : ℝ} (hκ : 0≤κ)
    (hU : (U : ℝ)≤(n : ℝ)^κ) (hlog : 1≤Real.log (n : ℝ)) :
    (Nat.log 2 (3*U+1) : ℝ)+2≤binaryConstant κ*Real.log (n : ℝ) := by
  have hnR : (1 : ℝ)<n := by exact_mod_cast hn
  have hnp : (0 : ℝ)<n := by linarith
  have hp : (1 : ℝ)≤(n : ℝ)^κ := Real.one_le_rpow hnR.le hκ
  have hsize : ((3*U+1 : ℕ) : ℝ)≤4*(n : ℝ)^κ := by push_cast; linarith
  have hl := Real.log_le_log (by positivity : (0 : ℝ)<((3*U+1 : ℕ) : ℝ)) hsize
  rw [Real.log_mul (by norm_num : (4 : ℝ)≠0) (Real.rpow_pos_of_pos hnp κ).ne',Real.log_rpow hnp] at hl
  have hfour : Real.log 4=2*Real.log 2 := by
    rw [show (4 : ℝ)=2^2 by norm_num,Real.log_pow]
    norm_num
  rw [hfour] at hl
  have hb := floor_log_linear_bound (by decide : 1<(2 : ℕ)) (by omega : 0<3*U+1)
  have hh := div_le_div_of_nonneg_right hl log_two_pos.le
  have he : (2*Real.log 2+κ*Real.log (n : ℝ))/Real.log 2=
      2+κ/Real.log 2*Real.log (n : ℝ) := by field_simp
  rw [he] at hh
  unfold binaryConstant
  nlinarith only [hb,hh,hlog]

theorem polynomial_digit_budget {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ ε : ℝ} (hκ : 0≤κ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) (d : ℕ)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      A*((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d≤(n : ℝ)^ε := by
  let C : ℝ := (digitConstant m b κ*binaryConstant κ)^d
  have hC : 0≤C := by
    exact pow_nonneg (mul_nonneg (digitConstant_pos hm hb hκ).le (binaryConstant_pos hκ).le) d
  have hpow := (isLittleO_log_rpow_rpow_atTop ((2*d : ℕ) : ℝ) hε).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hbound := (hpow.const_mul_left (A*C)).bound (by norm_num : (0 : ℝ)<1)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hbound,hlog,eventually_gt_atTop (1 : ℕ)] with n hbound hlog hn
  dsimp only [Function.comp_apply] at hbound hlog
  have hJ := digit_logarithmic_bound hm hb hn hκ (hU n hn) hlog
  have hB := binary_logarithmic_bound hn hκ (hU n hn) hlog
  have hJp := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(paddedLength b (U n) (radixLength m n) : ℝ)+1) hJ d
  have hBp := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤(Nat.log 2 (3*U n+1) : ℝ)+2) hB d
  have hCJ := digitConstant_pos hm hb hκ
  have hCB := binaryConstant_pos hκ
  have hprod := mul_le_mul hJp hBp (by positivity) (by positivity)
  have hprodA := mul_le_mul_of_nonneg_left hprod hA
  have he : A*((digitConstant m b κ*Real.log (n : ℝ))^d*
        (binaryConstant κ*Real.log (n : ℝ))^d)=A*C*(Real.log (n : ℝ))^(2*d) := by
    dsimp [C]
    rw [mul_pow,mul_pow,mul_pow,show 2*d=d+d by omega,pow_add]
    ring
  rw [he] at hprodA
  rw [Real.rpow_natCast] at hbound
  have hpoly : 0≤A*C*(Real.log (n : ℝ))^(2*d) := by positivity
  have hnpow : 0≤(n : ℝ)^ε := by positivity
  have hbound' : A*C*(Real.log (n : ℝ))^(2*d)≤(n : ℝ)^ε := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hpoly,abs_of_nonneg hnpow,one_mul] using hbound
  simpa only [← mul_assoc] using hprodA.trans hbound'

/-- This includes even the crude requester-by-carry product preprocessing.
The physical matrix/table/pass theorems discharge its per-iteration costs. -/
theorem carry_preparation_budget {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ δ ε : ℝ} (hκ : 0≤κ) (hδ : carryExponent m b κ<δ) (hε : 0<ε)
    (A : ℝ) (hA : 0≤A) (d : ℕ) (U : ℕ→ℕ)
    (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      A*(n : ℝ)*(2 : ℝ)^paddedLength b (U n) (radixLength m n)*
        ((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d≤(n : ℝ)^(1+δ+ε) := by
  filter_upwards [padded_carry_eventually hm hb hκ hδ U hU,
    polynomial_digit_budget hm hb hκ hε A hA d U hU,
    eventually_gt_atTop (1 : ℕ)] with n hc hp hn
  have hnp : (0 : ℝ)<n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hh := mul_le_mul_of_nonneg_left hc hnp.le
  have hhh := mul_le_mul hp hh (by positivity) (by positivity)
  calc
    _ = (A*((paddedLength b (U n) (radixLength m n) : ℝ)+1)^d*
        ((Nat.log 2 (3*U n+1) : ℝ)+2)^d)*
        ((n : ℝ)*(2 : ℝ)^paddedLength b (U n) (radixLength m n)) := by ring
    _ ≤ (n : ℝ)^ε*((n : ℝ)*(n : ℝ)^δ) := hhh
    _ = (n : ℝ)^ε*((n : ℝ)^(1 : ℝ)*(n : ℝ)^δ) := by rw [Real.rpow_one]
    _ = (n : ℝ)^(ε+(1+δ)) := by rw [← Real.rpow_add hnp,← Real.rpow_add hnp]
    _ = _ := by congr 1; ring

end ThreeSum.TernarySignedPreparationBudget
