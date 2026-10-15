import Submission.ThreeSum.TernaryPrincipalDimensions
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Absorption of ordinary polynomial work per fixed-radix prefix. -/
noncomputable section
namespace ThreeSum.TernaryRadixOverhead
open Filter Real Asymptotics TernaryCoverScale TernaryPrincipalDimensions
open scoped Topology

theorem polynomial_radix_budget {m : ℕ} (hm : 0 < m) (A : ℝ) (hA : 0 ≤ A)
    (d : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d ≤ (n : ℝ)^ε := by
  have hM : 1 < outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hLM := output_log_pos hm
  let c : ℝ := 2+2/Real.log (outputSize m : ℝ)
  have hc : 0 < c := by dsimp [c]; positivity
  have hpow := (isLittleO_log_rpow_rpow_atTop (d : ℝ) hε).comp_tendsto
    tendsto_natCast_atTop_atTop
  have hb := (hpow.const_mul_left (A*c^d)).bound (by norm_num : (0 : ℝ) < 1)
  have hlog := (Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))).eventually_ge_atTop 1
  filter_upwards [hb,hlog,eventually_gt_atTop (1 : ℕ)] with n hb hnlog hn
  dsimp only [Function.comp_apply] at hb hnlog
  have hnr : (0 : ℝ) ≤ n := Nat.cast_nonneg _
  have hr := prefix_linear_bound hM hn (le_rfl : Nat.clog (outputSize m) (n^2) ≤ _) (by norm_num : (0 : ℝ) ≤ 1)
  norm_num at hr
  have hrb : (radixLength m n : ℝ)+1 ≤ c*Real.log n := by
    unfold radixLength at *
    dsimp [c]
    nlinarith
  have hrp := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (radixLength m n : ℝ)+1) hrb d
  have ha := mul_le_mul_of_nonneg_left hrp hA
  have hcLog : 0 ≤ A*c^d*(Real.log (n : ℝ))^d := by positivity
  have hnrpow : 0 ≤ (n : ℝ)^ε := by positivity
  rw [Real.rpow_natCast] at hb
  have hbb : A*c^d*(Real.log (n : ℝ))^d ≤ (n : ℝ)^ε := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg hcLog,abs_of_nonneg hnrpow,one_mul] using hb
  have haa : A*((radixLength m n : ℝ)+1)^d ≤ A*c^d*(Real.log (n : ℝ))^d := by
    simpa only [mul_pow,← mul_assoc] using ha
  exact haa.trans hbb

/-- A polynomial amount of work per prefix is absorbed by the strict
principal-charge margin. The dimension bound is explicit and must come
from the concrete table/query cardinality theorem. -/
theorem polynomial_dimension_budget {m : ℕ} (hm : 0 < m) (A K e q : ℝ)
    (hA : 0 ≤ A) (hK : 0 ≤ K) (he : e < q) (d : ℕ) (X : ℕ → ℝ)
    (hX : ∀ n : ℕ, 1 < n → X n ≤ K*(n : ℝ)^e) :
    ∀ᶠ n : ℕ in atTop,
      A*((radixLength m n : ℝ)+1)^d*X n ≤ (n : ℝ)^q := by
  have hb := polynomial_radix_budget hm (A*K) (mul_nonneg hA hK) d (sub_pos.mpr he)
  filter_upwards [hb,eventually_gt_atTop (1 : ℕ)] with n hb hn
  have hnp : (0 : ℝ) < n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hp : 0 ≤ A*((radixLength m n : ℝ)+1)^d := by positivity
  calc
    _ ≤ A*((radixLength m n : ℝ)+1)^d*(K*(n : ℝ)^e) := mul_le_mul_of_nonneg_left (hX n hn) hp
    _ = ((A*K)*((radixLength m n : ℝ)+1)^d)*(n : ℝ)^e := by ring
    _ ≤ (n : ℝ)^(q-e)*(n : ℝ)^e := mul_le_mul_of_nonneg_right hb (Real.rpow_nonneg hnp.le _)
    _ = _ := by rw [← Real.rpow_add hnp]; congr 1; ring

end ThreeSum.TernaryRadixOverhead
