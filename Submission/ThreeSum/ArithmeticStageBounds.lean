import Submission.ThreeSum.ModuloCosts
import Submission.ThreeSum.BudgetTime

/-!
# The arithmetic and balancing work outside the six reporting stages

The finite bounds here include complete modular-counting invocations, their
signed-remainder bit cost, and the actual correlation/minimum routine. They
augment the six-stage reporting budget. The whole solver still has to charge
its actual host operations to this combined budget.
-/

namespace ThreeSum.ArithmeticStageBounds

open Filter Real Parameters Scales BandScales CostLedger HierarchyScales
  MassScales StageBounds UniformStageBounds ModuloCosts
open scoped Topology

set_option maxHeartbeats 1000000

def maxMod (n : ℕ) : ℕ := radix n * (4*primeWindow n)^2

def bitBudget (k n : ℕ) : ℕ := 2*(k+2)*primeWindow n^2+1

def perTripleBudget (k n : ℕ) : ℕ :=
  10000*(roundedPower (maxMod n) + bandSize n * bitBudget k n + 1)

def arithmeticBudget (C k n : ℕ) : ℕ :=
  concreteOverhead C n * (3*bandCount n^2 * perTripleBudget k n)

def offsetBudget (C n : ℕ) : ℕ :=
  concreteOverhead C n * (2982*roundedPower (radix n))

def normalizationBudget (C n : ℕ) : ℕ := concreteOverhead C n * n

def combinedBudget (C k n : ℕ) : ℕ :=
  workBudget C k n + arithmeticBudget C k n + offsetBudget C n + normalizationBudget C n

theorem maxMod_pos (n : ℕ) : 0 < maxMod n := by
  unfold maxMod
  exact Nat.mul_pos (radix_pos n) (Nat.pow_pos (by have := primeWindow_ge_two n; omega))

theorem bits_le_window_square (n : ℕ) : inputBits n+1 ≤ primeWindow n^2 := by
  have hroot := Nat.lt_succ_sqrt' (inputBits n)
  have hpow : Nat.sqrt (inputBits n)+1 ≤ 2^(Nat.sqrt (inputBits n)+1) :=
    (Nat.lt_pow_self (by decide : 1 < 2)).le
  have hs := Nat.pow_le_pow_left hpow 2
  unfold primeWindow windowExponent
  simp only [Nat.succ_eq_add_one] at hroot
  omega

theorem remainder_bits_le {n : ℕ} (k : ℕ) (hn : 0 < n) :
    Nat.log 2 (n^k+1)+1 ≤ bitBudget k n := by
  have hp : 0 < n^k := Nat.pow_pos hn
  have hm := Nat.log_mono_right (b := 2) (show n^k+1 ≤ 3*n^k by omega)
  have hl := log2_difference_bound k hn
  rw [Nat.log2_eq_log_two] at hl
  have hw := Nat.mul_le_mul_left (2*(k+2)) (bits_le_window_square n)
  unfold bitBudget
  omega

theorem invocation_le_budget {n p nA nB nC : ℕ} (k : ℕ)
    (hn : 0 < n) (hp : p ≤ maxMod n)
    (ha : nA ≤ bandSize n) (hb : nB ≤ bandSize n) (hc : nC ≤ bandSize n) :
    LightModuloCounts.time p nA nB nC (n^k) ≤ perTripleBudget k n := by
  have ht := ModuloRuntime.time_mono hp nA nB nC (n^k)
  have hbnd := ModuloCosts.time_bound (maxMod n) nA nB nC (bandSize n) (n^k) ha hb hc
  have hm := Nat.mul_le_mul_left (bandSize n) (remainder_bits_le k hn)
  unfold perTripleBudget
  omega

noncomputable section

theorem powerBound_mono {f g : ℕ → ℕ} {a : ℝ} (hg : PowerBound g a)
    (hfg : ∀ᶠ n : ℕ in atTop, f n ≤ g n) : PowerBound f a := by
  intro d hd
  filter_upwards [hg d hd, hfg] with n hn hm
  exact (show (f n : ℝ) ≤ (g n : ℝ) by exact_mod_cast hm).trans hn

/-- An exact integer fifth-power estimate supplies the real exponent bound. -/
theorem powerBound_of_fifth {f g : ℕ → ℕ} {a : ℝ}
    (hg : PowerBound g a) (hfg : ∀ n, f n^5 ≤ 256*g n^8) :
    PowerBound f ((8/5)*a) := by
  intro d hd
  filter_upwards [hg (d/2) (by linarith), (PowerBound.const 256) (d/2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hn hconst hge
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hgeR : (1 : ℝ) ≤ n := by exact_mod_cast hge
  have hpow : (f n : ℝ)^5 ≤ ((n : ℝ)^((8/5)*a+d))^5 := by
    calc
      _ ≤ 256*(g n : ℝ)^8 := by exact_mod_cast hfg n
      _ ≤ (n : ℝ)^(d/2) * ((n : ℝ)^(a+d/2))^8 := by
        apply mul_le_mul
        · simpa only [zero_add, Nat.cast_ofNat] using hconst
        · exact pow_le_pow_left₀ (Nat.cast_nonneg _) hn 8
        · positivity
        · positivity
      _ = (n : ℝ)^(d/2+(a+d/2)*8) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hnR.le, ← Real.rpow_add hnR]
        norm_num
      _ ≤ (n : ℝ)^(((8/5)*a+d)*5) :=
        Real.rpow_le_rpow_of_exponent_le hgeR (by linarith)
      _ = _ := by rw [Real.rpow_mul hnR.le]; norm_num only [Real.rpow_ofNat]
  exact le_of_pow_le_pow_left₀ (by decide : (5 : ℕ) ≠ 0) (by positivity) hpow

theorem window_powerBound : PowerBound primeWindow 0 :=
  PowerBound.of_rate primeWindow_log_ratio_tendsto_zero

theorem maxMod_powerBound : PowerBound maxMod ((E+1/2)/5) := by
  change PowerBound (fun n => radix n*(4*primeWindow n)^2) ((E+1/2)/5)
  have hwindow := ((PowerBound.const 4).mul window_powerBound).pow 2
  have hh := (PowerBound.of_rate radix_log_ratio_tendsto).mul hwindow
  simpa only [zero_add, mul_zero, add_zero] using hh

theorem rounded_maxMod_powerBound :
    PowerBound (fun n => roundedPower (maxMod n)) ((8/5)*((E+1/2)/5)) := by
  apply powerBound_of_fifth maxMod_powerBound
  intro n
  simpa only [show (2 : ℕ)^8 = 256 by norm_num] using roundedPower_fifth (maxMod_pos n)

theorem bitBudget_powerBound (k : ℕ) : PowerBound (bitBudget k) 0 := by
  have hh := (PowerBound.const (2*(k+2))).mul (window_powerBound.pow 2)
  have hh' : PowerBound (fun n => 2*(k+2)*primeWindow n^2) 0 := by
    simpa only [Nat.cast_ofNat, mul_zero, add_zero] using hh
  exact hh'.add_same (PowerBound.const 1)

theorem perTriple_powerBound (k : ℕ) :
    PowerBound (perTripleBudget k) ((8/5)*((E+1/2)/5)) := by
  change PowerBound (fun n => 10000*(roundedPower (maxMod n)+bandSize n*bitBudget k n+1)) _
  have hb := (PowerBound.of_rate bandSize_log_rate_shift).mul (bitBudget_powerBound k)
  have hb' : PowerBound (fun n => bandSize n*bitBudget k n) ((E+bandShift)/5) := by
    simpa only [add_zero] using hb
  have hba : (E+bandShift)/5 ≤ (8/5)*((E+1/2)/5) := by
    have he := E_bounds.1
    unfold bandShift
    linarith
  have hzero : (0 : ℝ) ≤ (8/5)*((E+1/2)/5) := by
    have he := E_bounds.1
    linarith
  have hsum := (rounded_maxMod_powerBound.add_same (hb'.mono_exponent hba)).add_same
    ((PowerBound.const 1).mono_exponent hzero)
  have hh := (PowerBound.const 10000).mul hsum
  simpa only [zero_add] using hh

theorem arithmetic_powerBound (C k : ℕ) :
    PowerBound (arithmeticBudget C k)
      (2+epsilon*(4/5-(2/5)*E-2*bandShift)) := by
  have hm := (PowerBound.of_rate bandCount_log_rate).pow 2
  have hh := (concreteOverhead_powerBound C).mul
    (((PowerBound.const 3).mul hm).mul (perTriple_powerBound k))
  have heq : (0 : ℝ)+(0+2*(1-(E+bandShift)/5)+(8/5)*((E+1/2)/5)) =
      2+epsilon*(4/5-(2/5)*E-2*bandShift) := by unfold epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  exact hh

theorem offset_powerBound (C : ℕ) :
    PowerBound (offsetBudget C) (epsilon*(8/5)*(E+1/2)) := by
  have hrad : PowerBound (fun n => roundedPower (radix n)) ((8/5)*((E+1/2)/5)) := by
    apply powerBound_of_fifth (PowerBound.of_rate radix_log_ratio_tendsto)
    intro n
    simpa only [show (2 : ℕ)^8 = 256 by norm_num] using roundedPower_fifth (radix_pos n)
  have hh := (concreteOverhead_powerBound C).mul ((PowerBound.const 2982).mul hrad)
  have heq : (0 : ℝ)+(0+(8/5)*((E+1/2)/5)) = epsilon*(8/5)*(E+1/2) := by
    unfold epsilon
    ring
  rw [heq] at hh
  exact hh

theorem identity_powerBound : PowerBound (fun n : ℕ => n) 1 := by
  intro d hd
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  simpa only [Real.rpow_one] using
    (Real.rpow_le_rpow_of_exponent_le hnR (show (1 : ℝ) ≤ 1+d by linarith))

theorem normalization_powerBound (C : ℕ) : PowerBound (normalizationBudget C) 1 := by
  change PowerBound (fun n => concreteOverhead C n*n) 1
  simpa only [zero_add] using (concreteOverhead_powerBound C).mul identity_powerBound

/-- Every term is a concrete size-only natural budget. This is not an
assertion that a complete solver already satisfies the budget. -/
theorem combined_powerBound (C k : ℕ) : PowerBound (combinedBudget C k) certificateExponent := by
  have ha := (arithmetic_powerBound C k).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ho := (offset_powerBound C).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hn := (normalization_powerBound C).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact (((workBudget_powerBound C k).add_same ha).add_same ho).add_same hn

theorem combined_eventually_target (C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (combinedBudget C k n : ℝ) ≤ (n : ℝ)^targetExponent := by
  have hh := (combined_powerBound C k) (targetExponent-certificateExponent)
    (sub_pos.mpr certificate_lt_target)
  simpa only [add_sub_cancel] using hh

theorem combined_endStatementBigO (C k : ℕ) :
    EndStatement.BigO (combinedBudget C k) (981/500 : Rat) := by
  apply BudgetTime.endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using combined_eventually_target C k

end
end ThreeSum.ArithmeticStageBounds
