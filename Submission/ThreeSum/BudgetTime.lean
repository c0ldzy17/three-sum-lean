import Submission.ThreeSum.UniformStageBounds
import Submission.EndStatement

/-!
# The concrete work budget in the benchmark's exact time notation

The benchmark states rational time bounds using natural-number powers.  This
module converts the proved eventual real-power bound for `workBudget` to that
exact notation, absorbing the finitely many exceptional input sizes.

`compiledBudget` also permits fixed multiplicative and additive compilation
costs.  The final adapter is explicitly conditional on an actual program, its
word-size bound, its execution/correctness proof for every input, and its
eventual cost bound.  This module supplies no such program or semantic proof;
it does not discharge the full 3SUM benchmark.
-/

namespace ThreeSum.BudgetTime

open Filter Real ThreeSum.Parameters ThreeSum.StageBounds
  ThreeSum.UniformStageBounds
open scoped Topology

set_option maxHeartbeats 400000

/-- Raising a nonnegative rational power to its denominator gives the
corresponding natural-number numerator power. -/
theorem rational_rpow_power {r : ℚ} (hr : 0 ≤ r) (n : ℕ) :
    ((n : ℝ) ^ (r : ℝ)) ^ r.den = (n : ℝ) ^ r.num.toNat := by
  have hnum : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (Int.cast : ℤ → ℝ) (Int.toNat_of_nonneg (Rat.num_nonneg.2 hr))
  have hden : (r.den : ℝ) ≠ 0 := by exact_mod_cast r.den_nz
  have hmul : (r : ℝ) * (r.den : ℝ) = ((r.num.toNat : ℕ) : ℝ) := by
    rw [Rat.cast_def, hnum]
    field_simp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg n), hmul,
    Real.rpow_natCast]

/-- A genuinely eventual estimate suffices for the benchmark's bound at
every `n ≥ 2`: the finite exceptional values enter its constant. -/
theorem endStatementBigO_of_eventually_le_rpow {r : ℚ} {T : ℕ → ℕ}
    (hr : 0 ≤ r)
    (hT : ∀ᶠ n : ℕ in atTop, (T n : ℝ) ≤ (n : ℝ) ^ (r : ℝ)) :
    EndStatement.BigO T r := by
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.1 hT
  let K : ℕ := 1 + ∑ i ∈ Finset.range N, T i ^ r.den
  refine ⟨K, ?_⟩
  intro n hn
  have hK : 1 ≤ K := by dsimp [K]; omega
  by_cases hnN : N ≤ n
  · have hreal := pow_le_pow_left₀ (Nat.cast_nonneg (α := ℝ) (T n)) (hN n hnN) r.den
    rw [rational_rpow_power hr] at hreal
    have hnat : T n ^ r.den ≤ n ^ r.num.toNat := by exact_mod_cast hreal
    exact hnat.trans (Nat.le_mul_of_pos_left _ hK)
  · have hmem : n ∈ Finset.range N := Finset.mem_range.mpr (by omega)
    have hterm : T n ^ r.den ≤ ∑ i ∈ Finset.range N, T i ^ r.den :=
      Finset.single_le_sum (fun i _ => Nat.zero_le (T i ^ r.den)) hmem
    have hTK : T n ^ r.den ≤ K := hterm.trans (by dsimp [K]; omega)
    have hnpow : 1 ≤ n ^ r.num.toNat := Nat.one_le_pow _ _ (by omega)
    exact hTK.trans (Nat.le_mul_of_pos_right _ hnpow)

theorem workBudget_endStatementBigO (C k : ℕ) :
    EndStatement.BigO (workBudget C k) (981 / 500) := by
  apply endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using workBudget_eventually_target C k

/-- Constants depending only on a fixed compiled program. -/
def compiledBudget (a b C k n : ℕ) : ℕ := a * workBudget C k n + b

theorem compiledBudget_powerBound (a b C k : ℕ) :
    PowerBound (compiledBudget a b C k) certificateExponent := by
  have hmain := (PowerBound.const a).mul (workBudget_powerBound C k)
  have hmain' : PowerBound (fun n => a * workBudget C k n) certificateExponent := by
    simpa only [zero_add] using hmain
  have hconst : PowerBound (fun _ : ℕ => b) certificateExponent :=
    (PowerBound.const b).mono_exponent (by norm_num [certificateExponent])
  exact hmain'.add_same hconst

theorem compiledBudget_eventually_target (a b C k : ℕ) :
    ∀ᶠ n : ℕ in atTop, (compiledBudget a b C k n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  have h := compiledBudget_powerBound a b C k
    (targetExponent - certificateExponent) (sub_pos.mpr certificate_lt_target)
  have heq : certificateExponent + (targetExponent - certificateExponent) = targetExponent := by ring
  simpa only [heq] using h

theorem compiledBudget_endStatementBigO (a b C k : ℕ) :
    EndStatement.BigO (compiledBudget a b C k) (981 / 500) := by
  apply endStatementBigO_of_eventually_le_rpow (by norm_num)
  simpa [targetExponent] using compiledBudget_eventually_target a b C k

/-- This theorem requires the cost of an actual program (or another concrete
natural-valued cost) to have been bounded separately. -/
theorem time_endStatementBigO_of_eventually_le_compiledBudget
    {T : ℕ → ℕ} {a b C k : ℕ}
    (hT : ∀ᶠ n : ℕ in atTop, T n ≤ compiledBudget a b C k n) :
    EndStatement.BigO T (981 / 500) := by
  apply endStatementBigO_of_eventually_le_rpow (by norm_num)
  filter_upwards [hT, compiledBudget_eventually_target a b C k] with n hcost hbound
  have hcast : (T n : ℝ) ≤ compiledBudget a b C k n := by exact_mod_cast hcost
  simpa [targetExponent] using hcast.trans hbound

/-- An interface for the remaining program proof.  The hypothesis contains
actual machine execution and correctness at every input size and admissible
word width; only its cost comparison may be eventual.  No instance of this
hypothesis is constructed here. -/
theorem solvedInTime_of_program_contract (Q : EndStatement.Problem)
    (hprogram : ∀ κ : ℕ, ∃ (P : List EndStatement.Instr) (w : ℕ) (T : ℕ → ℕ)
      (a b C k : ℕ),
      (∀ᶠ n : ℕ in atTop, T n ≤ compiledBudget a b C k n) ∧
      ∀ (n : ℕ) (x : Q.Instance n),
        (∀ z ∈ Q.input x, z.natAbs ≤ n ^ κ) →
        ∀ W ≥ w * (Nat.log2 n + 1), Q.SolvedBy x P W (T n)) :
    Q.SolvedInTime (981 / 500) := by
  intro κ
  obtain ⟨P, w, T, a, b, C, k, hcost, hcorrect⟩ := hprogram κ
  exact ⟨P, w, T, time_endStatementBigO_of_eventually_le_compiledBudget hcost, hcorrect⟩

end ThreeSum.BudgetTime
