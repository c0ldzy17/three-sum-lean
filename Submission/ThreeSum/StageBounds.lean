import Submission.ThreeSum.MassScales

/-!
# The six principal finite stage counts

This module assembles actual natural-number work quantities.  Its final
theorem is a runtime-ledger target, not a 3SUM correctness or machine-time
theorem.  The only input-dependent assumptions are four explicit finite
counting inequalities for the wanted mass and the prime-chain score.
An implementation must still connect its operation counter to these counts.
-/

namespace ThreeSum.StageBounds

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.Switch ThreeSum.CostLedger ThreeSum.HierarchyScales
  ThreeSum.MassScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def tableCount (n : ℕ) : ℕ := scheduleCount n * fullOutputs n

def encoderCount (n : ℕ) : ℕ := 2 * bandCount n * scheduleCount n * fullOutputs n

def boxCount (n : ℕ) : ℕ := 3 * bandCount n ^ 2 * scheduleCount n * allPrefixBoxes n

def initialCount (W : ℕ → ℕ) (n : ℕ) : ℕ := W n * queryTerms n 0

def activeCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  H n * representationBound n * microPartitions n * allQueryTerms n

def terminalChoices (n : ℕ) : ℕ := 2 ^ residualSize n (terminalDepth n)

def terminalCount (H : ℕ → ℕ) (n : ℕ) : ℕ :=
  2 * H n * representationBound n * terminalChoices n

def coreWork (W H : ℕ → ℕ) (n : ℕ) : ℕ :=
  tableCount n + encoderCount n + boxCount n + initialCount W n + activeCount H n + terminalCount H n

def concreteOverhead (C n : ℕ) : ℕ :=
  (localSearch C n + 1) * (primeWindow n + 1) ^ C * polynomialFactor C n

def amplifiedCoreWork (C : ℕ) (W H : ℕ → ℕ) (n : ℕ) : ℕ :=
  concreteOverhead C n * coreWork W H n

noncomputable section

/-- A proved power upper bound with arbitrarily small positive slack. -/
def PowerBound (f : ℕ → ℕ) (a : ℝ) : Prop :=
  ∀ d : ℝ, 0 < d → ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d)

namespace PowerBound

theorem of_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) : PowerBound f a :=
  fun _ hd => eventually_le_rpow_of_log_ratio hf hd

theorem const (c : ℕ) : PowerBound (fun _ => c) 0 := of_rate (nat_log_rate_const c)

theorem mul {f g : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hg : PowerBound g b) :
    PowerBound (fun n => f n * g n) (a + b) := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    eventually_ge_atTop (1 : ℕ)] with n hfn hgn hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  rw [Nat.cast_mul]
  calc
    _ ≤ (n : ℝ) ^ (a + d / 2) * (n : ℝ) ^ (b + d / 2) :=
      mul_le_mul hfn hgn (Nat.cast_nonneg _) (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ ((a + b) + d) := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem mono_exponent {f : ℕ → ℕ} {a b : ℝ} (hf : PowerBound f a) (hab : a ≤ b) :
    PowerBound f b := by
  intro d hd
  filter_upwards [hf d hd, eventually_ge_atTop (1 : ℕ)] with n hn hge
  exact hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hge) (by linarith))

theorem add_same {f g : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (hg : PowerBound g a) :
    PowerBound (fun n => f n + g n) a := by
  intro d hd
  filter_upwards [hf (d / 2) (by linarith), hg (d / 2) (by linarith),
    (const 2) (d / 2) (by linarith), eventually_ge_atTop (1 : ℕ)] with n hfn hgn htwo hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  simp only [zero_add, Nat.cast_ofNat] at htwo
  rw [Nat.cast_add]
  calc
    _ ≤ 2 * (n : ℝ) ^ (a + d / 2) := by linarith
    _ ≤ (n : ℝ) ^ (d / 2) * (n : ℝ) ^ (a + d / 2) :=
      mul_le_mul_of_nonneg_right htwo (Real.rpow_nonneg hnR.le _)
    _ = (n : ℝ) ^ (a + d) := by rw [← Real.rpow_add hnR]; congr 1; ring

theorem pow {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) (k : ℕ) :
    PowerBound (fun n => f n ^ k) ((k : ℝ) * a) := by
  induction k with
  | zero => simpa only [Nat.cast_zero, zero_mul, pow_zero] using const 1
  | succ k ih =>
      simpa only [Nat.pow_succ, Nat.cast_add, Nat.cast_one, add_mul, one_mul] using ih.mul hf

end PowerBound

theorem wanted_powerBound {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n) :
    PowerBound W (2 - (1 / 2 + bandShift) / 5) := by
  intro d hd
  filter_upwards [hW, wantedMajorant_eventually_le hd] with n hn he
  exact (wanted_mass_le hn).trans he

theorem false_powerBound {H P H1 : ℕ → ℕ} (k : ℕ)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound H (2 - (1 / 2 - bandShift) / 5) := by
  intro d hd
  filter_upwards [hscore, hinit, hmod, falseMajorant_eventually_le k hd] with n hs hi hm he
  exact (false_mass_le hs hi hm).trans he

theorem table_powerBound : PowerBound tableCount (2 * epsilon * E) := by
  have hh := (PowerBound.of_rate scheduleCount_log_rate).mul
    (PowerBound.of_rate fullOutputs_log_rate)
  have heq : (0 : ℝ) + 2 * E / 5 = 2 * epsilon * E := by unfold epsilon; ring
  rw [heq] at hh
  exact hh

theorem encoder_powerBound : PowerBound encoderCount (1 + epsilon * (E - bandShift)) := by
  have hh := (((PowerBound.const 2).mul (PowerBound.of_rate bandCount_log_rate)).mul
    (PowerBound.of_rate scheduleCount_log_rate)).mul (PowerBound.of_rate fullOutputs_log_rate)
  have heq : ((0 : ℝ) + (1 - (E + bandShift) / 5) + 0) + 2 * E / 5 =
      1 + epsilon * (E - bandShift) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh

theorem boxes_powerBound : PowerBound boxCount (2 - epsilon * boxSaving) := by
  have hB := PowerBound.of_rate (nat_log_rate_pow bandCount_log_rate 2)
  have hQ : PowerBound allPrefixBoxes ((2 * E + 2 * bandShift - boxSaving) / 5) :=
    fun _ hd => allPrefixBoxes_eventually_le hd
  have hh := (((PowerBound.const 3).mul hB).mul (PowerBound.of_rate scheduleCount_log_rate)).mul hQ
  have heq : ((0 : ℝ) + 2 * (1 - (E + bandShift) / 5) + 0) +
      (2 * E + 2 * bandShift - boxSaving) / 5 = 2 - epsilon * boxSaving := by unfold epsilon; ring
  norm_num only [Nat.cast_ofNat] at hh
  rw [heq] at hh
  exact hh

theorem initial_powerBound {W : ℕ → ℕ}
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n) :
    PowerBound (initialCount W) (2 - epsilon * (1 / 2 + bandShift - entropy initialTheta)) := by
  have hQ : PowerBound (fun n => queryTerms n 0) (entropy initialTheta / 5) :=
    fun _ hd => initial_query_eventually_le hd
  have hh := (wanted_powerBound hW).mul hQ
  have heq : (2 - (1 / 2 + bandShift) / 5) + entropy initialTheta / 5 =
      2 - epsilon * (1 / 2 + bandShift - entropy initialTheta) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh

theorem active_powerBound {H P H1 : ℕ → ℕ} (k : ℕ)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (activeCount H)
      (2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift))) := by
  have hG : PowerBound microPartitions 0 := by
    intro d hd
    simpa only [zero_add] using microPartitions_subpolynomial hd
  have hQ : PowerBound allQueryTerms ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5) :=
    fun _ hd => allQueryTerms_eventually_le hd
  have hh := (((false_powerBound k hscore hinit hmod).mul
    (PowerBound.of_rate representationBound_log_rate)).mul hG).mul hQ
  have heq : ((2 - (1 / 2 - bandShift) / 5) + kappa / 5 + 0) +
      (entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 =
      2 - epsilon * (1 / 2 - bandShift - kappa - entropyRatio * (1 + boxSaving - 2 * bandShift)) := by
    unfold epsilon
    ring
  rw [heq] at hh
  exact hh

theorem terminalChoices_log_rate :
    Tendsto (fun n : ℕ => Real.log (terminalChoices n : ℝ) / Real.log n) atTop
      (𝓝 ((1 - terminalFraction) / 5)) := by
  have hh := mu_log_ratio_tendsto.const_mul (Real.log 2 * (1 - terminalFraction))
  have heq : Real.log 2 * (1 - terminalFraction) * (1 / (5 * Real.log 2)) =
      (1 - terminalFraction) / 5 := by field_simp
  rw [heq] at hh
  apply hh.congr'
  filter_upwards [mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hid := residual_real_identity (by omega : 0 < mu n)
    (j := terminalDepth n) le_rfl
  rw [terminal_fraction_exact (by omega : 0 < mu n)] at hid
  simp only [terminalChoices, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow, hid]
  ring

theorem terminal_powerBound {H P H1 : ℕ → ℕ} (k : ℕ)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (terminalCount H)
      (2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa)) := by
  have hh := (((PowerBound.const 2).mul (false_powerBound k hscore hinit hmod)).mul
    (PowerBound.of_rate representationBound_log_rate)).mul (PowerBound.of_rate terminalChoices_log_rate)
  have heq : ((0 : ℝ) + (2 - (1 / 2 - bandShift) / 5) + kappa / 5) +
      (1 - terminalFraction) / 5 =
      2 - epsilon * (terminalFraction - 1 / 2 - bandShift - kappa) := by unfold epsilon; ring
  rw [heq] at hh
  exact hh

theorem coreWork_powerBound {W H P H1 : ℕ → ℕ} (k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (coreWork W H) certificateExponent := by
  have ht := table_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have he := encoder_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hb := boxes_powerBound.mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hi := (initial_powerBound hW).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have ha := (active_powerBound k hscore hinit hmod).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  have hf := (terminal_powerBound k hscore hinit hmod).mono_exponent
    (all_costs_le_certificate _ (by simp [costLedger]))
  exact ((((ht.add_same he).add_same hb).add_same hi).add_same ha).add_same hf

theorem concreteOverhead_powerBound (C : ℕ) : PowerBound (concreteOverhead C) 0 := by
  have hl : PowerBound (localSearch C) 0 := by
    intro d hd
    simpa only [zero_add] using localSearch_subpolynomial C hd
  have hp := PowerBound.of_rate (polynomialFactor_log_rate C)
  have hw := ((PowerBound.of_rate primeWindow_log_ratio_tendsto_zero).add_same (PowerBound.const 1)).pow C
  intro d hd
  have hh := (((hl.add_same (PowerBound.const 1)).mul hw).mul hp) d hd
  simpa only [concreteOverhead, mul_zero, zero_add] using hh

theorem amplifiedCoreWork_powerBound {W H P H1 : ℕ → ℕ} (C k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    PowerBound (amplifiedCoreWork C W H) certificateExponent := by
  intro d hd
  have hh := ((concreteOverhead_powerBound C).mul
    (coreWork_powerBound k hW hscore hinit hmod)) d hd
  simpa only [amplifiedCoreWork, zero_add] using hh

theorem amplifiedCoreWork_eventually_target {W H P H1 : ℕ → ℕ} (C k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    ∀ᶠ n : ℕ in atTop, (amplifiedCoreWork C W H n : ℝ) ≤ (n : ℝ) ^ targetExponent := by
  have hh := (amplifiedCoreWork_powerBound C k hW hscore hinit hmod)
    (targetExponent - certificateExponent) (sub_pos.mpr certificate_lt_target)
  have hid : certificateExponent + (targetExponent - certificateExponent) = targetExponent := by ring
  rw [hid] at hh
  exact hh

theorem amplifiedCoreWork_isBigO {W H P H1 : ℕ → ℕ} (C k : ℕ)
    (hW : ∀ᶠ n : ℕ in atTop, W n * radix n ≤ wantedNumerator n)
    (hscore : ∀ᶠ n : ℕ in atTop, P n * H n ≤ scoreLoss k n * H1 n)
    (hinit : ∀ᶠ n : ℕ in atTop, H1 n ≤ candidateCount n * rawTripleBound n)
    (hmod : ∀ᶠ n : ℕ in atTop, radix n ≤ primeLoss radix n * P n) :
    (fun n : ℕ => (amplifiedCoreWork C W H n : ℝ)) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ targetExponent) := by
  apply _root_.Asymptotics.IsBigO.of_norm_eventuallyLE
  filter_upwards [amplifiedCoreWork_eventually_target C k hW hscore hinit hmod] with n hn
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg (α := ℝ) (amplifiedCoreWork C W H n)),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) targetExponent)] using hn

end
end ThreeSum.StageBounds
