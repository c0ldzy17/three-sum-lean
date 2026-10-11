import Submission.ThreeSum.HierarchyScales

/-!
# Actual wanted-incidence and false-mass majorants

The numerator of the wanted bound retains all raw A occurrences, all three
arithmetic lifts, and every schedule occurrence.  The false bound uses the
actual candidate count, integer band count, score loss, and modulus loss.
No asymptotic premise about an input-dependent mass is assumed here: the
transfer lemmas take the explicit finite inequalities from the counting
and prime-chain algorithms.
-/

namespace ThreeSum.MassScales

open Filter Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.TrimScales
  ThreeSum.BandScales ThreeSum.CostLedger ThreeSum.HierarchyScales
open scoped Topology

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def wantedNumerator (n : ℕ) : ℕ :=
  9 * scheduleCount n * typedOutputs n * bandCount n ^ 2 * bandSize n

def rawTripleBound (n : ℕ) : ℕ := 3 * bandCount n ^ 2 * bandSize n ^ 3

def falseNumerator (k n : ℕ) : ℕ :=
  candidateCount n * rawTripleBound n * scoreLoss k n * primeLoss radix n

theorem scheduleCount_pos (n : ℕ) : 0 < scheduleCount n :=
  Nat.pow_pos (localLength_pos _)

theorem bandCount_pos {n : ℕ} (hn : 0 < n) : 0 < bandCount n :=
  Nat.pos_of_mul_pos_left (hn.trans_le (bandCount_mul_bounds n).1)

theorem rawTripleBound_pos {n : ℕ} (hn : 0 < n) : 0 < rawTripleBound n := by
  have hB := bandCount_pos hn
  have hb := bandSize_pos n
  unfold rawTripleBound
  positivity

theorem wantedNumerator_pos {n : ℕ} (hn : 0 < n) : 0 < wantedNumerator n := by
  have hS := scheduleCount_pos n
  have hM := typedOutputs_pos n
  have hB := bandCount_pos hn
  have hb := bandSize_pos n
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) hS) hM)
    (Nat.pow_pos hB)) hb

theorem scoreLoss_pos (k n : ℕ) : 0 < scoreLoss k n := by
  unfold scoreLoss
  positivity

theorem primeLoss_pos (n : ℕ) : 0 < primeLoss radix n := by
  have hy := primeWindow_ge_two n
  unfold primeLoss
  positivity

theorem candidateCount_eventually_pos : ∀ᶠ n : ℕ in atTop, 0 < candidateCount n := by
  filter_upwards [actual_candidates_nonempty] with n hn
  exact Finset.card_pos.mpr hn

theorem falseNumerator_eventually_pos (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, 0 < falseNumerator k n := by
  filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have ht := rawTripleBound_pos (by omega : 0 < n)
  have hs := scoreLoss_pos k n
  have hp := primeLoss_pos n
  unfold falseNumerator
  positivity

noncomputable section

def wantedMajorant (n : ℕ) : ℝ := (wantedNumerator n : ℝ) / radix n

def falseMajorant (k n : ℕ) : ℝ := (falseNumerator k n : ℝ) / radix n

theorem nat_log_rate_const (c : ℕ) :
    Tendsto (fun n : ℕ => Real.log (c : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa only [mul_zero, Pi.inv_apply, div_eq_mul_inv] using
    Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log (c : ℝ))

theorem nat_log_rate_mul {f g : ℕ → ℕ} {a b : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hg : Tendsto (fun n : ℕ => Real.log (g n : ℝ) / Real.log n) atTop (𝓝 b))
    (hp : ∀ᶠ n : ℕ in atTop, 0 < f n ∧ 0 < g n) :
    Tendsto (fun n : ℕ => Real.log ((f n * g n : ℕ) : ℝ) / Real.log n) atTop (𝓝 (a + b)) := by
  apply (hf.add hg).congr'
  filter_upwards [hp] with n hn
  have hfR : (f n : ℝ) ≠ 0 := by exact_mod_cast hn.1.ne'
  have hgR : (g n : ℝ) ≠ 0 := by exact_mod_cast hn.2.ne'
  simp only [Nat.cast_mul, Real.log_mul hfR hgR, add_div]

theorem nat_log_rate_pow {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a)) (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log ((f n ^ k : ℕ) : ℝ) / Real.log n) atTop (𝓝 ((k : ℝ) * a)) := by
  simpa only [Nat.cast_pow, Real.log_pow, mul_div_assoc] using hf.const_mul (k : ℝ)

theorem candidateCount_le_window (n : ℕ) : candidateCount n ≤ 4 * primeWindow n := by
  unfold candidateCount PrimeDensity.candidates
  calc
    _ ≤ (Nat.primesLE (4 * primeWindow n)).card := Finset.card_le_card Finset.sdiff_subset
    _ ≤ 4 * primeWindow n := by
      rw [Nat.primesLE_eq_filter_Ioc_zero]
      exact (Finset.card_filter_le _ _).trans_eq (by simp)

theorem candidateCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (candidateCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hu := nat_log_rate_mul (nat_log_rate_const 4) primeWindow_log_ratio_tendsto_zero (by
    filter_upwards [] with n
    have hy := primeWindow_ge_two n
    omega)
  simp only [zero_add] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact div_nonneg (Real.log_nonneg (by exact_mod_cast hC))
      (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (by exact_mod_cast hC) (by exact_mod_cast candidateCount_le_window n))
      (Real.log_nonneg (by exact_mod_cast hn))

theorem bandSize_log_rate_shift :
    Tendsto (fun n : ℕ => Real.log (bandSize n : ℝ) / Real.log n) atTop
      (𝓝 ((E + bandShift) / 5)) := by
  simpa only [bandShift, sub_eq_add_neg] using BandScales.bandSize_log_rate

theorem wantedNumerator_log_rate :
    Tendsto (fun n : ℕ => Real.log (wantedNumerator n : ℝ) / Real.log n) atTop
      (𝓝 (2 + 2 * E / 5 - (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul (nat_log_rate_const 9) scheduleCount_log_rate (by
    filter_upwards [] with n
    exact ⟨by norm_num, scheduleCount_pos n⟩)
  have h2 := nat_log_rate_mul h1 typedOutputs_log_ratio_tendsto (by
    filter_upwards [] with n
    exact ⟨Nat.mul_pos (by norm_num) (scheduleCount_pos n), typedOutputs_pos n⟩)
  have h3 := nat_log_rate_mul h2 (nat_log_rate_pow bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (Nat.mul_pos (by norm_num) (scheduleCount_pos n)) (typedOutputs_pos n),
      Nat.pow_pos (bandCount_pos (by omega))⟩)
  have h4 := nat_log_rate_mul h3 bandSize_log_rate_shift (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    refine ⟨?_, bandSize_pos n⟩
    exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by norm_num) (scheduleCount_pos n))
      (typedOutputs_pos n)) (Nat.pow_pos (bandCount_pos (by omega))))
  convert h4 using 1 <;> simp only [wantedNumerator, Nat.cast_ofNat] <;> ring

theorem rawTripleBound_log_rate :
    Tendsto (fun n : ℕ => Real.log (rawTripleBound n : ℝ) / Real.log n) atTop
      (𝓝 (2 + (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul (nat_log_rate_const 3) (nat_log_rate_pow bandCount_log_rate 2) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨by norm_num, Nat.pow_pos (bandCount_pos (by omega))⟩)
  have h2 := nat_log_rate_mul h1 (nat_log_rate_pow bandSize_log_rate_shift 3) (by
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact ⟨Nat.mul_pos (by norm_num) (Nat.pow_pos (bandCount_pos (by omega))),
      Nat.pow_pos (bandSize_pos n)⟩)
  convert h2 using 1 <;> simp only [rawTripleBound, Nat.cast_ofNat] <;> ring

theorem falseNumerator_log_rate (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (falseNumerator k n : ℝ) / Real.log n) atTop
      (𝓝 (2 + (E + bandShift) / 5)) := by
  have h1 := nat_log_rate_mul candidateCount_log_rate rawTripleBound_log_rate (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨hC, rawTripleBound_pos (by omega)⟩)
  have h2 := nat_log_rate_mul h1 (scoreLoss_log_ratio_tendsto_zero k) (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos hC (rawTripleBound_pos (by omega)), scoreLoss_pos k n⟩)
  have h3 := nat_log_rate_mul h2 primeLoss_log_ratio_tendsto_zero (by
    filter_upwards [candidateCount_eventually_pos, eventually_ge_atTop (1 : ℕ)] with n hC hn
    exact ⟨Nat.mul_pos (Nat.mul_pos hC (rawTripleBound_pos (by omega))) (scoreLoss_pos k n),
      primeLoss_pos n⟩)
  simpa only [falseNumerator, zero_add, add_zero] using h3

theorem wantedMajorant_log_rate :
    Tendsto (fun n : ℕ => Real.log (wantedMajorant n) / Real.log n) atTop
      (𝓝 (2 - (1 / 2 + bandShift) / 5)) := by
  have hh := wantedNumerator_log_rate.sub radix_log_ratio_tendsto
  have hid : (2 + 2 * E / 5 - (E + bandShift) / 5) - (E + 1 / 2) / 5 =
      2 - (1 / 2 + bandShift) / 5 := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
  have hN : (wantedNumerator n : ℝ) ≠ 0 := by exact_mod_cast (wantedNumerator_pos (by omega : 0 < n)).ne'
  have hR : (radix n : ℝ) ≠ 0 := by exact_mod_cast (radix_pos n).ne'
  simp only [wantedMajorant, Real.log_div hN hR, sub_div]

theorem falseMajorant_log_rate (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (falseMajorant k n) / Real.log n) atTop
      (𝓝 (2 - (1 / 2 - bandShift) / 5)) := by
  have hh := (falseNumerator_log_rate k).sub radix_log_ratio_tendsto
  have hid : (2 + (E + bandShift) / 5) - (E + 1 / 2) / 5 =
      2 - (1 / 2 - bandShift) / 5 := by ring
  rw [hid] at hh
  apply hh.congr'
  filter_upwards [falseNumerator_eventually_pos k] with n hn
  have hN : (falseNumerator k n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hR : (radix n : ℝ) ≠ 0 := by exact_mod_cast (radix_pos n).ne'
  simp only [falseMajorant, Real.log_div hN hR, sub_div]

theorem wantedMajorant_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, wantedMajorant n ≤ (n : ℝ) ^ (2 - (1 / 2 + bandShift) / 5 + d) :=
  eventually_real_le_rpow_of_log_rate wantedMajorant_log_rate hd

theorem falseMajorant_eventually_le (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, falseMajorant k n ≤ (n : ℝ) ^ (2 - (1 / 2 - bandShift) / 5 + d) :=
  eventually_real_le_rpow_of_log_rate (falseMajorant_log_rate k) hd

theorem wanted_mass_le {n W : ℕ} (hW : W * radix n ≤ wantedNumerator n) :
    (W : ℝ) ≤ wantedMajorant n := by
  rw [wantedMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
  exact_mod_cast hW

theorem false_mass_le {n k P H H1 : ℕ}
    (hscore : P * H ≤ scoreLoss k n * H1)
    (hinit : H1 ≤ candidateCount n * rawTripleBound n)
    (hmod : radix n ≤ primeLoss radix n * P) :
    (H : ℝ) ≤ falseMajorant k n := by
  have hbound : H * radix n ≤ falseNumerator k n := by
    calc
      H * radix n ≤ primeLoss radix n * (P * H) := by
        simpa only [mul_assoc, mul_comm, mul_left_comm] using Nat.mul_le_mul_left H hmod
      _ ≤ primeLoss radix n * (scoreLoss k n * H1) := Nat.mul_le_mul_left _ hscore
      _ ≤ primeLoss radix n * (scoreLoss k n * (candidateCount n * rawTripleBound n)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hinit)
      _ = falseNumerator k n := by unfold falseNumerator; ring
  rw [falseMajorant, le_div_iff₀ (show (0 : ℝ) < radix n by exact_mod_cast radix_pos n)]
  exact_mod_cast hbound

end
end ThreeSum.MassScales
