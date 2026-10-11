import Submission.ThreeSum.BinomialEntropy
import Submission.ThreeSum.Asymptotics
import Submission.ThreeSum.PrimeDensity
import Submission.ThreeSum.LocalCoverBounds
import Mathlib.Analysis.SpecialFunctions.Pow.NthRootLemmas
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Sqrt

/-!
# The actual integer block schedule

All four size parameters below are executable natural-number functions.
The finite bounds and limits concern these functions, including the even
rounding of the cube root and the divisibility constraints on the number
of blocks.  No asymptotic size premise is imposed on the schedule.
-/

namespace ThreeSum.Scales

open Filter Real
open scoped Topology

def inputBits (n : ℕ) : ℕ := Nat.log2 n

def microSize (m : ℕ) : ℕ := 2 * (Nat.nthRoot 3 m / 2)

def blockCount (m : ℕ) : ℕ := 20 * (m / (100 * microSize m))

def totalSize (m : ℕ) : ℕ := blockCount m * microSize m

def muZero (n : ℕ) : ℕ := microSize (inputBits n)

def mu (n : ℕ) : ℕ := totalSize (inputBits n)

def typedOutputs (n : ℕ) : ℕ :=
  ((256 * muZero n).choose (muZero n)) ^ blockCount (inputBits n)

def localSearch (C n : ℕ) : ℕ := 2 ^ (C * muZero n ^ 2)

def scheduleFactor (C n : ℕ) : ℕ :=
  (256 * muZero n + 1) ^ (C * blockCount (inputBits n))

/-- For integral `m`, `sqrt m + 1` is exactly `ceil(sqrt(m+1))`. -/
def windowExponent (m : ℕ) : ℕ := Nat.sqrt m + 1

def primeWindow (n : ℕ) : ℕ := 2 ^ windowExponent (inputBits n)

def primeDepth (R : ℕ → ℕ) (n : ℕ) : ℕ :=
  Nat.log (4 * primeWindow n) (R n / 4)

def primeLoss (R : ℕ → ℕ) (n : ℕ) : ℕ :=
  32 * primeWindow n * 4 ^ primeDepth R n

def microHalf (m : ℕ) : ℕ := Nat.nthRoot 3 m / 2

def localRadix (n : ℕ) : ℕ := LocalCoverBounds.localPrime (microHalf (inputBits n))

def radix (n : ℕ) : ℕ := localRadix n ^ blockCount (inputBits n)

def divisorBudget (k n : ℕ) : ℕ := Nat.log (primeWindow n) (3 * n ^ k)

def scoreLoss (k n : ℕ) : ℕ :=
  (16 * (k + 2) * (inputBits n + 1)) ^ primeDepth radix n

def candidateCount (n : ℕ) : ℕ := (PrimeDensity.candidates (primeWindow n)).card

theorem microSize_even (m : ℕ) : 2 ∣ microSize m := by
  exact ⟨Nat.nthRoot 3 m / 2, rfl⟩

theorem blockCount_multiple_twenty (m : ℕ) : 20 ∣ blockCount m := by
  exact ⟨m / (100 * microSize m), rfl⟩

theorem microSize_rounding (m : ℕ) :
    microSize m ≤ Nat.nthRoot 3 m ∧ Nat.nthRoot 3 m < microSize m + 2 := by
  have h := Nat.mod_add_div (Nat.nthRoot 3 m) 2
  have hr := Nat.mod_lt (Nat.nthRoot 3 m) (by decide : 0 < 2)
  unfold microSize
  omega

theorem microSize_cube_le (m : ℕ) : microSize m ^ 3 ≤ m := by
  exact (Nat.pow_le_pow_left (microSize_rounding m).1 3).trans
    (Nat.pow_nthRoot_le (Or.inl (by decide : 3 ≠ 0)))

theorem cube_lt_microSize_add_three (m : ℕ) : m < (microSize m + 3) ^ 3 := by
  have hroot := Nat.lt_pow_nthRoot_add_one (by decide : 3 ≠ 0) m
  have hround := (microSize_rounding m).2
  exact hroot.trans_le (Nat.pow_le_pow_left (by omega :
    Nat.nthRoot 3 m + 1 ≤ microSize m + 3) 3)

theorem totalSize_upper (m : ℕ) : 5 * totalSize m ≤ m := by
  have h := Nat.div_mul_le_self m (100 * microSize m)
  convert h using 1 <;> simp only [totalSize, blockCount] <;> ring

theorem totalSize_lower {m : ℕ} (hm : 0 < microSize m) :
    m < 5 * totalSize m + 100 * microSize m := by
  have hmod := Nat.mod_lt m (by omega : 0 < 100 * microSize m)
  have hdiv := Nat.mod_add_div m (100 * microSize m)
  have heq : 5 * totalSize m = 100 * microSize m * (m / (100 * microSize m)) := by
    simp only [totalSize, blockCount]
    ring
  omega

noncomputable section

theorem microSize_tendsto_atTop : Tendsto microSize atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop ((b + 2) ^ 3)] with m hm
  have hr : b + 2 ≤ Nat.nthRoot 3 m :=
    (Nat.le_nthRoot_iff (by decide : 3 ≠ 0)).mpr hm
  have hround := (microSize_rounding m).2
  omega

theorem microSize_cast_tendsto_atTop :
    Tendsto (fun m : ℕ => (microSize m : ℝ)) atTop atTop :=
  tendsto_natCast_atTop_atTop.comp microSize_tendsto_atTop

theorem microSize_inv_tendsto_zero :
    Tendsto (fun m : ℕ => (microSize m : ℝ)⁻¹) atTop (𝓝 0) :=
  microSize_cast_tendsto_atTop.inv_tendsto_atTop

theorem microSize_square_ratio_bound {m : ℕ} (hm : 0 < microSize m) :
    (microSize m : ℝ) ^ 2 / m ≤ (microSize m : ℝ)⁻¹ := by
  have hx : (0 : ℝ) < microSize m := by exact_mod_cast hm
  have hcube : (microSize m : ℝ) ^ 3 ≤ (m : ℝ) := by
    exact_mod_cast microSize_cube_le m
  have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hcube
  apply (div_le_iff₀ hmpos).mpr
  rw [mul_comm ((microSize m : ℝ)⁻¹) (m : ℝ)]
  change (microSize m : ℝ) ^ 2 ≤ (m : ℝ) / microSize m
  apply (le_div_iff₀ hx).mpr
  nlinarith [hcube]

theorem microSize_square_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (microSize m : ℝ) ^ 2 / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ microSize_inv_tendsto_zero
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    exact microSize_square_ratio_bound (by omega)

theorem microSize_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (microSize m : ℝ) / m) atTop (𝓝 0) := by
  apply squeeze_zero' _ _ microSize_square_ratio_tendsto_zero
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hmr : (1 : ℝ) ≤ microSize m := by exact_mod_cast hm
    exact div_le_div_of_nonneg_right (by nlinarith) (Nat.cast_nonneg m)

theorem totalSize_real_bounds {m : ℕ} (hm : 0 < microSize m) :
    (m : ℝ) / 5 - 20 * microSize m < totalSize m ∧
      (totalSize m : ℝ) ≤ (m : ℝ) / 5 := by
  have hu : (5 : ℝ) * totalSize m ≤ (m : ℝ) := by
    exact_mod_cast totalSize_upper m
  have hl : (m : ℝ) < 5 * totalSize m + 100 * microSize m := by
    exact_mod_cast totalSize_lower hm
  constructor <;> linarith

theorem totalSize_ratio_tendsto :
    Tendsto (fun m : ℕ => (totalSize m : ℝ) / m) atTop (𝓝 (1 / 5)) := by
  have hlo : Tendsto (fun m : ℕ => (1 / 5 : ℝ) - 20 * ((microSize m : ℝ) / m))
      atTop (𝓝 (1 / 5)) := by
    simpa using tendsto_const_nhds.sub (microSize_ratio_tendsto_zero.const_mul 20)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop (1 : ℕ)] with m hm hmpos
    have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hl := (totalSize_real_bounds (by omega : 0 < microSize m)).1.le
    apply (le_div_iff₀ hmp).mpr
    calc
      _ = (m : ℝ) / 5 - 20 * microSize m := by field_simp
      _ ≤ _ := hl
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    apply (div_le_iff₀ hmp).mpr
    have hu : (5 : ℝ) * totalSize m ≤ (m : ℝ) := by
      exact_mod_cast totalSize_upper m
    linarith

theorem inputBits_eq_floor (n : ℕ) : inputBits n = ⌊Real.logb 2 (n : ℝ)⌋₊ := by
  rw [inputBits, Nat.log2_eq_log_two]
  exact (Real.natFloor_logb_natCast 2 n).symm

theorem inputBits_tendsto_atTop : Tendsto inputBits atTop atTop := by
  have h := tendsto_nat_floor_atTop.comp
    ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  simpa [Function.comp_def, ← inputBits_eq_floor] using h

theorem inputBits_log_ratio_tendsto :
    Tendsto (fun n : ℕ => (inputBits n : ℝ) / Real.log n) atTop
      (𝓝 (1 / Real.log 2)) := by
  have h := tendsto_nat_floor_div_atTop.comp
    ((Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ)))
  have h' := h.div_const (Real.log 2)
  convert h' using 1
  funext n
  simp only [Function.comp_def, ← inputBits_eq_floor]
  rw [Real.logb, div_div, div_mul_cancel₀ _ Parameters.log_two_pos.ne']

theorem mu_log_ratio_tendsto :
    Tendsto (fun n : ℕ => (mu n : ℝ) / Real.log n) atTop
      (𝓝 (1 / (5 * Real.log 2))) := by
  have h := (totalSize_ratio_tendsto.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto
  have hlim : (1 / 5 : ℝ) * (1 / Real.log 2) = 1 / (5 * Real.log 2) := by ring
  rw [hlim] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, mu]
  field_simp

theorem muZero_tendsto_atTop : Tendsto muZero atTop atTop :=
  microSize_tendsto_atTop.comp inputBits_tendsto_atTop

theorem muZero_square_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (muZero n : ℝ) ^ 2 / Real.log n) atTop (𝓝 0) := by
  have h := (microSize_square_ratio_tendsto_zero.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto
  simp only [zero_mul] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, muZero]
  field_simp

theorem microSize_real_root_bounds (m : ℕ) :
    (microSize m : ℝ) ≤ (m : ℝ) ^ (1 / 3 : ℝ) ∧
      (m : ℝ) ^ (1 / 3 : ℝ) < (microSize m : ℝ) + 3 := by
  simp only [one_div]
  constructor
  · apply (Real.le_rpow_inv_iff_of_pos (Nat.cast_nonneg (microSize m)) (Nat.cast_nonneg m)
      (by norm_num : (0 : ℝ) < 3)).mpr
    norm_num only [Real.rpow_natCast]
    exact_mod_cast microSize_cube_le m
  · apply (Real.rpow_inv_lt_iff_of_pos (Nat.cast_nonneg m)
      (by positivity : (0 : ℝ) ≤ (microSize m : ℝ) + 3)
      (by norm_num : (0 : ℝ) < 3)).mpr
    norm_num only [Real.rpow_natCast]
    exact_mod_cast cube_lt_microSize_add_three m

theorem microSize_root_ratio_tendsto :
    Tendsto (fun m : ℕ => (microSize m : ℝ) / (m : ℝ) ^ (1 / 3 : ℝ)) atTop
      (𝓝 1) := by
  have hroot : Tendsto (fun m : ℕ => (m : ℝ) ^ (1 / 3 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp tendsto_natCast_atTop_atTop
  have hlo : Tendsto (fun m : ℕ => (1 : ℝ) - 3 * ((m : ℝ) ^ (1 / 3 : ℝ))⁻¹)
      atTop (𝓝 1) := by
    simpa using tendsto_const_nhds.sub (hroot.inv_tendsto_atTop.const_mul 3)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo tendsto_const_nhds
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hp : 0 < (m : ℝ) ^ (1 / 3 : ℝ) := by positivity
    have hl := (microSize_real_root_bounds m).2
    apply (le_div_iff₀ hp).mpr
    have heq : (1 - 3 * ((m : ℝ) ^ (1 / 3 : ℝ))⁻¹) * (m : ℝ) ^ (1 / 3 : ℝ) =
        (m : ℝ) ^ (1 / 3 : ℝ) - 3 := by field_simp
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hp : 0 < (m : ℝ) ^ (1 / 3 : ℝ) := by positivity
    apply (div_le_iff₀ hp).mpr
    simpa using (microSize_real_root_bounds m).1

theorem typedOutputs_log_ratio_tendsto :
    Tendsto (fun n : ℕ => Real.log (typedOutputs n : ℝ) / Real.log n) atTop
      (𝓝 (2 * Parameters.E / 5)) := by
  have hl := BinomialEntropy.output_table_rate.comp muZero_tendsto_atTop
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : 2 * Parameters.E * (Real.log 2 * (1 / (5 * Real.log 2))) =
      2 * Parameters.E / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (muZero n : ℝ) ≠ 0 := by exact_mod_cast (by omega : muZero n ≠ 0)
  simp only [Function.comp_def, typedOutputs, Nat.cast_pow, Real.log_pow]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) * muZero n := by
    simp [mu, totalSize, muZero]
  rw [hmu]
  field_simp

theorem localSearch_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (localSearch C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := muZero_square_log_ratio_tendsto_zero.const_mul ((C : ℝ) * Real.log 2)
  simpa [localSearch, Nat.cast_pow, Nat.cast_mul, Real.log_pow, mul_div_assoc,
    mul_comm, mul_left_comm, mul_assoc] using h

theorem scheduleFactor_log_ratio_tendsto_zero (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (scheduleFactor C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have he := (BinomialEntropy.logarithmic_error_tendsto_zero
    (c := 256) (by norm_num)).comp muZero_tendsto_atTop
  have h := (he.mul mu_log_ratio_tendsto).const_mul (C : ℝ)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (muZero n : ℝ) ≠ 0 := by exact_mod_cast (by omega : muZero n ≠ 0)
  simp only [Function.comp_def, scheduleFactor, Nat.cast_pow, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, Real.log_pow]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) * muZero n := by
    simp [mu, totalSize, muZero]
  rw [hmu]
  field_simp

/-- Converts a proved logarithmic rate into a power bound; the concrete
table and construction functions are instantiated immediately below. -/
theorem eventually_le_rpow_of_log_ratio {f : ℕ → ℕ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n : ℝ) / Real.log n) atTop (𝓝 a))
    (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (f n : ℝ) ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hnp : (1 : ℝ) < n := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log n := Real.log_pos hnp
  exact Real.le_rpow_of_log_le (by linarith) ((div_lt_iff₀ hlog).mp hn).le

theorem localSearch_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (localSearch C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio (localSearch_log_ratio_tendsto_zero C) hd

theorem scheduleFactor_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (scheduleFactor C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio (scheduleFactor_log_ratio_tendsto_zero C) hd

theorem typedOutputs_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (typedOutputs n : ℝ) ≤ (n : ℝ) ^ (2 * Parameters.E / 5 + d) :=
  eventually_le_rpow_of_log_ratio typedOutputs_log_ratio_tendsto hd

theorem natSqrt_tendsto_atTop : Tendsto Nat.sqrt atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [eventually_ge_atTop (b ^ 2)] with m hm
  exact Nat.le_sqrt'.mpr hm

theorem natSqrt_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (Nat.sqrt m : ℝ) / m) atTop (𝓝 0) := by
  have hinv := ((tendsto_natCast_atTop_atTop (R := ℝ)).comp natSqrt_tendsto_atTop).inv_tendsto_atTop
  apply squeeze_zero' _ _ hinv
  · exact Filter.Eventually.of_forall (fun m => by positivity)
  · filter_upwards [natSqrt_tendsto_atTop.eventually (eventually_ge_atTop 1)] with m hm
    have hx : (0 : ℝ) < Nat.sqrt m := by exact_mod_cast (by omega : 0 < Nat.sqrt m)
    have hs : (Nat.sqrt m : ℝ) ^ 2 ≤ (m : ℝ) := by exact_mod_cast Nat.sqrt_le' m
    have hmpos : (0 : ℝ) < m := lt_of_lt_of_le (by positivity) hs
    apply (div_le_iff₀ hmpos).mpr
    change (Nat.sqrt m : ℝ) ≤ (Nat.sqrt m : ℝ)⁻¹ * m
    rw [mul_comm ((Nat.sqrt m : ℝ)⁻¹) (m : ℝ)]
    change (Nat.sqrt m : ℝ) ≤ (m : ℝ) / Nat.sqrt m
    apply (le_div_iff₀ hx).mpr
    nlinarith [hs]

theorem windowExponent_ratio_tendsto_zero :
    Tendsto (fun m : ℕ => (windowExponent m : ℝ) / m) atTop (𝓝 0) := by
  have h := natSqrt_ratio_tendsto_zero.add
    (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  simpa [windowExponent, Nat.cast_add, add_div, one_div] using h

theorem primeWindow_ge_two (n : ℕ) : 2 ≤ primeWindow n := by
  unfold primeWindow windowExponent
  rw [pow_succ]
  have hp : 0 < 2 ^ Nat.sqrt (inputBits n) := by positivity
  omega

theorem primeWindow_tendsto_atTop : Tendsto primeWindow atTop atTop := by
  have hs := natSqrt_tendsto_atTop.comp inputBits_tendsto_atTop
  apply tendsto_atTop.2
  intro b
  filter_upwards [hs.eventually (eventually_ge_atTop b)] with n hn
  have hp : Nat.sqrt (inputBits n) + 1 < 2 ^ (Nat.sqrt (inputBits n) + 1) :=
    Nat.lt_pow_self (by decide : 1 < 2)
  change b ≤ 2 ^ (Nat.sqrt (inputBits n) + 1)
  exact hn.trans ((Nat.le_succ _).trans hp.le)

theorem primeWindow_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have h := ((windowExponent_ratio_tendsto_zero.comp inputBits_tendsto_atTop).mul
    inputBits_log_ratio_tendsto).const_mul (Real.log 2)
  simp only [zero_mul, mul_zero] at h
  apply h.congr'
  filter_upwards [inputBits_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (inputBits n : ℝ) ≠ 0 := by exact_mod_cast (by omega : inputBits n ≠ 0)
  simp only [Function.comp_def, primeWindow, Nat.cast_pow, Real.log_pow, Nat.cast_ofNat]
  field_simp

theorem primeWindow_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (primeWindow n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio primeWindow_log_ratio_tendsto_zero hd

theorem actual_candidate_density :
    ∀ᶠ n : ℕ in atTop,
      (primeWindow n : ℝ) / (4 * Real.log (primeWindow n)) ≤
        (PrimeDensity.candidates (primeWindow n)).card :=
  primeWindow_tendsto_atTop.eventually PrimeDensity.eventually_candidate_density

theorem actual_candidates_nonempty :
    ∀ᶠ n : ℕ in atTop, (PrimeDensity.candidates (primeWindow n)).Nonempty :=
  primeWindow_tendsto_atTop.eventually PrimeDensity.eventually_candidates_nonempty

theorem primeDepth_upper (R : ℕ → ℕ) {n : ℕ} (hR : 4 ≤ R n) :
    4 * (4 * primeWindow n) ^ primeDepth R n ≤ R n := by
  have hr : R n / 4 ≠ 0 := by omega
  have h := Nat.pow_log_le_self (4 * primeWindow n) hr
  have h4 := Nat.mul_le_mul_left 4 h
  have hd := Nat.div_mul_le_self (R n) 4
  simpa [primeDepth, Nat.mul_comm] using h4.trans (by simpa [Nat.mul_comm] using hd)

/-- The greedy depth loses only `32*y*4^r` compared with the target radix.
This applies to the actual selected product as soon as its finite `y^r`
lower bound from `PrimeChain.modulus_bounds` is supplied. -/
theorem primeDepth_loss_bound (R : ℕ → ℕ) {n P : ℕ}
    (hP : primeWindow n ^ primeDepth R n ≤ P) :
    R n ≤ primeLoss R n * P := by
  have hy := primeWindow_ge_two n
  have hr := Nat.lt_pow_succ_log_self (by omega : 1 < 4 * primeWindow n) (R n / 4)
  simp only [Nat.succ_eq_add_one] at hr
  have hmod := Nat.mod_lt (R n) (by decide : 0 < 4)
  have hdiv := Nat.mod_add_div (R n) 4
  have hbase : R n < 4 * (4 * primeWindow n) ^ (primeDepth R n + 1) := by
    simp only [primeDepth] at ⊢
    omega
  have heq : 4 * (4 * primeWindow n) ^ (primeDepth R n + 1) =
      16 * primeWindow n * 4 ^ primeDepth R n * primeWindow n ^ primeDepth R n := by
    rw [pow_succ, mul_pow]
    ring
  rw [heq] at hbase
  have hm := Nat.mul_le_mul_left (16 * primeWindow n * 4 ^ primeDepth R n) hP
  apply hbase.le.trans (hm.trans ?_)
  unfold primeLoss
  nlinarith [Nat.zero_le (primeWindow n * 4 ^ primeDepth R n * P)]

theorem microHalf_tendsto_atTop : Tendsto microHalf atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [microSize_tendsto_atTop.eventually (eventually_ge_atTop (2 * b))] with m hm
  change 2 * microHalf m ≥ 2 * b at hm
  omega

theorem muZero_eq_twice_half (n : ℕ) : muZero n = 2 * microHalf (inputBits n) := rfl

theorem even_output_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * Parameters.E)) := by
  have ht : Tendsto (fun h : ℕ => 2 * h) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop b] with h hh
    omega
  have hr := BinomialEntropy.output_table_rate.comp ht
  convert hr using 1
  funext h
  simp only [Function.comp_def, LocalCoverBounds.outputCount, Nat.cast_mul, Nat.cast_ofNat]
  rw [show 256 * (2 * h) = 512 * h by omega]

theorem localThreshold_log_formula (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) =
      Real.log (LocalCoverBounds.outputCount (512 * h) h : ℝ) +
        (2 * h : ℝ) * Real.log 2 := by
  have hM : (0 : ℝ) < LocalCoverBounds.outputCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : 2 * h ≤ 512 * h))
  simp only [LocalCoverBounds.localThreshold, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (ne_of_gt hM) (by positivity), Real.log_pow]
  simp

theorem localThreshold_log_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localThreshold h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (2 * Parameters.E + 1)) := by
  have hs := even_output_rate.add (tendsto_const_nhds (x := (1 : ℝ)))
  apply hs.congr'
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
  have hpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  rw [localThreshold_log_formula]
  field_simp

theorem localPrime_log_interval (h : ℕ) :
    Real.log (LocalCoverBounds.localThreshold h : ℝ) ≤
      2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ∧
    2 * Real.log (LocalCoverBounds.localPrime h : ℝ) ≤
      Real.log 16 + Real.log (LocalCoverBounds.localThreshold h : ℝ) := by
  have hN : (0 : ℝ) < LocalCoverBounds.localThreshold h := by
    exact_mod_cast LocalCoverBounds.localThreshold_pos h
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  have hl : (LocalCoverBounds.localThreshold h : ℝ) ≤
      (LocalCoverBounds.localPrime h : ℝ) ^ 2 := by
    exact_mod_cast LocalCoverBounds.localPrime_sq_lower h
  have hu : (LocalCoverBounds.localPrime h : ℝ) ^ 2 ≤
      16 * (LocalCoverBounds.localThreshold h : ℝ) := by
    exact_mod_cast LocalCoverBounds.localPrime_sq_upper h
  constructor
  · simpa [Real.log_pow] using Real.log_le_log hN hl
  · simpa [Real.log_pow, Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) hN.ne'] using
      Real.log_le_log (by positivity : (0 : ℝ) < (LocalCoverBounds.localPrime h : ℝ) ^ 2) hu

theorem localPrime_log_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localPrime h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (Parameters.E + 1 / 2)) := by
  have hmain := localThreshold_log_rate.div_const 2
  have hmain' : Tendsto (fun h : ℕ =>
      Real.log (LocalCoverBounds.localThreshold h : ℝ) / ((2 * h : ℝ) * Real.log 2) / 2)
      atTop (𝓝 (Parameters.E + 1 / 2)) := by
    convert hmain using 1 <;> ring
  have herr : Tendsto (fun h : ℕ => Real.log 16 / ((4 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 16 / (4 * Real.log 2))
  have hupper := hmain'.add herr
  simp only [add_zero] at hupper
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hmain' hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (localPrime_log_interval h).1
    apply (le_div_iff₀ hden).mpr
    have heq : (Real.log (LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2) * ((2 * h : ℝ) * Real.log 2) =
        Real.log (LocalCoverBounds.localThreshold h : ℝ) / 2 := by field_simp
    rw [heq]
    linarith
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
    have hi := (localPrime_log_interval h).2
    apply (div_le_iff₀ hden).mpr
    have heq : (Real.log (LocalCoverBounds.localThreshold h : ℝ) /
        ((2 * h : ℝ) * Real.log 2) / 2 + Real.log 16 / ((4 * h : ℝ) * Real.log 2)) *
        ((2 * h : ℝ) * Real.log 2) =
        (Real.log (LocalCoverBounds.localThreshold h : ℝ) + Real.log 16) / 2 := by field_simp; ring
    rw [heq]
    linarith

theorem radix_log_ratio_tendsto :
    Tendsto (fun n : ℕ => Real.log (radix n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E + 1 / 2) / 5)) := by
  have hl := localPrime_log_rate.comp (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop)
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : (Parameters.E + 1 / 2) * (Real.log 2 * (1 / (5 * Real.log 2))) =
      (Parameters.E + 1 / 2) / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ microHalf (inputBits n) at hn
  have hn0 : (microHalf (inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, radix, Nat.cast_pow, Real.log_pow, localRadix]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) *
      (2 * microHalf (inputBits n)) := by simp [mu, totalSize, microSize, microHalf]
  rw [hmu]
  field_simp

theorem radix_pos (n : ℕ) : 0 < radix n := by
  unfold radix localRadix
  exact Nat.pow_pos (LocalCoverBounds.localPrime_pos _)

theorem radix_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (radix n : ℝ)) atTop atTop := by
  have hpositive : (0 : ℝ) < (Parameters.E + 1 / 2) / 5 := by
    have h := Parameters.E_bounds.1
    linarith
  have h := radix_log_ratio_tendsto.pos_mul_atTop hpositive
    Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem radix_eventually_ge_four : ∀ᶠ n : ℕ in atTop, 4 ≤ radix n := by
  filter_upwards [radix_log_tendsto_atTop.eventually (eventually_ge_atTop (Real.log 4))] with n hn
  have hr : (0 : ℝ) < radix n := by exact_mod_cast radix_pos n
  have h : (4 : ℝ) ≤ radix n := (Real.log_le_log_iff (by norm_num) hr).mp hn
  exact_mod_cast h

theorem primeDepth_log_bound {n : ℕ} (hR : 4 ≤ radix n) :
    (primeDepth radix n : ℝ) * Real.log (4 * primeWindow n : ℝ) ≤
      Real.log (radix n : ℝ) := by
  have hp := primeDepth_upper radix hR
  have hpow : (4 * primeWindow n) ^ primeDepth radix n ≤ radix n := by omega
  have hpos : (0 : ℝ) < ((4 * primeWindow n : ℕ) : ℝ) ^ primeDepth radix n := by
    have hy := primeWindow_ge_two n
    positivity
  have hpowR : ((4 * primeWindow n : ℕ) : ℝ) ^ primeDepth radix n ≤ (radix n : ℝ) := by
    exact_mod_cast hpow
  have hl := Real.log_le_log hpos hpowR
  simpa only [Nat.cast_mul, Nat.cast_ofNat, Real.log_pow] using hl

theorem primeBase_log_tendsto_atTop :
    Tendsto (fun n : ℕ => Real.log (4 * primeWindow n : ℝ)) atTop atTop := by
  have hy := (tendsto_natCast_atTop_atTop (R := ℝ)).comp primeWindow_tendsto_atTop
  exact Real.tendsto_log_atTop.comp (hy.const_mul_atTop (by norm_num : (0 : ℝ) < 4))

theorem primeDepth_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => (primeDepth radix n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hupper := radix_log_ratio_tendsto.mul primeBase_log_tendsto_atTop.inv_tendsto_atTop
  simp only [mul_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Nat.cast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [radix_eventually_ge_four, eventually_ge_atTop (2 : ℕ)] with n hR hn
    have hy := primeWindow_ge_two n
    have hb : (0 : ℝ) < Real.log (4 * primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * primeWindow n))
    have hlog : (0 : ℝ) < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hdepth := (le_div_iff₀ hb).mpr (primeDepth_log_bound hR)
    have hd := div_le_div_of_nonneg_right hdepth hlog.le
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc, Pi.inv_apply] using hd

theorem primeLoss_log_ratio_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (primeLoss radix n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hc := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 32)
  have hd := primeDepth_log_ratio_tendsto_zero.const_mul (Real.log 4)
  have h := (hc.add primeWindow_log_ratio_tendsto_zero).add hd
  simp only [mul_zero, zero_add, add_zero] at h
  apply h.congr'
  filter_upwards [] with n
  have hy : (primeWindow n : ℝ) ≠ 0 := by exact_mod_cast (by have := primeWindow_ge_two n; omega : primeWindow n ≠ 0)
  simp only [primeLoss, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [Real.log_mul (mul_ne_zero (by norm_num) hy) (by positivity),
    Real.log_mul (by norm_num : (32 : ℝ) ≠ 0) hy, Real.log_pow]
  simp only [add_div, Pi.inv_apply]
  ring

theorem primeLoss_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (primeLoss radix n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio primeLoss_log_ratio_tendsto_zero hd

theorem modulus_eventually_ge_radix_div_power {P : ℕ → ℕ}
    (hP : ∀ᶠ n : ℕ in atTop, primeWindow n ^ primeDepth radix n ≤ P n)
    {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (radix n : ℝ) / (n : ℝ) ^ d ≤ P n := by
  filter_upwards [hP, primeLoss_subpolynomial hd, eventually_ge_atTop (1 : ℕ)] with n hP hn hnpos
  have hbound : (radix n : ℝ) ≤ (primeLoss radix n : ℝ) * P n := by
    exact_mod_cast primeDepth_loss_bound radix hP
  have hbound' : (radix n : ℝ) ≤ (n : ℝ) ^ d * P n :=
    hbound.trans (mul_le_mul_of_nonneg_right hn (Nat.cast_nonneg _))
  have hnp : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) ^ d)).mpr
  simpa only [mul_comm] using hbound'

theorem input_log_le_bits_add_one {n : ℕ} (hn : 0 < n) :
    Real.log (n : ℝ) ≤ inputBits n + 1 := by
  have hpow : n ≤ 2 ^ (inputBits n + 1) := by
    simpa [inputBits, Nat.log2_eq_log_two, Nat.succ_eq_add_one] using
      (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n).le
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hpowR : (n : ℝ) ≤ (2 : ℝ) ^ (inputBits n + 1) := by exact_mod_cast hpow
  have hl := Real.log_le_log hnpos hpowR
  rw [Real.log_pow] at hl
  have htwo : Real.log 2 ≤ 1 := by have := Parameters.log_two_upper; linarith
  have hm : (0 : ℝ) ≤ inputBits n + 1 := by positivity
  exact hl.trans (by simpa using mul_le_of_le_one_right hm htwo)

theorem log_difference_bound (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Real.log (3 * n ^ k : ℝ) ≤ ((k : ℝ) + 2) * (inputBits n + 1) := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by positivity), Real.log_pow]
  have hthree : Real.log 3 ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h
    exact h
  have hprod := mul_le_mul_of_nonneg_left (input_log_le_bits_add_one hn) (Nat.cast_nonneg k)
  have hm : (0 : ℝ) ≤ inputBits n := Nat.cast_nonneg _
  nlinarith [hm]

theorem actual_divisor_budget (k : ℕ) :
    ∀ᶠ n : ℕ in atTop,
      divisorBudget k n * primeWindow n ≤
        (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)) := by
  filter_upwards [actual_candidate_density, eventually_ge_atTop (1 : ℕ)] with n hC hn
  have hy := primeWindow_ge_two n
  have hlog : 0 < Real.log (primeWindow n : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
  have hK : (divisorBudget k n : ℝ) ≤
      Real.log (3 * n ^ k : ℝ) / Real.log (primeWindow n : ℝ) := by
    simpa [divisorBudget, Real.logb] using
      Real.natLog_le_logb (3 * n ^ k) (primeWindow n)
  have hKmul := (le_div_iff₀ hlog).mp hK
  have hCmul := (div_le_iff₀ (by positivity : (0 : ℝ) < 4 * Real.log (primeWindow n : ℝ))).mp hC
  have hdiff := log_difference_bound k (by omega : 0 < n)
  have hr : (divisorBudget k n : ℝ) * primeWindow n ≤
      ((PrimeDensity.candidates (primeWindow n)).card : ℝ) *
        (4 * ((k : ℝ) + 2) * (inputBits n + 1)) := by
    calc
      (divisorBudget k n : ℝ) * primeWindow n ≤
          (divisorBudget k n : ℝ) *
            (((PrimeDensity.candidates (primeWindow n)).card : ℝ) *
              (4 * Real.log (primeWindow n : ℝ))) :=
        mul_le_mul_of_nonneg_left hCmul (Nat.cast_nonneg _)
      _ = (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          ((divisorBudget k n : ℝ) * Real.log (primeWindow n : ℝ)) := by ring
      _ ≤ (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          Real.log (3 * n ^ k : ℝ) := mul_le_mul_of_nonneg_left hKmul (by positivity)
      _ ≤ (4 * (PrimeDensity.candidates (primeWindow n)).card : ℝ) *
          (((k : ℝ) + 2) * (inputBits n + 1)) := mul_le_mul_of_nonneg_left hdiff (by positivity)
      _ = _ := by ring
  exact_mod_cast hr

/-- A finite algebraic transfer of the actual prime-chain contraction to
the explicit accumulated score loss. The two count inequalities are the
outputs of `PrimeChain.modulus_score_bound` and `modulus_bounds`. -/
theorem scoreLoss_finite_bound {k n H H₁ P : ℕ}
    (hC : 0 < (PrimeDensity.candidates (primeWindow n)).card)
    (hbudget : divisorBudget k n * primeWindow n ≤
      (PrimeDensity.candidates (primeWindow n)).card * (4 * (k + 2) * (inputBits n + 1)))
    (hcontract : (PrimeDensity.candidates (primeWindow n)).card ^ primeDepth radix n * H ≤
      divisorBudget k n ^ primeDepth radix n * H₁)
    (hP : P ≤ (4 * primeWindow n) ^ primeDepth radix n) :
    P * H ≤ scoreLoss k n * H₁ := by
  let C := (PrimeDensity.candidates (primeWindow n)).card
  let r := primeDepth radix n
  let A := 4 * (k + 2) * (inputBits n + 1)
  have hpow := Nat.pow_le_pow_left hbudget r
  have hbig : C ^ r * (primeWindow n ^ r * H) ≤ C ^ r * (A ^ r * H₁) := by
    calc
      C ^ r * (primeWindow n ^ r * H) = primeWindow n ^ r * (C ^ r * H) := by ring
      _ ≤ primeWindow n ^ r * (divisorBudget k n ^ r * H₁) :=
        Nat.mul_le_mul_left _ hcontract
      _ = (divisorBudget k n * primeWindow n) ^ r * H₁ := by rw [mul_pow]; ring
      _ ≤ (C * A) ^ r * H₁ := Nat.mul_le_mul_right _ hpow
      _ = C ^ r * (A ^ r * H₁) := by rw [mul_pow]; ring
  have hsmall : primeWindow n ^ r * H ≤ A ^ r * H₁ :=
    Nat.le_of_mul_le_mul_left hbig (Nat.pow_pos hC)
  calc
    P * H ≤ (4 * primeWindow n) ^ r * H := Nat.mul_le_mul_right _ hP
    _ = 4 ^ r * (primeWindow n ^ r * H) := by rw [mul_pow]; ring
    _ ≤ 4 ^ r * (A ^ r * H₁) := Nat.mul_le_mul_left _ hsmall
    _ = scoreLoss k n * H₁ := by
      rw [← mul_assoc, ← mul_pow]
      have heq : 4 * A = 16 * (k + 2) * (inputBits n + 1) := by dsimp [A]; ring
      rw [heq]
      rfl

theorem windowExponent_tendsto_atTop : Tendsto windowExponent atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [natSqrt_tendsto_atTop.eventually (eventually_ge_atTop b)] with m hm
  change b ≤ Nat.sqrt m + 1
  omega

theorem bits_add_one_le_windowExponent_sq (m : ℕ) : m + 1 ≤ windowExponent m ^ 2 := by
  have h := Nat.lt_succ_sqrt' m
  simpa [windowExponent, Nat.succ_eq_add_one] using h

theorem log_bits_over_windowExponent_tendsto_zero :
    Tendsto (fun m : ℕ => Real.log (m + 1 : ℝ) / windowExponent m) atTop (𝓝 0) := by
  have ht := (tendsto_natCast_atTop_atTop (R := ℝ)).comp windowExponent_tendsto_atTop
  have hu := (Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp ht).const_mul 2
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun m =>
      div_nonneg (Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) m; linarith))
        (Nat.cast_nonneg _))
  · filter_upwards [] with m
    have hs : (m + 1 : ℝ) ≤ (windowExponent m : ℝ) ^ 2 := by
      exact_mod_cast bits_add_one_le_windowExponent_sq m
    have hlog := Real.log_le_log (by positivity : (0 : ℝ) < m + 1) hs
    rw [Real.log_pow] at hlog
    have hd := div_le_div_of_nonneg_right hlog (Nat.cast_nonneg (α := ℝ) (windowExponent m))
    simpa only [Function.comp_def, id_eq, Nat.cast_ofNat, mul_div_assoc] using hd

theorem log_bits_over_primeBase_tendsto_zero :
    Tendsto (fun n : ℕ => Real.log (inputBits n + 1 : ℝ) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by
  have hu := (log_bits_over_windowExponent_tendsto_zero.comp inputBits_tendsto_atTop).div_const
    (Real.log 2)
  simp only [zero_div] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [] with n
    have hy := primeWindow_ge_two n
    have hb : 0 ≤ Real.log (4 * primeWindow n : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ 4 * primeWindow n))
    have hn : 0 ≤ Real.log (inputBits n + 1 : ℝ) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (inputBits n); linarith)
    exact div_nonneg hn hb
  · filter_upwards [] with n
    have hy := primeWindow_ge_two n
    have hypo : (0 : ℝ) < primeWindow n := by exact_mod_cast (by omega : 0 < primeWindow n)
    have hly : 0 < Real.log (primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
    have hlyb : Real.log (primeWindow n : ℝ) ≤ Real.log (4 * primeWindow n : ℝ) :=
      Real.log_le_log hypo (by linarith)
    have hn : 0 ≤ Real.log (inputBits n + 1 : ℝ) :=
      Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) (inputBits n); linarith)
    have hd := div_le_div_of_nonneg_left hn hly hlyb
    simpa only [Function.comp_def, primeWindow, Nat.cast_pow, Nat.cast_ofNat,
      Real.log_pow, div_div] using hd

theorem scoreBase_log_over_primeBase_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (16 * ((k : ℝ) + 2) * (inputBits n + 1)) /
      Real.log (4 * primeWindow n : ℝ)) atTop (𝓝 0) := by
  have hc := primeBase_log_tendsto_atTop.inv_tendsto_atTop.const_mul
    (Real.log (16 * ((k : ℝ) + 2)))
  have h := hc.add log_bits_over_primeBase_tendsto_zero
  simp only [mul_zero, zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  rw [Real.log_mul (by positivity : (16 * ((k : ℝ) + 2)) ≠ 0)
    (by positivity : (inputBits n + 1 : ℝ) ≠ 0)]
  simp only [Pi.inv_apply, add_div]
  ring

theorem scoreLoss_log_ratio_tendsto_zero (k : ℕ) :
    Tendsto (fun n : ℕ => Real.log (scoreLoss k n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hu := radix_log_ratio_tendsto.mul (scoreBase_log_over_primeBase_tendsto_zero k)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with n hn
    exact div_nonneg (Real.log_natCast_nonneg _) (Real.log_nonneg (by exact_mod_cast hn))
  · filter_upwards [radix_eventually_ge_four, eventually_ge_atTop (2 : ℕ)] with n hR hn
    have hy := primeWindow_ge_two n
    have hb : 0 < Real.log (4 * primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < 4 * primeWindow n))
    have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
    have hs : 0 ≤ Real.log (16 * ((k : ℝ) + 2) * (inputBits n + 1)) := by
      apply Real.log_nonneg
      have hk := Nat.cast_nonneg (α := ℝ) k
      have hm := Nat.cast_nonneg (α := ℝ) (inputBits n)
      nlinarith
    have hd := (le_div_iff₀ hb).mpr (primeDepth_log_bound hR)
    have hmul := mul_le_mul_of_nonneg_right hd hs
    have hdiv := div_le_div_of_nonneg_right hmul hlog.le
    simp only [scoreLoss, Nat.cast_pow, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat,
      Nat.cast_one, Real.log_pow]
    apply le_of_le_of_eq hdiv
    ring

theorem scoreLoss_subpolynomial (k : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (scoreLoss k n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa using eventually_le_rpow_of_log_ratio (scoreLoss_log_ratio_tendsto_zero k) hd

theorem bits_over_candidateCount_tendsto_zero :
    Tendsto (fun n : ℕ => (inputBits n + 1 : ℝ) / candidateCount n) atTop (𝓝 0) := by
  have ht := windowExponent_tendsto_atTop.comp inputBits_tendsto_atTop
  have hu := ((tendsto_pow_const_div_const_pow_of_one_lt 3
    (by norm_num : (1 : ℝ) < 2)).comp ht).const_mul (4 * Real.log 2)
  simp only [mul_zero] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun n => by positivity)
  · filter_upwards [actual_candidate_density] with n hC
    have hy := primeWindow_ge_two n
    have hyl : 0 < Real.log (primeWindow n : ℝ) :=
      Real.log_pos (by exact_mod_cast (by omega : 1 < primeWindow n))
    have hypo : (0 : ℝ) < primeWindow n := by exact_mod_cast (by omega : 0 < primeWindow n)
    have hlower : (0 : ℝ) < (primeWindow n : ℝ) / (4 * Real.log (primeWindow n)) := by positivity
    have hbits : (inputBits n + 1 : ℝ) ≤ (windowExponent (inputBits n) : ℝ) ^ 2 := by
      exact_mod_cast bits_add_one_le_windowExponent_sq (inputBits n)
    have hs : (0 : ℝ) ≤ windowExponent (inputBits n) := Nat.cast_nonneg _
    have hdiv := div_le_div_of_nonneg_left
      (by positivity : (0 : ℝ) ≤ inputBits n + 1) hlower hC
    change (inputBits n + 1 : ℝ) / candidateCount n ≤
      4 * Real.log 2 * ((windowExponent (inputBits n) : ℝ) ^ 3 /
        (2 : ℝ) ^ windowExponent (inputBits n))
    calc
      (inputBits n + 1 : ℝ) / candidateCount n ≤
          (inputBits n + 1 : ℝ) / ((primeWindow n : ℝ) / (4 * Real.log (primeWindow n))) := hdiv
      _ = ((inputBits n + 1 : ℝ) *
          (4 * (windowExponent (inputBits n) : ℝ) * Real.log 2)) /
            (2 : ℝ) ^ windowExponent (inputBits n) := by
        simp only [primeWindow, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
        field_simp
      _ ≤ ((windowExponent (inputBits n) : ℝ) ^ 2 *
          (4 * (windowExponent (inputBits n) : ℝ) * Real.log 2)) /
            (2 : ℝ) ^ windowExponent (inputBits n) := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        exact mul_le_mul_of_nonneg_right hbits (by positivity)
      _ = _ := by ring

theorem candidateCount_eventually_gt_multiple (K : ℕ) :
    ∀ᶠ n : ℕ in atTop, K * (inputBits n + 1) < candidateCount n := by
  have hsmall := bits_over_candidateCount_tendsto_zero.eventually
    (gt_mem_nhds (by positivity : (0 : ℝ) < 1 / ((K : ℝ) + 1)))
  filter_upwards [hsmall, actual_candidates_nonempty] with n hn hC
  have hCpos : (0 : ℝ) < candidateCount n := by
    exact_mod_cast Finset.card_pos.mpr hC
  have hKpos : (0 : ℝ) < (K : ℝ) + 1 := by positivity
  have h := (div_lt_div_iff₀ hCpos hKpos).mp hn
  have hNat : (inputBits n + 1) * (K + 1) < candidateCount n := by
    simpa only [one_mul] using (show (inputBits n + 1 : ℝ) * ((K : ℝ) + 1) <
      candidateCount n by simpa only [one_mul] using h) |> fun ht => by exact_mod_cast ht
  nlinarith

theorem log2_difference_bound (k : ℕ) {n : ℕ} (hn : 0 < n) :
    Nat.log2 (3 * n ^ k) ≤ 2 * (k + 2) * (inputBits n + 1) := by
  have hl : (Nat.log2 (3 * n ^ k) : ℝ) ≤ Real.log (3 * n ^ k : ℝ) / Real.log 2 := by
    simpa [Nat.log2_eq_log_two, Real.logb] using Real.natLog_le_logb (3 * n ^ k) 2
  have hmul := (le_div_iff₀ Parameters.log_two_pos).mp hl
  have hdiff := log_difference_bound k hn
  have hk : (0 : ℝ) ≤ Nat.log2 (3 * n ^ k) := Nat.cast_nonneg _
  have hlog : (1 / 2 : ℝ) ≤ Real.log 2 := by have := Parameters.log_two_lower; linarith
  have hhalf := mul_le_mul_of_nonneg_left hlog hk
  have hR : (Nat.log2 (3 * n ^ k) : ℝ) ≤ 2 * ((k : ℝ) + 2) * (inputBits n + 1) := by
    nlinarith [hhalf]
  exact_mod_cast hR

theorem actual_auxiliary_cardinality (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, Nat.log2 (3 * n ^ k) < candidateCount n := by
  filter_upwards [candidateCount_eventually_gt_multiple (2 * (k + 2)),
    eventually_ge_atTop (1 : ℕ)] with n hC hn
  exact (log2_difference_bound k (by omega)).trans_lt hC

theorem candidateCount_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (candidateCount n : ℝ) ≤ (n : ℝ) ^ d := by
  have hc : Tendsto (fun n : ℕ => Real.log (4 * primeWindow n : ℝ) / Real.log n) atTop (𝓝 0) := by
    have hh := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 4)
    have h := hh.add primeWindow_log_ratio_tendsto_zero
    simp only [mul_zero, zero_add] at h
    apply h.congr'
    filter_upwards [] with n
    have hynz : (primeWindow n : ℝ) ≠ 0 := by
      exact_mod_cast (by have := primeWindow_ge_two n; omega : primeWindow n ≠ 0)
    rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) hynz]
    simp only [Pi.inv_apply, add_div]
    ring
  have hbound : ∀ᶠ n : ℕ in atTop, ((4 * primeWindow n : ℕ) : ℝ) ≤ (n : ℝ) ^ d := by
    have h := eventually_le_rpow_of_log_ratio (a := 0) (f := fun n => 4 * primeWindow n) (by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hc) hd
    simpa only [zero_add] using h
  filter_upwards [hbound] with n hn
  have hcard : candidateCount n ≤ 4 * primeWindow n := by
    unfold candidateCount PrimeDensity.candidates
    calc
      _ ≤ (Nat.primesLE (4 * primeWindow n)).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ 4 * primeWindow n := by
        rw [Nat.primesLE_eq_filter_Ioc_zero]
        exact (Finset.card_filter_le _ _).trans_eq (by simp)
  have hcardR : (candidateCount n : ℝ) ≤ ((4 * primeWindow n : ℕ) : ℝ) := by exact_mod_cast hcard
  exact hcardR.trans hn

end

end ThreeSum.Scales
