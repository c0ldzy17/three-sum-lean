import Submission.ThreeSum.Scales
import Submission.ThreeSum.LocalHashMoments

/-!
# Actual vertex and trimmed-bucket scales

The local prime and bucket cap are the computable finite selections from
`LocalCoverBounds`.  Their logarithmic rates are derived from those exact
definitions and the exact integer schedule in `Scales`.
-/

namespace ThreeSum.TrimScales

open Filter Real ThreeSum.Scales
open scoped Topology

def replicatedHalf (f : ℕ → ℕ) (n : ℕ) : ℕ :=
  f (microHalf (inputBits n)) ^ blockCount (inputBits n)

def typedVertices (n : ℕ) : ℕ :=
  replicatedHalf (fun h => LocalCoverBounds.vertexCount (512 * h) h) n

def trimMultiplicity (n : ℕ) : ℕ :=
  LocalCoverBounds.localBucketCap (microHalf (inputBits n)) ^ (2 * blockCount (inputBits n))

def localLength (h : ℕ) : ℕ := (LocalHashMoments.localSchedule h).length

def scheduleCount (n : ℕ) : ℕ := replicatedHalf localLength n

def representationBound (n : ℕ) : ℕ :=
  (localLength (microHalf (inputBits n)) *
    LocalCoverBounds.localBucketCap (microHalf (inputBits n)) ^ 2) ^ blockCount (inputBits n)

def fullOutputs (n : ℕ) : ℕ := (256 * mu n).choose (mu n)

def representationDomain (n : ℕ) : ℕ := 2 ^ mu n

noncomputable section

def vertexLoad (h : ℕ) : ℝ :=
  (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h

theorem replicatedHalf_log_rate {f : ℕ → ℕ} {a : ℝ}
    (hf : Tendsto (fun h : ℕ => Real.log (f h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => Real.log (replicatedHalf f n : ℝ) / Real.log n) atTop (𝓝 (a / 5)) := by
  have hl := hf.comp (microHalf_tendsto_atTop.comp inputBits_tendsto_atTop)
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hl.mul hs
  have hlim : a * (Real.log 2 * (1 / (5 * Real.log 2))) = a / 5 := by field_simp
  rw [hlim] at h
  apply h.congr'
  filter_upwards [(microHalf_tendsto_atTop.comp inputBits_tendsto_atTop).eventually
      (eventually_ge_atTop 1)] with n hn
  change 1 ≤ microHalf (inputBits n) at hn
  have hn0 : (microHalf (inputBits n) : ℝ) ≠ 0 := by
    exact_mod_cast (by omega : microHalf (inputBits n) ≠ 0)
  simp only [Function.comp_def, replicatedHalf, Nat.cast_pow, Real.log_pow]
  have hmu : (mu n : ℝ) = (blockCount (inputBits n) : ℝ) *
      (2 * microHalf (inputBits n)) := by simp [mu, totalSize, microSize, microHalf]
  rw [hmu]
  field_simp

theorem typedVertices_log_rate :
    Tendsto (fun n : ℕ => Real.log (typedVertices n : ℝ) / Real.log n) atTop
      (𝓝 ((Parameters.E + 1 / 2 + Parameters.kappa / 2) / 5)) := by
  exact replicatedHalf_log_rate BinomialEntropy.vertex_table_rate

theorem vertexLoad_pos (h : ℕ) : 0 < vertexLoad h := by
  have hV : (0 : ℝ) < LocalCoverBounds.vertexCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 512 * h))
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  exact div_pos hV hp

theorem vertexLoad_log_rate :
    Tendsto (fun h : ℕ => Real.log (vertexLoad h) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 (Parameters.kappa / 2)) := by
  have h := BinomialEntropy.vertex_table_rate.sub localPrime_log_rate
  have heq : (Parameters.E + 1 / 2 + Parameters.kappa / 2) - (Parameters.E + 1 / 2) =
      Parameters.kappa / 2 := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [] with h
  have hV : (0 : ℝ) < LocalCoverBounds.vertexCount (512 * h) h := by
    exact_mod_cast (Nat.choose_pos (by omega : h ≤ 512 * h))
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  rw [vertexLoad, Real.log_div hV.ne' hp.ne', sub_div]
  rfl

theorem vertexLoad_eventually_ge_one : ∀ᶠ h : ℕ in atTop, 1 ≤ vertexLoad h := by
  have hpos : 0 < Parameters.kappa / 2 := by have := Parameters.kappa_positive; linarith
  have hr := vertexLoad_log_rate.eventually (lt_mem_nhds hpos)
  filter_upwards [hr, eventually_ge_atTop (1 : ℕ)] with h hh hhpos
  have hhp : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
  have hden : 0 < (2 * h : ℝ) * Real.log 2 := by positivity
  have hlog : 0 < Real.log (vertexLoad h) := (div_pos_iff.mp hh).elim
    (fun hp => hp.1) (fun hp => False.elim (not_lt_of_ge hden.le hp.2))
  exact (Real.log_pos_iff (vertexLoad_pos h).le).mp hlog |>.le

theorem localBucketCap_ge_load (h : ℕ) :
    vertexLoad h ≤ (LocalCoverBounds.localBucketCap h : ℝ) := by
  have hp : (0 : ℝ) < LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localPrime_pos h
  have hV : (0 : ℝ) ≤ LocalCoverBounds.vertexCount (512 * h) h := Nat.cast_nonneg _
  have ht : 4 * (LocalCoverBounds.localPrime h +
      (LocalCoverBounds.vertexCount (512 * h) h : ℝ)) ≤
      (LocalCoverBounds.localBucketCap h : ℝ) * LocalCoverBounds.localPrime h := by
    exact_mod_cast LocalCoverBounds.localBucketCap_threshold h
  rw [vertexLoad, div_le_iff₀ hp]
  nlinarith

theorem localBucketCap_pos (h : ℕ) : 0 < LocalCoverBounds.localBucketCap h := by
  have h := (vertexLoad_pos h).trans_le (localBucketCap_ge_load h)
  exact_mod_cast h

theorem localBucketCap_eventually_le_nine_load :
    ∀ᶠ h : ℕ in atTop, (LocalCoverBounds.localBucketCap h : ℝ) ≤ 9 * vertexLoad h := by
  filter_upwards [vertexLoad_eventually_ge_one] with h hh
  have hu := LocalCoverBounds.bucketCap_real_bound (V := LocalCoverBounds.vertexCount (512 * h) h)
    (LocalCoverBounds.localPrime_pos h)
  change (LocalCoverBounds.localBucketCap h : ℝ) <
    5 + 4 * (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h at hu
  change (LocalCoverBounds.localBucketCap h : ℝ) ≤
    9 * ((LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h)
  change 1 ≤ (LocalCoverBounds.vertexCount (512 * h) h : ℝ) / LocalCoverBounds.localPrime h at hh
  rw [mul_div_assoc] at hu
  linarith

theorem localBucketCap_log_rate :
    Tendsto (fun h : ℕ => Real.log (LocalCoverBounds.localBucketCap h : ℝ) /
      ((2 * h : ℝ) * Real.log 2)) atTop (𝓝 (Parameters.kappa / 2)) := by
  have herr : Tendsto (fun h : ℕ => Real.log 9 / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
    have hi := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      hi.const_mul (Real.log 9 / (2 * Real.log 2))
  have hu := vertexLoad_log_rate.add herr
  simp only [add_zero] at hu
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' vertexLoad_log_rate hu
  · filter_upwards [] with h
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (vertexLoad_pos h) (localBucketCap_ge_load h)) (by positivity)
  · filter_upwards [localBucketCap_eventually_le_nine_load] with h hh
    have hc : (0 : ℝ) < LocalCoverBounds.localBucketCap h := by exact_mod_cast localBucketCap_pos h
    have hlog := Real.log_le_log hc hh
    rw [Real.log_mul (by norm_num : (9 : ℝ) ≠ 0) (vertexLoad_pos h).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    simpa only [add_div, add_comm] using hd

theorem trimMultiplicity_log_rate :
    Tendsto (fun n : ℕ => Real.log (trimMultiplicity n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.kappa / 5)) := by
  have h := (replicatedHalf_log_rate localBucketCap_log_rate).const_mul 2
  have heq : 2 * (Parameters.kappa / 2 / 5) = Parameters.kappa / 5 := by ring
  rw [heq] at h
  convert h using 1
  funext n
  simp only [trimMultiplicity, replicatedHalf, Nat.cast_pow, Real.log_pow, Nat.cast_mul, Nat.cast_ofNat]
  ring

theorem trimMultiplicity_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (trimMultiplicity n : ℝ) ≤ (n : ℝ) ^ (Parameters.kappa / 5 + d) :=
  eventually_le_rpow_of_log_ratio trimMultiplicity_log_rate hd

theorem localPrime_sq_le_power (h : ℕ) :
    LocalCoverBounds.localPrime h ^ 2 ≤ 2 ^ (4 + 514 * h) := by
  have hM : LocalCoverBounds.outputCount (512 * h) h ≤ 2 ^ (512 * h) :=
    Nat.choose_le_two_pow _ _
  calc
    LocalCoverBounds.localPrime h ^ 2 ≤
        16 * (LocalCoverBounds.outputCount (512 * h) h * 2 ^ (2 * h)) :=
      LocalCoverBounds.localPrime_sq_upper h
    _ ≤ 16 * (2 ^ (512 * h) * 2 ^ (2 * h)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hM)
    _ = 2 ^ (4 + 514 * h) := by
      rw [← pow_add, show 512 * h + 2 * h = 514 * h by omega, pow_add]
      norm_num

theorem localPrime_log2_sq_le (h : ℕ) :
    Nat.log2 (LocalCoverBounds.localPrime h ^ 2) ≤ 4 + 514 * h := by
  rw [Nat.log2_eq_log_two]
  have hm := Nat.log_mono_right (b := 2) (localPrime_sq_le_power h)
  simpa only [Nat.log_pow (by decide : 1 < 2)] using hm

theorem localLength_pos (h : ℕ) : 0 < localLength h := by
  simp only [localLength, LocalHashMoments.localSchedule_length]
  positivity

theorem localLength_quadratic_bound (h : ℕ) :
    localLength h ≤ 2 ^ 19 * (h + 1) ^ 2 := by
  have hlog := localPrime_log2_sq_le h
  have hb : localLength h ≤ 320 * (2 * h + 1) * (514 * h + 5) := by
    rw [localLength, LocalHashMoments.localSchedule_length]
    exact Nat.mul_le_mul_left _ (by omega)
  norm_num
  nlinarith [hb]

theorem localLength_log_rate :
    Tendsto (fun h : ℕ => Real.log (localLength h : ℝ) / ((2 * h : ℝ) * Real.log 2))
      atTop (𝓝 0) := by
  have hlog := BinomialEntropy.logarithmic_error_tendsto_zero (c := 1) (by norm_num)
  have hinv := (tendsto_natCast_atTop_atTop (R := ℝ)).inv_tendsto_atTop
  have hu := (hinv.const_mul (19 / 2 : ℝ)).add (hlog.div_const (Real.log 2))
  simp only [mul_zero, zero_div, zero_add] at hu
  apply squeeze_zero' _ _ hu
  · exact Filter.Eventually.of_forall (fun h =>
      div_nonneg (Real.log_natCast_nonneg _) (by positivity))
  · filter_upwards [eventually_ge_atTop (1 : ℕ)] with h hh
    have hhpos : (0 : ℝ) < h := by exact_mod_cast (by omega : 0 < h)
    have hlen : (0 : ℝ) < localLength h := by exact_mod_cast localLength_pos h
    have hb : (localLength h : ℝ) ≤ (2 : ℝ) ^ 19 * (h + 1) ^ 2 := by
      exact_mod_cast localLength_quadratic_bound h
    have hlogb := Real.log_le_log hlen hb
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlogb
    have hd := div_le_div_of_nonneg_right hlogb (by positivity :
      (0 : ℝ) ≤ (2 * h : ℝ) * Real.log 2)
    apply le_of_le_of_eq hd
    simp only [one_mul, Pi.inv_apply, Nat.cast_ofNat]
    field_simp
    ring

theorem scheduleCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (scheduleCount n : ℝ) / Real.log n) atTop (𝓝 0) := by
  simpa [scheduleCount] using replicatedHalf_log_rate localLength_log_rate

theorem representationBound_eq (n : ℕ) :
    representationBound n = scheduleCount n * trimMultiplicity n := by
  simp only [representationBound, scheduleCount, replicatedHalf, trimMultiplicity, mul_pow, pow_mul]

theorem representationBound_log_rate :
    Tendsto (fun n : ℕ => Real.log (representationBound n : ℝ) / Real.log n) atTop
      (𝓝 (Parameters.kappa / 5)) := by
  have h := scheduleCount_log_rate.add trimMultiplicity_log_rate
  simp only [zero_add] at h
  apply h.congr'
  filter_upwards [] with n
  have hs : (0 : ℝ) < scheduleCount n := by
    exact_mod_cast (Nat.pow_pos (localLength_pos (microHalf (inputBits n))) :
      0 < scheduleCount n)
  have ht : (0 : ℝ) < trimMultiplicity n := by
    exact_mod_cast (Nat.pow_pos (localBucketCap_pos (microHalf (inputBits n))) :
      0 < trimMultiplicity n)
  rw [representationBound_eq, Nat.cast_mul, Real.log_mul hs.ne' ht.ne', add_div]

theorem representationBound_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (representationBound n : ℝ) ≤ (n : ℝ) ^ (Parameters.kappa / 5 + d) :=
  eventually_le_rpow_of_log_ratio representationBound_log_rate hd

theorem mu_cast_tendsto_atTop : Tendsto (fun n : ℕ => (mu n : ℝ)) atTop atTop := by
  have hpos : (0 : ℝ) < 1 / (5 * Real.log 2) := by positivity
  have h := mu_log_ratio_tendsto.pos_mul_atTop hpos Asymptotics.log_nat_tendsto_atTop
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  exact div_mul_cancel₀ _ hlog

theorem mu_tendsto_atTop : Tendsto mu atTop atTop := by
  apply tendsto_atTop.2
  intro b
  filter_upwards [mu_cast_tendsto_atTop.eventually (eventually_ge_atTop (b : ℝ))] with n hn
  exact_mod_cast hn

theorem fullOutputs_log_rate :
    Tendsto (fun n : ℕ => Real.log (fullOutputs n : ℝ) / Real.log n) atTop
      (𝓝 (2 * Parameters.E / 5)) := by
  have hm := BinomialEntropy.output_table_rate.comp mu_tendsto_atTop
  have hs := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have h := hm.mul hs
  have heq : 2 * Parameters.E * (Real.log 2 * (1 / (5 * Real.log 2))) =
      2 * Parameters.E / 5 := by field_simp
  rw [heq] at h
  apply h.congr'
  filter_upwards [mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hn0 : (mu n : ℝ) ≠ 0 := by exact_mod_cast (by omega : mu n ≠ 0)
  simp only [Function.comp_def, fullOutputs]
  field_simp

theorem fullOutputs_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (fullOutputs n : ℝ) ≤ (n : ℝ) ^ (2 * Parameters.E / 5 + d) :=
  eventually_le_rpow_of_log_ratio fullOutputs_log_rate hd

theorem representationDomain_log_rate :
    Tendsto (fun n : ℕ => Real.log (representationDomain n : ℝ) / Real.log n) atTop
      (𝓝 (1 / 5)) := by
  have h := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have heq : Real.log 2 * (1 / (5 * Real.log 2)) = (1 / 5 : ℝ) := by field_simp
  rw [heq] at h
  convert h using 1
  funext n
  simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  ring

theorem representationBound_log_domain_rate :
    Tendsto (fun n : ℕ => Real.log (representationBound n : ℝ) /
      Real.log (representationDomain n : ℝ)) atTop (𝓝 Parameters.kappa) := by
  have h := representationBound_log_rate.div representationDomain_log_rate
    (by norm_num : (1 / 5 : ℝ) ≠ 0)
  have heq : Parameters.kappa / 5 / (1 / 5) = Parameters.kappa := by ring
  rw [heq] at h
  apply h.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ),
    mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  have hmupos : (0 : ℝ) < mu n := by exact_mod_cast (by omega : 0 < mu n)
  have hD : Real.log (representationDomain n : ℝ) ≠ 0 := by
    simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    positivity
  simp only [Pi.div_apply]
  field_simp

theorem representationBound_eventually_le_domain {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (representationBound n : ℝ) ≤
      (representationDomain n : ℝ) ^ (Parameters.kappa + d) := by
  have hs := representationBound_log_domain_rate.eventually
    (gt_mem_nhds (by linarith : Parameters.kappa < Parameters.kappa + d))
  filter_upwards [hs, mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hmupos : (0 : ℝ) < mu n := by exact_mod_cast (by omega : 0 < mu n)
  have hDpos : (0 : ℝ) < representationDomain n := by
    simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat]
    positivity
  have hDlog : 0 < Real.log (representationDomain n : ℝ) := by
    simp only [representationDomain, Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
    positivity
  exact Real.le_rpow_of_log_le hDpos ((div_lt_iff₀ hDlog).mp hn).le

end

end ThreeSum.TrimScales
