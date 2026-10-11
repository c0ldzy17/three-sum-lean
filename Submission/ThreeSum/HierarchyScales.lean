import Submission.ThreeSum.CostLedger

/-!
# Finite sums and asymptotic bounds for the actual hierarchy

The finite box and query counts are summed over the executable depth range.
The only envelopes introduced here are explicit elementary functions of the
already constructed integer `mu`; all growth rates are proved from Scales.
-/

namespace ThreeSum.HierarchyScales

open Filter Set Real ThreeSum.Parameters ThreeSum.Scales ThreeSum.Switch ThreeSum.CostLedger
open scoped Topology BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def initialCap (r : ℕ) : ℕ := r ⌈/⌉ 25

def polynomialFactor (C n : ℕ) : ℕ := (mu n + 1) ^ C

theorem initialCap_bounds (r : ℕ) : r ≤ 25 * initialCap r ∧ 25 * initialCap r < r + 25 := by
  constructor
  · exact (ceilDiv_le_iff_le_mul (a := 25) (b := r)
      (c := initialCap r) (by norm_num)).mp le_rfl
  · have h := Nat.div_mul_le_self (r + 25 - 1) 25
    simp only [initialCap, Nat.ceilDiv_eq_add_pred_div]
    omega

theorem initialCap_accepted (J r : ℕ) : accepts J 0 r (initialCap r) := by
  have hh := Nat.mul_le_mul_right (r ^ 2) (initialCap_bounds r).1
  have hm := Nat.mul_le_mul_left (291 * J) hh
  unfold accepts cubicNumerator
  simp only [Nat.mul_zero, Nat.add_zero, Nat.sub_zero]
  ring_nf at hm ⊢
  omega

theorem initialIndex_le_cap (J : ℕ) {r : ℕ} (hr : 50 ≤ r) :
    switchIndex J 0 r ≤ initialCap r := by
  apply switchIndex_le
  apply mem_candidates.mpr
  refine ⟨?_, initialCap_accepted J r⟩
  have h := (initialCap_bounds r).2
  omega

theorem residual_zero (n : ℕ) : residualSize n 0 = mu n := by
  simp only [residualSize, Nat.sub_zero, actual_totalSize]

theorem terminalDepth_le_mu {n : ℕ} (hmu : 0 < mu n) : terminalDepth n ≤ mu n := by
  have hprod := hmu
  rw [actual_totalSize] at hprod
  have hm := Nat.pos_of_mul_pos_left hprod
  have hc := Nat.mul_le_mul_left (blockCount (inputBits n)) (show 1 ≤ muZero n by omega)
  have hd := actual_depth_condition (n := n) (j := terminalDepth n) le_rfl
  rw [Nat.mul_one, ← actual_totalSize] at hc
  omega

noncomputable section

def hierarchyEnvelope (C B : ℝ) (n : ℕ) : ℝ :=
  (mu n + 1 : ℝ) * Real.exp ((mu n : ℝ) * Real.log 2 * C + B)

theorem allPrefixBoxes_envelope {n : ℕ} (hmu : 0 < mu n) :
    (allPrefixBoxes n : ℝ) ≤ hierarchyEnvelope (2 * E + 2 * bandShift - boxSaving) 0 n := by
  unfold allPrefixBoxes
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (terminalDepth n + 1),
        Real.exp ((mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving)) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (prefixBoxes_log_bound hmu (by simpa using hj))
    _ = (terminalDepth n + 1 : ℝ) *
        Real.exp ((mu n : ℝ) * Real.log 2 * (2 * E + 2 * bandShift - boxSaving)) := by simp
    _ ≤ hierarchyEnvelope (2 * E + 2 * bandShift - boxSaving) 0 n := by
      simp only [hierarchyEnvelope, add_zero]
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (terminalDepth_le_mu hmu) 1

theorem allQueryTerms_envelope {n : ℕ} (hmu : 0 < mu n) :
    (allQueryTerms n : ℝ) ≤
      hierarchyEnvelope (entropyRatio * (1 + boxSaving - 2 * bandShift))
        (9 * entropyRatio * Real.log 2) n := by
  unfold allQueryTerms
  rw [Nat.cast_sum]
  calc
    _ ≤ ∑ j ∈ Finset.range (terminalDepth n + 1),
        Real.exp ((mu n : ℝ) * Real.log 2 *
          (entropyRatio * (1 + boxSaving - 2 * bandShift)) + 9 * entropyRatio * Real.log 2) := by
      apply Finset.sum_le_sum
      intro j hj
      exact Real.le_exp_of_log_le (queryTerms_log_bound hmu (by simpa using hj))
    _ = (terminalDepth n + 1 : ℝ) *
        Real.exp ((mu n : ℝ) * Real.log 2 *
          (entropyRatio * (1 + boxSaving - 2 * bandShift)) + 9 * entropyRatio * Real.log 2) := by simp
    _ ≤ hierarchyEnvelope (entropyRatio * (1 + boxSaving - 2 * bandShift))
        (9 * entropyRatio * Real.log 2) n := by
      apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
      exact_mod_cast Nat.add_le_add_right (terminalDepth_le_mu hmu) 1

theorem log_mu_add_one_rate :
    Tendsto (fun n : ℕ => Real.log (mu n + 1 : ℝ) / Real.log n) atTop (𝓝 0) := by
  have he := (BinomialEntropy.logarithmic_error_tendsto_zero
    (c := 1) (by norm_num)).comp TrimScales.mu_tendsto_atTop
  have hh := he.mul mu_log_ratio_tendsto
  simp only [zero_mul] at hh
  apply hh.congr'
  filter_upwards [TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn
  have hmu : (mu n : ℝ) ≠ 0 := by exact_mod_cast (by omega : mu n ≠ 0)
  simp only [Function.comp_def, Nat.cast_one, one_mul]
  field_simp

theorem hierarchyEnvelope_log_rate (C B : ℝ) :
    Tendsto (fun n : ℕ => Real.log (hierarchyEnvelope C B n) / Real.log n) atTop (𝓝 (C / 5)) := by
  have hm := mu_log_ratio_tendsto.const_mul (Real.log 2 * C)
  have hid : Real.log 2 * C * (1 / (5 * Real.log 2)) = C / 5 := by field_simp
  rw [hid] at hm
  have hc := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul B
  have hh := log_mu_add_one_rate.add (hm.add hc)
  simp only [mul_zero, add_zero, zero_add] at hh
  convert hh using 1
  funext n
  have hp : (mu n + 1 : ℝ) ≠ 0 := by positivity
  simp only [hierarchyEnvelope, Real.log_mul hp (Real.exp_ne_zero _), Real.log_exp,
    Pi.inv_apply, add_div]
  ring

theorem eventually_real_le_rpow_of_log_rate {f : ℕ → ℝ} {a d : ℝ}
    (hf : Tendsto (fun n : ℕ => Real.log (f n) / Real.log n) atTop (𝓝 a)) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, f n ≤ (n : ℝ) ^ (a + d) := by
  have hs := hf.eventually (gt_mem_nhds (by linarith : a < a + d))
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    ((div_lt_iff₀ hlog).mp hn).le

theorem allPrefixBoxes_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (allPrefixBoxes n : ℝ) ≤
      (n : ℝ) ^ ((2 * E + 2 * bandShift - boxSaving) / 5 + d) := by
  have he := eventually_real_le_rpow_of_log_rate
    (hierarchyEnvelope_log_rate (2 * E + 2 * bandShift - boxSaving) 0) hd
  filter_upwards [he, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (allPrefixBoxes_envelope (by omega : 0 < mu n)).trans hn

theorem allQueryTerms_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (allQueryTerms n : ℝ) ≤
      (n : ℝ) ^ ((entropyRatio * (1 + boxSaving - 2 * bandShift)) / 5 + d) := by
  have he := eventually_real_le_rpow_of_log_rate
    (hierarchyEnvelope_log_rate (entropyRatio * (1 + boxSaving - 2 * bandShift))
      (9 * entropyRatio * Real.log 2)) hd
  filter_upwards [he, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  exact (allQueryTerms_envelope (by omega : 0 < mu n)).trans hn

theorem polynomialFactor_log_rate (C : ℕ) :
    Tendsto (fun n : ℕ => Real.log (polynomialFactor C n : ℝ) / Real.log n) atTop (𝓝 0) := by
  have hh := log_mu_add_one_rate.const_mul (C : ℝ)
  simp only [mul_zero] at hh
  simpa only [polynomialFactor, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Real.log_pow,
    mul_div_assoc] using hh

theorem polynomialFactor_subpolynomial (C : ℕ) {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (polynomialFactor C n : ℝ) ≤ (n : ℝ) ^ d := by
  simpa only [zero_add] using eventually_le_rpow_of_log_ratio (polynomialFactor_log_rate C) hd

theorem microPartitions_subpolynomial {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (microPartitions n : ℝ) ≤ (n : ℝ) ^ d := by
  filter_upwards [localSearch_subpolynomial 1 hd,
    muZero_tendsto_atTop.eventually (eventually_ge_atTop 1)] with n hn hmu
  have hpow : muZero n ≤ muZero n ^ 2 := by nlinarith
  have hc : microPartitions n ≤ localSearch 1 n := by
    exact (Nat.choose_le_two_pow _ _).trans (by simpa [localSearch] using Nat.pow_le_pow_right (by norm_num : 0 < 2) hpow)
  exact (show (microPartitions n : ℝ) ≤ localSearch 1 n by exact_mod_cast hc).trans hn

theorem initial_ratio_le {n : ℕ} (hmu : 50 ≤ mu n) :
    (actualSwitch n 0 : ℝ) / mu n ≤ initialTheta + 1 / mu n := by
  have hq := initialIndex_le_cap (blockCount (inputBits n)) hmu
  have hc := (initialCap_bounds (mu n)).2
  have hq' : actualSwitch n 0 ≤ initialCap (mu n) := by
    simpa only [actualSwitch, residual_zero] using hq
  have hbound : (25 : ℝ) * actualSwitch n 0 < (mu n : ℝ) + 25 := by exact_mod_cast lt_of_le_of_lt (Nat.mul_le_mul_left 25 hq') hc
  have hmuR : (0 : ℝ) < mu n := by exact_mod_cast (by omega : 0 < mu n)
  rw [div_le_iff₀ hmuR]
  have hid : (initialTheta + 1 / (mu n : ℝ)) * mu n = (mu n : ℝ) / 25 + 1 := by
    unfold initialTheta
    field_simp
  rw [hid]
  linarith

theorem initial_upper_mem {n : ℕ} (hmu : 50 ≤ mu n) :
    initialTheta + 1 / (mu n : ℝ) ∈ Icc (0 : ℝ) (1 / 2) := by
  have hm : (50 : ℝ) ≤ mu n := by exact_mod_cast hmu
  have hp : (0 : ℝ) < mu n := by linarith
  have hu : 1 / (mu n : ℝ) ≤ 1 / 50 := one_div_le_one_div_of_le (by norm_num) hm
  constructor
  · unfold initialTheta; positivity
  · unfold initialTheta; linarith

theorem initial_query_log_bound {n : ℕ} (hmu : 50 ≤ mu n) :
    Real.log (queryTerms n 0 : ℝ) ≤
      (mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ)) := by
  have hm : 0 < mu n := by omega
  have ht := (actual_switch_certified (j := 0) hm (by omega)).1
  rw [residual_zero] at ht
  have hupper := initial_upper_mem hmu
  have hmono := Real.binEntropy_strictMonoOn.monotoneOn
    (by simpa only [one_div] using ht)
    (by simpa only [one_div] using hupper) (initial_ratio_le hmu)
  have hprod := hm
  rw [actual_totalSize] at hprod
  have hq := (switchIndex_spec (Nat.pos_of_mul_pos_right hprod)
    (actual_depth_condition (n := n) (j := 0) (by omega))
    (actual_residual_pos hm (by omega)) (actual_residual_even n 0)).1
  have hb := (BinomialEntropy.log_choose_entropy_bounds
    (hq.trans (Nat.div_le_self _ _))).2
  change Real.log (queryTerms n 0 : ℝ) ≤
    (residualSize n 0 : ℝ) * Real.binEntropy ((actualSwitch n 0 : ℝ) / residualSize n 0) at hb
  rw [residual_zero] at hb
  have hmul := mul_le_mul_of_nonneg_left hmono (Nat.cast_nonneg (α := ℝ) (mu n))
  have hid : (mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ)) =
      (mu n : ℝ) * Real.binEntropy (initialTheta + 1 / (mu n : ℝ)) := by
    unfold entropy
    field_simp
  rw [hid]
  exact hb.trans hmul

theorem initial_entropy_tendsto :
    Tendsto (fun n : ℕ => entropy (initialTheta + 1 / (mu n : ℝ))) atTop
      (𝓝 (entropy initialTheta)) := by
  have hu := TrimScales.mu_cast_tendsto_atTop.inv_tendsto_atTop.const_add initialTheta
  simp only [add_zero] at hu
  have hc : Continuous entropy := Real.binEntropy_continuous.div_const _
  simpa only [Function.comp_def, one_div, Pi.inv_apply] using hc.continuousAt.tendsto.comp hu

theorem initial_query_eventually_le {d : ℝ} (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop, (queryTerms n 0 : ℝ) ≤
      (n : ℝ) ^ (entropy initialTheta / 5 + d) := by
  have hm := mu_log_ratio_tendsto.const_mul (Real.log 2)
  have hid : Real.log 2 * (1 / (5 * Real.log 2)) = (1 / 5 : ℝ) := by field_simp
  rw [hid] at hm
  have hh := hm.mul initial_entropy_tendsto
  have hrate : Tendsto
      (fun n : ℕ => ((mu n : ℝ) * Real.log 2 * entropy (initialTheta + 1 / (mu n : ℝ))) /
        Real.log n) atTop (𝓝 (entropy initialTheta / 5)) := by
    convert hh using 1
    · funext n
      ring
    · ring
  have hs := hrate.eventually (gt_mem_nhds (by linarith : entropy initialTheta / 5 < entropy initialTheta / 5 + d))
  filter_upwards [hs, TrimScales.mu_tendsto_atTop.eventually (eventually_ge_atTop 50),
    eventually_ge_atTop (2 : ℕ)] with n hn hmu hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb := initial_query_log_bound hmu
  exact Real.le_rpow_of_log_le (by exact_mod_cast (by omega : 0 < n))
    (hb.trans ((div_lt_iff₀ hlog).mp hn).le)

def unroundedBandCount (n : ℕ) : ℝ := (n : ℝ) / BandScales.bandSize n

theorem unroundedBandCount_pos {n : ℕ} (hn : 0 < n) : 0 < unroundedBandCount n := by
  exact div_pos (by exact_mod_cast hn) (by exact_mod_cast BandScales.bandSize_pos n)

theorem unroundedBandCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (unroundedBandCount n) / Real.log n) atTop
      (𝓝 (1 - (E + bandShift) / 5)) := by
  have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
  have hh := hone.sub BandScales.bandSize_log_rate
  change Tendsto (fun n : ℕ => (1 : ℝ) - Real.log (BandScales.bandSize n : ℝ) / Real.log n)
    atTop (𝓝 (1 - (E - 1 / 20) / 5)) at hh
  change Tendsto _ _ (𝓝 (1 - (E - 1 / 20) / 5))
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hbR : (BandScales.bandSize n : ℝ) ≠ 0 := by exact_mod_cast (BandScales.bandSize_pos n).ne'
  have hlog : Real.log n ≠ 0 := (Real.log_pos (by exact_mod_cast (by omega : 1 < n))).ne'
  simp only [unroundedBandCount, Real.log_div hnR hbR, sub_div, div_self hlog]

theorem bandCount_ge_unrounded (n : ℕ) : unroundedBandCount n ≤ (bandCount n : ℝ) := by
  have hb : (0 : ℝ) < BandScales.bandSize n := by exact_mod_cast BandScales.bandSize_pos n
  rw [unroundedBandCount, div_le_iff₀ hb]
  have hn : (n : ℝ) ≤ (BandScales.bandSize n : ℝ) * bandCount n :=
    by exact_mod_cast (bandCount_mul_bounds n).1
  simpa only [mul_comm] using hn

theorem unroundedBandCount_eventually_ge_one :
    ∀ᶠ n : ℕ in atTop, 1 ≤ unroundedBandCount n := by
  have ha : (0 : ℝ) < 1 - (E + bandShift) / 5 := by
    have he := E_bounds.2
    dsimp [bandShift]
    linarith
  have hs := unroundedBandCount_log_rate.eventually (lt_mem_nhds ha)
  filter_upwards [hs, eventually_ge_atTop (2 : ℕ)] with n hn hge
  have hlog : 0 < Real.log n := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hb : 0 < Real.log (unroundedBandCount n) := (div_pos_iff.mp hn).elim
    (fun h => h.1) (fun h => False.elim (not_lt_of_ge hlog.le h.2))
  exact ((Real.log_pos_iff (unroundedBandCount_pos (by omega : 0 < n)).le).mp hb).le

theorem bandCount_eventually_le_twice :
    ∀ᶠ n : ℕ in atTop, (bandCount n : ℝ) ≤ 2 * unroundedBandCount n := by
  filter_upwards [unroundedBandCount_eventually_ge_one] with n hn
  have hb : (0 : ℝ) < BandScales.bandSize n := by exact_mod_cast BandScales.bandSize_pos n
  have hu : (BandScales.bandSize n : ℝ) * bandCount n < (n : ℝ) + BandScales.bandSize n :=
    by exact_mod_cast (bandCount_mul_bounds n).2
  have hsmall : (bandCount n : ℝ) < unroundedBandCount n + 1 := by
    rw [unroundedBandCount]
    have hid : (n : ℝ) / BandScales.bandSize n + 1 =
      ((n : ℝ) + BandScales.bandSize n) / BandScales.bandSize n := by field_simp
    rw [hid, lt_div_iff₀ hb]
    simpa only [mul_comm] using hu
  linarith

theorem bandCount_log_rate :
    Tendsto (fun n : ℕ => Real.log (bandCount n : ℝ) / Real.log n) atTop
      (𝓝 (1 - (E + bandShift) / 5)) := by
  have he := Asymptotics.log_nat_tendsto_atTop.inv_tendsto_atTop.const_mul (Real.log 2)
  have hh := unroundedBandCount_log_rate.add he
  simp only [mul_zero, add_zero] at hh
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' unroundedBandCount_log_rate hh
  · filter_upwards [eventually_ge_atTop (2 : ℕ)] with n hn
    exact div_le_div_of_nonneg_right
      (Real.log_le_log (unroundedBandCount_pos (by omega)) (bandCount_ge_unrounded n))
      (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
  · filter_upwards [bandCount_eventually_le_twice, eventually_ge_atTop (2 : ℕ)] with n hn hge
    have hp : (0 : ℝ) < bandCount n :=
      lt_of_lt_of_le (unroundedBandCount_pos (by omega)) (bandCount_ge_unrounded n)
    have hlog := Real.log_le_log hp hn
    rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
      (unroundedBandCount_pos (by omega : 0 < n)).ne'] at hlog
    have hd := div_le_div_of_nonneg_right hlog
      (show 0 ≤ Real.log (n : ℝ) from Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ n)))
    simpa only [add_div, Pi.inv_apply, div_eq_mul_inv, add_mul, add_comm] using hd

end
end ThreeSum.HierarchyScales
