import Submission.ThreeSum.TernaryParameters
import Submission.ThreeSum.TernaryCoverScale
import Submission.ThreeSum.TernaryTypeCardinality

/-! Exact entropy rates for two-binomial three-symbol type counts. -/
noncomputable section
namespace ThreeSum.TernaryEntropyRates
open Filter Real
open scoped Topology
open TernaryJointType TernaryCoverLocal TernaryLocalParameters TernaryCoverScale

set_option maxRecDepth 10000

theorem entropy_split {a b c : ℝ} (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (hs : a+b+c=1) :
    Real.binEntropy c+(1-c)*Real.binEntropy (b/(1-c)) =
      -a*Real.log a-b*Real.log b-c*Real.log c := by
  have hac : 0 < 1-c := by linarith
  have hcomp : 1-b/(1-c)=a/(1-c) := by field_simp; linarith
  unfold Real.binEntropy
  simp only [Real.log_inv]
  rw [hcomp, Real.log_div hb.ne' hac.ne', Real.log_div ha.ne' hac.ne']
  field_simp
  linear_combination hs * Real.log (1-c)

def typeCount (N r1 r2 m : ℕ) : ℕ :=
  (N*m).choose (r2*m)*((N-r2)*m).choose (r1*m)

theorem typeCount_pos {N r1 r2 : ℕ} (h1 : r1+r2 ≤ N) (m : ℕ) :
    0 < typeCount N r1 r2 m := by
  unfold typeCount
  exact Nat.mul_pos (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))
    (Nat.choose_pos (Nat.mul_le_mul_right m (by omega)))

def splitBits (N r1 r2 : ℕ) : ℝ :=
  ((N : ℝ)*ThreeSum.Parameters.entropy ((r2 : ℝ)/N)+
    ((N-r2 : ℕ) : ℝ)*ThreeSum.Parameters.entropy ((r1 : ℝ)/(N-r2 : ℕ)))/N

theorem typeCount_bits_tendsto {N r1 r2 : ℕ} (hN : 0 < N)
    (h2 : r2 < N) (h1 : r1+r2 ≤ N) :
    Tendsto (fun m : ℕ => Real.log (typeCount N r1 r2 m : ℝ)/
      (((N*m : ℕ) : ℝ)*Real.log 2)) atTop (𝓝 (splitBits N r1 r2)) := by
  have hfirst := BinomialEntropy.fixed_ratio_bits_tendsto hN h2.le
  have hrest := BinomialEntropy.fixed_ratio_bits_tendsto (Nat.sub_pos_of_lt h2)
    (show r1 ≤ N-r2 by omega)
  have h := (hfirst.add hrest).div_const (N : ℝ)
  convert h using 1
  · funext m
    unfold typeCount
    rw [Nat.cast_mul, Real.log_mul]
    · push_cast
      ring
    · exact_mod_cast (Nat.choose_pos (Nat.mul_le_mul_right m h2.le)).ne'
    · exact_mod_cast (Nat.choose_pos (Nat.mul_le_mul_right m (show r1 ≤ N-r2 by omega))).ne'
  · rfl

theorem output_splitBits : splitBits 100000000 15860350 2934747 = TernaryParameters.Hpi := by
  have h := entropy_split TernaryParameters.pi_positive.1 TernaryParameters.pi_positive.2.1
    TernaryParameters.pi_positive.2.2 TernaryParameters.pi_total
  unfold splitBits ThreeSum.Parameters.entropy TernaryParameters.Hpi
  norm_num [TernaryParameters.pi0,TernaryParameters.pi1,TernaryParameters.pi2] at h ⊢
  linear_combination h / Real.log 2

theorem endpoint_splitBits : splitBits 100000000 8908424 978249 = TernaryParameters.Halpha := by
  have h := entropy_split TernaryParameters.alpha_positive.1 TernaryParameters.alpha_positive.2.1
    TernaryParameters.alpha_positive.2.2 TernaryParameters.alpha_total
  unfold splitBits ThreeSum.Parameters.entropy TernaryParameters.Halpha
  norm_num [TernaryParameters.alpha0,TernaryParameters.alpha1,TernaryParameters.alpha2] at h ⊢
  linear_combination h / Real.log 2

theorem output_formula_rate :
    Tendsto (fun m : ℕ => Real.log (typeCount 100000000 15860350 2934747 m : ℝ)/
      (((100000000*m : ℕ) : ℝ)*Real.log 2)) atTop (𝓝 TernaryParameters.Hpi) := by
  simpa only [output_splitBits] using
    (typeCount_bits_tendsto (N := 100000000) (r1 := 15860350) (r2 := 2934747)
      (by decide) (by decide) (by decide))

theorem endpoint_formula_rate :
    Tendsto (fun m : ℕ => Real.log (typeCount 100000000 8908424 978249 m : ℝ)/
      (((100000000*m : ℕ) : ℝ)*Real.log 2)) atTop (𝓝 TernaryParameters.Halpha) := by
  simpa only [endpoint_splitBits] using
    (typeCount_bits_tendsto (N := 100000000) (r1 := 8908424) (r2 := 978249)
      (by decide) (by decide) (by decide))

theorem fixedAlpha_total (m : ℕ) : fixedAlpha m 0+fixedAlpha m 1+fixedAlpha m 2=fixedLength m := by
  simp [fixedAlpha,fixedLength]
  omega

theorem actual_output_count (m : ℕ) :
    outputSize m=typeCount 100000000 15860350 2934747 m := by
  unfold outputSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedPi m) (fixedPi_total m)]
  change (100000000*m).choose (2934747*m)*(100000000*m-2934747*m).choose (15860350*m)=
    (100000000*m).choose (2934747*m)*((100000000-2934747)*m).choose (15860350*m)
  rw [← Nat.sub_mul]

def endpointSize (m : ℕ) : ℕ := (vertices (fixedLength m) (fixedAlpha m)).card
theorem actual_endpoint_count (m : ℕ) :
    endpointSize m=typeCount 100000000 8908424 978249 m := by
  unfold endpointSize
  rw [TernaryTypeCardinality.vertices_card_eq_choose (fixedAlpha m) (fixedAlpha_total m)]
  change (100000000*m).choose (978249*m)*(100000000*m-978249*m).choose (8908424*m)=
    (100000000*m).choose (978249*m)*((100000000-978249)*m).choose (8908424*m)
  rw [← Nat.sub_mul]

def outputRate (m : ℕ) : ℝ := Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def endpointRate (m : ℕ) : ℝ := Real.log (endpointSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def primeRate (m : ℕ) : ℝ := Real.log (prime m : ℝ)/((fixedLength m : ℝ)*Real.log 2)
def partitionCap (m : ℕ) : ℕ := 2^(fixedPi m 1)*3^(fixedPi m 2)

theorem actual_output_rate : Tendsto outputRate atTop (𝓝 TernaryParameters.Hpi) := by
  change Tendsto (fun m => Real.log (outputSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2)) _ _
  simpa only [actual_output_count,fixedLength] using output_formula_rate
theorem actual_endpoint_rate : Tendsto endpointRate atTop (𝓝 TernaryParameters.Halpha) := by
  change Tendsto (fun m => Real.log (endpointSize m : ℝ)/((fixedLength m : ℝ)*Real.log 2)) _ _
  simpa only [actual_endpoint_count,fixedLength] using endpoint_formula_rate

theorem partition_log (m : ℕ) : Real.log (partitionCap m : ℝ)=
    (fixedLength m : ℝ)*Real.log 2*TernaryParameters.partitionEntropy := by
  unfold partitionCap
  rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_pow,Real.log_mul (by positivity) (by positivity),
    Real.log_pow,Real.log_pow]
  unfold TernaryParameters.partitionEntropy TernaryParameters.pi1 TernaryParameters.pi2
    TernaryParameters.three fixedPi fixedLength
  norm_num
  push_cast
  field_simp
  ring

theorem denominator_pos {m : ℕ} (hm : 0 < m) :
    0 < (fixedLength m : ℝ)*Real.log 2 := by
  have hL : 0 < fixedLength m := by unfold fixedLength; positivity
  exact mul_pos (by exact_mod_cast hL) TernaryParameters.log_two_pos

theorem prime_rate_bounds {m : ℕ} (hm : 0 < m) :
    (outputRate m+TernaryParameters.partitionEntropy)/2 ≤ primeRate m ∧
    primeRate m ≤ (outputRate m+TernaryParameters.partitionEntropy)/2+
      Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by
  have hM : 0 < (outputSize m : ℝ) := by exact_mod_cast lt_of_lt_of_le (by decide : 0 < (16 : ℕ)) (outputSize_ge_sixteen hm)
  have hR : 0 < (partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hp : 0 < (prime m : ℝ) := by exact_mod_cast (prime_prime m).pos
  have hlo : (outputSize m : ℝ)*(partitionCap m : ℝ) ≤ (prime m : ℝ)^2 := by
    exact_mod_cast prime_lower m
  have hup : (prime m : ℝ)^2 ≤ 16*((outputSize m : ℝ)*(partitionCap m : ℝ)) := by
    exact_mod_cast prime_upper m
  have hl := Real.log_le_log (mul_pos hM hR) hlo
  have hu := Real.log_le_log (pow_pos hp 2) hup
  rw [Real.log_mul hM.ne' hR.ne',Real.log_pow,partition_log] at hl
  rw [Real.log_mul (by norm_num : (16 : ℝ) ≠ 0) (mul_pos hM hR).ne',
    Real.log_mul hM.ne' hR.ne',Real.log_pow,partition_log] at hu
  norm_num at hl hu
  have hd := denominator_pos hm
  have hL : (fixedLength m : ℝ) ≠ 0 := by
    have hLp : 0 < fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hLp.ne'
  unfold outputRate primeRate
  constructor
  · apply (le_div_iff₀ hd).mpr
    field_simp [hL,TernaryParameters.log_two_pos.ne']
    nlinarith
  · apply (div_le_iff₀ hd).mpr
    field_simp [hL,TernaryParameters.log_two_pos.ne']
    nlinarith

theorem prime_rate_error_tendsto :
    Tendsto (fun m : ℕ => Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)))
      atTop (𝓝 0) := by
  have hn := tendsto_natCast_atTop_atTop (R := ℝ)
  have hinv := hn.inv_tendsto_atTop
  have h := hinv.const_mul (Real.log 16/(200000000*Real.log 2))
  convert h using 1
  · funext m
    unfold fixedLength
    push_cast
    simp only [Pi.inv_apply]
    ring
  · simp

theorem actual_prime_rate :
    Tendsto primeRate atTop (𝓝 ((TernaryParameters.Hpi+TernaryParameters.partitionEntropy)/2)) := by
  have hl := (actual_output_rate.add_const TernaryParameters.partitionEntropy).div_const 2
  have hu := hl.add prime_rate_error_tendsto
  have hb : ∀ᶠ m : ℕ in atTop,
      (outputRate m+TernaryParameters.partitionEntropy)/2 ≤ primeRate m ∧
      primeRate m ≤ (outputRate m+TernaryParameters.partitionEntropy)/2+
        Real.log 16/(2*((fixedLength m : ℝ)*Real.log 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact prime_rate_bounds hm
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hl (by simpa using hu)
    (hb.mono fun _ h => h.1) (hb.mono fun _ h => h.2)

end ThreeSum.TernaryEntropyRates
