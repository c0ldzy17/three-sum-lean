import Submission.ThreeSum.TernaryPairedFamilyMargin
import Submission.ThreeSum.TernaryPairedRecurrence

noncomputable section
namespace ThreeSum.TernaryPairedCollisionRate
open Filter Real TernaryParameters TernaryEntropyRates TernaryOversizeRates TernaryOversizePrime
open TernaryCoverScale TernaryLocalParameters
open scoped Topology
set_option maxHeartbeats 1000000

def charge (K m : ℕ) : ℝ :=
  2-2*(nativeRate K m-Real.log 9/((fixedLength m : ℝ)*Real.log 2))/outputRate m

theorem charge_tendsto {K : ℕ} (hK : 0<K) :
    Tendsto (charge K) atTop (𝓝 (1-partitionEntropy/Hpi-2/(K : ℝ))) := by
  have hc := denominator_atTop.const_div_atTop (Real.log 9)
  have h := (((native_rate_tendsto hK).sub hc).const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h.const_sub 2 using 1
  · rfl
  · have hk : (0 : ℝ)<K := by exact_mod_cast hK
    field_simp [Hpi_pos.ne',hk.ne']
    ring

theorem limit_lt {K : ℕ} (hK : 0<K) :
    1-partitionEntropy/Hpi-2/(K : ℝ)<(7483/10000 : ℝ) := by
  have hratio : (2517/10000 : ℝ)<partitionEntropy/Hpi := by
    apply (lt_div_iff₀ Hpi_pos).mpr
    have := Hpi_bounds.2
    have := partitionEntropy_bounds.1
    linarith
  have hk : (0 : ℝ)<K := by exact_mod_cast hK
  have hh : 0<2/(K : ℝ) := by positivity
  linarith

theorem charge_eventually {K : ℕ} (hK : 0<K) :
    ∀ᶠ m : ℕ in atTop, charge K m<(7483/10000 : ℝ) :=
  (charge_tendsto hK).eventually (gt_mem_nhds (limit_lt hK))

theorem charge_eq {K m : ℕ} (hm : 0<m) :
    charge K m=2+2*Real.log (9/(nativePrime K m : ℝ))/Real.log (outputSize m : ℝ) := by
  have hp : (0 : ℝ)<nativePrime K m := by exact_mod_cast (nativePrime_prime K m).pos
  have hLen : (fixedLength m : ℝ)≠0 := by
    have hh : 0<fixedLength m := by unfold fixedLength; omega
    exact_mod_cast hh.ne'
  unfold charge nativeRate outputRate
  rw [Real.log_div (by norm_num) hp.ne']
  field_simp [hLen,log_two_pos.ne',TernaryPrincipalDimensions.output_log_pos hm |>.ne']
  ring

/-- Exact ordered collision recurrence, evaluated at the full original
radix depth. The finite selector's paid factor nine is included. -/
theorem collision_bound {K m n : ℕ} (hm : 0<m) (hn : 1<n)
    (hp9 : 9<nativePrime K m) (score : ℕ→ℕ)
    (hstep : ∀ j, nativePrime K m*score (j+1)≤9*score j)
    (hinit : score 0≤n^2) :
    (score (radixLength m n) : ℝ)≤(n : ℝ)^charge K m := by
  let p := nativePrime K m
  let r := radixLength m n
  have hp : (0 : ℝ)<p := by exact_mod_cast (nativePrime_prime K m).pos
  have hnR : (0 : ℝ)<n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hM : 1<outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hlogM := TernaryPrincipalDimensions.output_log_pos hm
  have hbound := TernaryPairedRecurrence.iterate_bound p 9 score hstep r
  have hboundR : (p : ℝ)^r*(score r : ℝ)≤(9 : ℝ)^r*(n : ℝ)^2 := by
    exact_mod_cast hbound.trans (Nat.mul_le_mul_left (9^r) hinit)
  have hfirst : (score r : ℝ)≤(9/(p : ℝ))^r*(n : ℝ)^2 := by
    have he : (9/(p : ℝ))^r*(n : ℝ)^2=((9 : ℝ)^r*(n : ℝ)^2)/(p : ℝ)^r := by
      rw [div_pow]
      ring
    rw [he]
    apply (le_div_iff₀ (pow_pos hp r)).mpr
    nlinarith [hboundR]
  have hcover : (n : ℝ)^2≤(outputSize m : ℝ)^r := by
    exact_mod_cast Nat.le_pow_clog hM (n^2)
  have hlogcover := Real.log_le_log (pow_pos hnR 2) hcover
  rw [Real.log_pow,Real.log_pow] at hlogcover
  have hr : 2*Real.log (n : ℝ)/Real.log (outputSize m : ℝ)≤(r : ℝ) := by
    apply (div_le_iff₀ hlogM).mpr
    simpa only [Nat.cast_ofNat] using hlogcover
  have hbase : 0<9/(p : ℝ) := by positivity
  have hbase1 : 9/(p : ℝ)≤1 := (div_le_one hp).mpr (by exact_mod_cast hp9.le)
  have hpow := Real.rpow_le_rpow_of_exponent_ge hbase hbase1 hr
  rw [Real.rpow_natCast] at hpow
  have heq : (9/(p : ℝ))^(2*Real.log (n : ℝ)/Real.log (outputSize m : ℝ))*(n : ℝ)^2=
      (n : ℝ)^charge K m := by
    rw [charge_eq hm,Real.rpow_def_of_pos hbase,←Real.rpow_natCast (n : ℝ) 2,
      Real.rpow_def_of_pos hnR,Real.rpow_def_of_pos hnR,←Real.exp_add]
    congr 1
    dsimp [p]
    push_cast
    ring
  exact hfirst.trans ((mul_le_mul_of_nonneg_right hpow (sq_nonneg (n : ℝ))).trans_eq heq)

/-- All exact paired, collision, preprocessing and principal cost margins
hold in one fixed block, chosen before inspecting the input. -/
theorem simultaneous_parameters {K : ℕ} (hK : 100000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      TernaryOversizeOverhead.overheadCharge (TernaryOversizeOverhead.selectedMoment K) c d m<
        TernaryOversizeOverhead.microAllowance K ∧
      TernarySignedPadding.carryExponent m (2^t) κ<TernaryOversizeOverhead.microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      (9*(nativeFamily K m (TernaryOversizeOverhead.selectedMoment K)).length)^4≤outputSize m ∧
      9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) := by
  have hk : 0<K := by omega
  have hh : ∀ᶠ m : ℕ in atTop, 9<nativePrime K m ∧ charge K m<(7483/10000 : ℝ) := by
    filter_upwards [TernarySignedParameters.native_large_eventually hk 9,charge_eventually hk] with m hp hc
    exact ⟨hp,hc⟩
  obtain ⟨N₀,hN₀⟩ := eventually_atTop.mp hh
  obtain ⟨t,m,ht,hm,hg,ho,hc,hminor,hp,hF⟩ :=
    TernaryPairedFamilyMargin.simultaneous_parameters hK hκ c d (max N N₀)
  exact ⟨t,m,ht,(le_max_left N N₀).trans hm,hg,ho,hc,hminor,hp,hF,
    hN₀ m ((le_max_right N N₀).trans hm)⟩

end ThreeSum.TernaryPairedCollisionRate
