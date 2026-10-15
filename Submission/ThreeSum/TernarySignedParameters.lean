import Submission.ThreeSum.TernarySignedPadding

/-! One simultaneous choice of actual digit base, block, and native prime. -/
noncomputable section
namespace ThreeSum.TernarySignedParameters
open Filter Real TernarySignedPadding TernaryCoverScale TernaryOversizeOverhead
open TernaryOversizePrime TernaryEntropyRates TernaryLocalParameters
open TernaryOversizeRates TernaryParameters
open scoped Topology

theorem output_log_atTop :
    Tendsto (fun m => Real.log (outputSize m : ℝ)) atTop atTop := by
  have h := denominator_atTop.atTop_mul_pos Hpi_pos actual_output_rate
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  unfold outputRate
  have hlen : (fixedLength m : ℝ)≠0 := by
    have hp : 0<fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hp.ne'
  field_simp [hlen,log_two_pos.ne']

theorem native_log_atTop {K : ℕ} (hK : 0<K) :
    Tendsto (fun m => Real.log (nativePrime K m : ℝ)) atTop atTop := by
  have hc : 0<(Hpi+partitionEntropy)/2+Hpi/K := by
    have hpart : 0<partitionEntropy := by linarith [partitionEntropy_bounds.1]
    exact add_pos (half_pos (add_pos Hpi_pos hpart))
      (div_pos Hpi_pos (by exact_mod_cast hK))
  have h := denominator_atTop.atTop_mul_pos hc (native_rate_tendsto hK)
  apply h.congr'
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
  unfold nativeRate
  have hlen : (fixedLength m : ℝ)≠0 := by
    have hp : 0<fixedLength m := by unfold fixedLength; positivity
    exact_mod_cast hp.ne'
  field_simp [hlen,log_two_pos.ne']

theorem native_large_eventually {K : ℕ} (hK : 0<K) (D : ℕ) :
    ∀ᶠ m : ℕ in atTop, D<nativePrime K m := by
  filter_upwards [(native_log_atTop hK).eventually_gt_atTop (D : ℝ)] with m hm
  have hlog := Real.log_le_self (Nat.cast_nonneg (nativePrime K m) : (0 : ℝ)≤_)
  exact_mod_cast hm.trans_le hlog

theorem padding_slope_tendsto_zero :
    Tendsto (fun m => 2*Real.log 2/Real.log (outputSize m : ℝ)) atTop (𝓝 0) :=
  output_log_atTop.const_div_atTop _

theorem power_two_base {κ δ : ℝ} (hκ : 0≤κ) (hδ : 0<δ) :
    ∃ t : ℕ, 0<t ∧ 1<2^t ∧ κ*Real.log 2/Real.log ((2^t : ℕ) : ℝ)<δ/2 := by
  obtain ⟨t,ht⟩ := exists_nat_gt (2*κ/δ)
  have htR : (0 : ℝ)<t := lt_of_le_of_lt (by positivity : (0 : ℝ)≤2*κ/δ) ht
  have htN : 0<t := by exact_mod_cast htR
  have hp : 2≤2^t := by
    simpa using (Nat.pow_le_pow_right (by decide : 0<(2 : ℕ)) (show 1≤t by omega))
  refine ⟨t,htN,by omega,?_⟩
  have he : Real.log ((2^t : ℕ) : ℝ)=(t : ℝ)*Real.log 2 := by
    rw [Nat.cast_pow,Real.log_pow]
    norm_num
  rw [he]
  have heq : κ*Real.log 2/((t : ℝ)*Real.log 2)=κ/(t : ℝ) := by
    field_simp [htR.ne',log_two_pos.ne']
  rw [heq]
  apply (div_lt_iff₀ htR).mpr
  have hh := (div_lt_iff₀ hδ).mp ht
  nlinarith

/-- The base is fixed first. The block is then chosen far enough out for
all principal charges, repeated local losses, padding, and original-row
integer-minor preservation to hold simultaneously. -/
theorem simultaneous_parameters {K : ℕ} (hK : 100000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m := by
  have hk : 0<K := by omega
  have hδ : 0<microAllowance K := by unfold microAllowance; positivity
  obtain ⟨t,ht,hbase,hslope⟩ := power_two_base hκ hδ
  have hpadd := padding_slope_tendsto_zero.eventually
    (gt_mem_nhds (half_pos hδ))
  have h : ∀ᶠ m : ℕ in atTop, N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧ 2*(2^t)<nativePrime K m := by
    filter_upwards [eventually_ge_atTop N,goodBlock_eventually hK,
      small_overhead_eventually hk c d,hpadd,
      native_large_eventually hk ((2*K).factorial*(2^t)^(2*K)),
      native_large_eventually hk (2*(2^t))] with m hN hg ho hpad hminor hp
    refine ⟨hN,hg,ho,?_,hminor,hp⟩
    unfold carryExponent
    linarith only [hslope,hpad]
  obtain ⟨m,hm⟩ := h.exists
  exact ⟨t,m,ht,hm⟩

end ThreeSum.TernarySignedParameters
