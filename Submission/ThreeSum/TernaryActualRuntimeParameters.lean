import Submission.ThreeSum.TernaryActualSeedRuntime
import Submission.ThreeSum.TernarySignedParameters

/-! A simultaneous fixed parameter choice for the actual prefix runtime,
including the physical digit carry count and every polynomial digit cost. -/
noncomputable section
namespace ThreeSum.TernaryActualRuntimeParameters
open TernaryActualPrefixRuntime TernaryActualSeedRuntime TernaryOversizePrime
open TernaryOversizeOverhead TernaryOversizeRates TernarySignedPadding
set_option maxHeartbeats 2000000

theorem runtime_margin {K m : ℕ} (hK : 100000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    fullExponent K (selectedMoment K) c d m+microAllowance K+(1/10000:ℝ)<
      TernaryParameters.targetExponent:=by
  have ht:=full_exponent_lt hK c d hgood hover
  have hk : (100000000:ℝ)≤K:=by exact_mod_cast hK
  have hp : (0:ℝ)<K:=by linarith
  have hμ : microAllowance K<(1/10000:ℝ):=by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  norm_num [TernaryCountFrontendBudget.frontendExponent,TernaryParameters.targetExponent] at ht ⊢
  linarith

/-- The digit radix and one sufficiently large fixed ternary block meet
both the exact minor guard and the complete runtime exponent budget. -/
theorem simultaneous_parameters {K : ℕ} (hK : 100000000≤K)
    {κ : ℝ} (hκ : 0≤κ) (c d N : ℕ) :
    ∃ t m : ℕ, 0<t ∧ N≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      carryExponent m (2^t) κ<microAllowance K ∧
      (2*K).factorial*(2^t)^(2*K)<nativePrime K m ∧
      2*(2^t)<nativePrime K m ∧
      fullExponent K (selectedMoment K) c d m+microAllowance K+(1/10000:ℝ)<
        TernaryParameters.targetExponent:=by
  obtain ⟨t,m,ht,hN,hgood,hover,hcarry,hminor,hprime⟩:=
    TernarySignedParameters.simultaneous_parameters hK hκ c d N
  exact ⟨t,m,ht,hN,hgood,hover,hcarry,hminor,hprime,runtime_margin hK c d hgood hover⟩

end ThreeSum.TernaryActualRuntimeParameters
