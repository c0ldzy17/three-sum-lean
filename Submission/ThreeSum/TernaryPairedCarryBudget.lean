import Submission.ThreeSum.TernarySignedPreparationBudget
import Submission.ThreeSum.TernaryPairedInitial

noncomputable section
namespace ThreeSum.TernaryPairedCarryBudget
open Filter Real TernarySignedPreparationBudget TernarySignedPadding TernaryCoverScale
open scoped Topology

theorem initial_digit_carry_eventually {m b K : ℕ} (hm : 0<m) (hb : 1<b)
    {κ δ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m b κ<δ) (hδ : 4*δ<1)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      (2^(paddedLength b (U n) (radixLength m n)))^4*
        (paddedLength b (U n) (radixLength m n)+2)^(8*K)≤n := by
  have he : 0<1-4*δ := by linarith
  filter_upwards [padded_carry_eventually hm hb hκ hcarry U hU,
    polynomial_digit_budget hm hb hκ he 1 (by norm_num) (8*K) U hU,
    eventually_gt_atTop (1 : ℕ)] with n hc hp hn
  let J := paddedLength b (U n) (radixLength m n)
  let B := Nat.log 2 (3*U n+1)+2
  have hJB : J+2≤(J+1)*B := by dsimp [B]; nlinarith
  have hsmall := Nat.pow_le_pow_left hJB (8*K)
  rw [mul_pow] at hsmall
  have hsmallR : ((J+2 : ℕ) : ℝ)^(8*K)≤(J+1 : ℝ)^(8*K)*(B : ℝ)^(8*K) := by exact_mod_cast hsmall
  have hp' : ((J+2 : ℕ) : ℝ)^(8*K)≤(n : ℝ)^(1-4*δ) := by
    apply hsmallR.trans
    simpa [J,B] using hp
  have hc4 := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤2^J) hc 4
  have hnp : (0 : ℝ)<n := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hh := mul_le_mul hc4 hp' (by positivity) (by positivity)
  have heq : ((n : ℝ)^δ)^4*(n : ℝ)^(1-4*δ)=(n : ℝ) := by
    rw [←Real.rpow_natCast ((n : ℝ)^δ) 4,←Real.rpow_mul hnp.le,←Real.rpow_add hnp]
    norm_num only [Nat.cast_ofNat]
    rw [show δ*4+(1-4*δ)=1 by ring,Real.rpow_one]
  rw [heq] at hh
  exact_mod_cast hh

end ThreeSum.TernaryPairedCarryBudget
