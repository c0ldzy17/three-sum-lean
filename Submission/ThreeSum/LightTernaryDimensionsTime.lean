import Submission.ThreeSum.LightTernaryDimensions
import Submission.ThreeSum.TernaryExtensionBudget

noncomputable section
namespace ThreeSum.LightTernaryDimensions
open TernarySignedPadding TernaryExtensionEncoding TernaryCoverScale Filter Real
set_option maxHeartbeats 2000000

theorem time_linear_parameters (M b p K n U : ℕ) :
    time M b p K n U ≤ 1000*(p^(dim M b p K n U)+dim M b p K n U+J M b n U+3) := by
  have hJ : J M b n U=Nat.clog b (4*U+1)+r M n+1 := rfl
  have hdim : Nat.clog p (8*(J M b n U+3)*p^(4*K))=dim M b p K n U := by
    unfold dim menuDegree
    congr 1
  unfold time LightTernaryDigitLength.clogTime LightTernaryDigitLength.time LightNatPower.time
  change 20*r M n+20+(20*Nat.clog b (4*U+1)+20+60)+
    (20*Nat.clog p (8*(J M b n U+3)*p^(4*K))+20)+(20*dim M b p K n U+20)+250 ≤ _
  rw [hdim]
  omega

variable {p : ℕ} [Fact p.Prime]

/-- Runtime computation of every size parameter costs at most n^ε eventually. -/
theorem time_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ) (U : ℕ → ℕ)
    (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop, (time (outputSize m) b p K n (U n) : ℝ) ≤ (n : ℝ)^ε := by
  filter_upwards [extension_polynomial_budget (p := p) hm hb hκ hε 1000 (by norm_num) 1 K U hU]
    with n hn
  have ht := time_linear_parameters (outputSize m) b p K n (U n)
  have htR : (time (outputSize m) b p K n (U n) : ℝ) ≤
      1000*((p^(dim (outputSize m) b p K n (U n))+dim (outputSize m) b p K n (U n)+
        J (outputSize m) b n (U n)+3 : ℕ) : ℝ) := by exact_mod_cast ht
  apply htR.trans
  simpa only [dim,J,r,radixLength,pow_one,Nat.add_assoc] using hn

end ThreeSum.LightTernaryDimensions
