import Submission.ThreeSum.LightExtensionBackendSetup
import Submission.ThreeSum.LightExtensionBackendBudget
import Submission.ThreeSum.TernaryExtensionBudget

noncomputable section
namespace ThreeSum.LightExtensionBackendSetup
open LightExtensionBackendLayout TernaryExtensionEncoding TernarySignedPadding TernaryCoverScale Filter Real
set_option maxHeartbeats 2000000

theorem time_polynomial (base d p q J : ℕ) :
    time base d p q J ≤ 20000000000*(d+p+q+J+2)^10 := by
  have ht := LightExtensionBackend.time_polynomial (factor base d p q J) q J
    (a base d q J) (b base d q J) (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
  have ht' : LightExtensionBackend.time (factor base d p q J) q J
      (a base d q J) (b base d q J) (h base d q J) (r base d q J) (prod base d q J) (sum base d q J)
      (LightIrreducibleFinder.uniformFactorTime d p q) ≤ 10000000000*(d+p+q+J+2)^10 := by
    simpa only [factor] using ht
  have h1 : 1 ≤ (d+p+q+J+2)^10 := Nat.one_le_pow _ _ (by omega)
  unfold time
  omega

theorem parameters_with_base (d p q J : ℕ) : d+p+q+J+2 ≤ (p+1)*(q+d+(J+2)+1) := by
  have hh : p ≤ p*(q+d+(J+2)+1) := Nat.le_mul_of_pos_right _ (by omega)
  calc
    _ ≤ p+(q+d+(J+2)+1) := by omega
    _ ≤ p*(q+d+(J+2)+1)+(q+d+(J+2)+1) := Nat.add_le_add_right hh _
    _ = _ := by ring

variable {p : ℕ} [Fact p.Prime]

/-- Fixed polynomial overhead of the fully concrete field backend is subpolynomial in n. -/
theorem parameter_polynomial_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (A : ℝ) (hA : 0 ≤ A) (D K : ℕ)
    (U : ℕ → ℕ) (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      let d := menuDegree p (J+2) K
      A*((d+p+p^d+J+2 : ℕ) : ℝ)^D ≤ (n : ℝ)^ε := by
  filter_upwards [extension_polynomial_budget (p := p) hm hb hκ hε
    (A*(p+1)^D) (by positivity) D K U hU] with n hn
  dsimp only
  let J := paddedLength b (U n) (radixLength m n)
  let d := menuDegree p (J+2) K
  have hp : (((d+p+p^d+J+2 : ℕ) : ℝ)) ≤ (p+1)*((p^d+d+(J+2)+1 : ℕ) : ℝ) := by
    exact_mod_cast parameters_with_base d p (p^d) J
  have hpow := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hp D) hA
  calc
    _ ≤ A*((p+1)*((p^d+d+(J+2)+1 : ℕ) : ℝ))^D := hpow
    _ = A*(p+1)^D*(((p^d+d+(J+2)+1 : ℕ) : ℝ))^D := by rw [mul_pow]; ring
    _ ≤ _ := hn

theorem time_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ) (U base : ℕ → ℕ)
    (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      let d := menuDegree p (J+2) K
      (time (base n) d p (p^d) J : ℝ) ≤ (n : ℝ)^ε := by
  filter_upwards [parameter_polynomial_eventually (p := p) hm hb hκ hε
    20000000000 (by norm_num) 10 K U hU] with n hn
  dsimp only
  let J := paddedLength b (U n) (radixLength m n)
  let d := menuDegree p (J+2) K
  have htR : (time (base n) d p (p^d) J : ℝ) ≤
      20000000000*((d+p+p^d+J+2 : ℕ) : ℝ)^10 := by
    exact_mod_cast time_polynomial (base n) d p (p^d) J
  exact htR.trans hn

theorem reserve_eventually {m b : ℕ} (hm : 0 < m) (hb : 1 < b)
    {κ ε : ℝ} (hκ : 0 ≤ κ) (hε : 0 < ε) (K : ℕ) (U : ℕ → ℕ)
    (hU : ∀ n, 1 < n → (U n : ℝ) ≤ (n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      let d := menuDegree p (J+2) K
      (reserve d p (p^d) J : ℝ) ≤ (n : ℝ)^ε := by
  filter_upwards [parameter_polynomial_eventually (p := p) hm hb hκ hε
    100000000 (by norm_num) 6 K U hU] with n hn
  simpa only [reserve,params,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hn

end ThreeSum.LightExtensionBackendSetup
