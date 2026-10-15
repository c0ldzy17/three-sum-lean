import Submission.ThreeSum.TernaryExtensionCandidates
import Submission.ThreeSum.TernarySignedPreparationBudget

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Filter Real TernarySignedPadding TernaryCoverScale
open TernarySignedPreparationBudget
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem degree_le_field_size (d : ℕ) : d≤p^d := by
  induction d with
  | zero => simp
  | succ d ih =>
    rw [pow_succ]
    have hp := (Fact.out : p.Prime).one_lt
    have hpos := pow_pos (Fact.out : p.Prime).pos d
    nlinarith

theorem menu_parameters_bound (J K : ℕ) :
    p^(menuDegree p (J+2) K)+menuDegree p (J+2) K+(J+2)+1≤
      (48*p^(4*K+1)+3)*(J+1) := by
  have hq := menu_field_upper (p := p) (J+2) K
  have hd := degree_le_field_size (p := p) (menuDegree p (J+2) K)
  have hmul : 8*p^(4*K+1)*(J+2+1)≤24*p^(4*K+1)*(J+1) := by
    have hh := Nat.mul_le_mul_left (8*p^(4*K+1)) (show J+2+1≤3*(J+1) by omega)
    nlinarith
  nlinarith

/-- Every fixed polynomial cost of constructing the field, its complete
multiplication table, and every seed row is absorbed into any positive power
of the original input length. The field size is the actual ceiling-log size. -/
theorem extension_polynomial_budget {m b : ℕ} (hm : 0<m) (hb : 1<b)
    {κ ε : ℝ} (hκ : 0≤κ) (hε : 0<ε) (A : ℝ) (hA : 0≤A) (D K : ℕ)
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ) :
    ∀ᶠ n : ℕ in atTop,
      let J := paddedLength b (U n) (radixLength m n)
      A*((p^(menuDegree p (J+2) K)+menuDegree p (J+2) K+(J+2)+1 : ℕ) : ℝ)^D≤
        (n : ℝ)^ε := by
  let C : ℝ := (48*p^(4*K+1)+3 : ℕ)
  have hC : 0≤C := by dsimp [C]; positivity
  filter_upwards [polynomial_digit_budget hm hb hκ hε (A*C^D) (by positivity) D U hU] with n hn
  dsimp only
  let J := paddedLength b (U n) (radixLength m n)
  have hparams : ((p^(menuDegree p (J+2) K)+menuDegree p (J+2) K+(J+2)+1 : ℕ) : ℝ)≤
      C*((J : ℝ)+1) := by
    dsimp [C]
    exact_mod_cast menu_parameters_bound (p := p) J K
  have hp := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) hparams D) hA
  have hlog : (1 : ℝ)≤((Nat.log 2 (3*U n+1) : ℝ)+2)^D :=
    one_le_pow₀ (by have h : (0 : ℝ)≤(Nat.log 2 (3*U n+1) : ℝ) := Nat.cast_nonneg _; linarith)
  calc
    _ ≤ A*(C*((J : ℝ)+1))^D := hp
    _ = A*C^D*((J : ℝ)+1)^D := by rw [mul_pow]; ring
    _ ≤ A*C^D*((J : ℝ)+1)^D*((Nat.log 2 (3*U n+1) : ℝ)+2)^D :=
      le_mul_of_one_le_right (by positivity) hlog
    _ ≤ _ := hn

end ThreeSum.TernaryExtensionEncoding
