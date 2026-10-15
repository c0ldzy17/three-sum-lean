import Submission.ThreeSum.TernaryNativeMomentBounds
import Mathlib.Data.Nat.Choose.Bounds

/-! Uniform, fixed-degree original-source word bounds for all moment
channels. These bounds feed the source readiness certificates directly. -/
namespace ThreeSum.TernaryMomentWeightBounds
open LightTernaryMomentChannelFactory

def leftBound (U K : ℕ) : ℕ :=2^K*(U+1)^K
def rightBound (U K : ℕ) : ℕ :=(U+1)^K
def leftWord (U K : ℕ) : ℕ :=U+2*(2^K+1)*(U+2)^K
def rightWord (U K : ℕ) : ℕ :=U+2*(U+1)^K

theorem choose_bound {k j K : ℕ} (hk : k≤K) : (k.choose j : ℤ)≤(2 : ℤ)^K := by
  have hc := (Nat.choose_le_two_pow k j).trans (Nat.pow_le_pow_right (by decide : 1≤2) hk)
  exact_mod_cast hc

theorem left_bound {U K k j : ℕ} (x : ℤ) (hx : |x|≤(U : ℤ)) (hk : k≤K) (hj : j≤k) :
    |(k.choose j : ℤ)*(-x)^j|≤(leftBound U K : ℤ) := by
  rw [abs_mul,abs_pow,abs_neg,Int.abs_natCast]
  have hp := (pow_le_pow_left₀ (abs_nonneg x) (show |x|≤(U : ℤ)+1 by omega) j).trans
    (pow_le_pow_right₀ (show (1 : ℤ)≤U+1 by omega) (show j≤K by omega))
  have hh := mul_le_mul (choose_bound (j := j) hk) hp (by positivity) (by positivity : (0 : ℤ)≤2^K)
  simpa [leftBound] using hh

theorem right_bound {U K k j : ℕ} (x : ℤ) (hx : |x|≤(U : ℤ)) (hk : k≤K) :
    |x^(k-j)|≤(rightBound U K : ℤ) := by
  rw [abs_pow]
  have hp := (pow_le_pow_left₀ (abs_nonneg x) (show |x|≤(U : ℤ)+1 by omega) (k-j)).trans
    (pow_le_pow_right₀ (show (1 : ℤ)≤U+1 by omega) (show k-j≤K by omega))
  simpa [rightBound] using hp

theorem left_word_bound {U K k j : ℕ} (hk : k≤K) (hj : j≤k) :
    max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤(leftWord U K : ℤ) := by
  have hc := choose_bound (j := j) hk
  have hp := pow_le_pow_right₀ (show (1 : ℤ)≤U+2 by omega) (show j≤K by omega)
  have hm := mul_le_mul (show (2 : ℤ)*(k.choose j+1)≤2*(2^K+1) by omega)
    hp (by positivity) (by positivity : (0 : ℤ)≤2*(2^K+1))
  unfold leftWord
  push_cast
  apply max_le <;> nlinarith [show (0 : ℤ)≤2*(2^K+1)*((U : ℤ)+2)^K by positivity]

theorem right_word_bound {U K k j : ℕ} (hk : k≤K) :
    max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤(rightWord U K : ℤ) := by
  have hp := pow_le_pow_right₀ (show (1 : ℤ)≤U+1 by omega) (show k-j≤K by omega)
  have hm := mul_le_mul_of_nonneg_left hp (by decide : (0 : ℤ)≤2)
  unfold rightWord
  push_cast
  apply max_le <;> nlinarith [show (0 : ℤ)≤2*((U : ℤ)+1)^K by positivity]

end ThreeSum.TernaryMomentWeightBounds
