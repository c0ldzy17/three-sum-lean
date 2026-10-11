import Submission.ThreeSum.LightNatPower

/-! # Scalar maximum for exact shared-bank dimensions -/

namespace ThreeSum.LightSourceControlsMax

open Light

def body : Stmt := .ite (v 0 <' v 1) (.set 0 (v 1)) (.set 0 (v 0))

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p a b : ℕ} (hp : P[p]?=some body) (μ : ℕ → ℤ)
    (hword : ((max a b : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P p d [a,b] μ 40 (fun r ν => r=((max a b : ℕ) : ℤ) ∧ ν=μ) := by
  have ha : (a : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hb : (b : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  apply Meets.of_body hp
  unfold body
  light_if hy hn : (a : ℤ) < (b : ℤ)
  · have hab : a ≤ b := by omega
    light_set (b : ℕ)
    exact ⟨by simp [max_eq_right hab],rfl⟩
  · have hba : b ≤ a := by omega
    light_set (a : ℕ)
    exact ⟨by simp [max_eq_left hba],rfl⟩

def program : Program := [body]

end ThreeSum.LightSourceControlsMax
