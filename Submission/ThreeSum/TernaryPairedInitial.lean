import Submission.ThreeSum.TernaryPairedPotential

/-! The initial paired score is paid from actual original requester/carry
groups, original endpoint pairs, and the literal integer minors. -/

namespace ThreeSum.TernaryPairedInitial
open Finset Matrix TernaryPairedPotential
open scoped BigOperators

theorem initial_bound {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e)) ≤
      Fintype.card G*Fintype.card P^K*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
  calc
    _ ≤ ∑ _g : G, ∑ _e : Fin K → P, Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
      apply sum_le_sum
      intro g hg
      exact sum_le_sum fun e he => minorWeight_le (A g e) b (hA g e)
    _ = _ := by simp; ring

theorem initial_original_bound {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b n carries : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b)
    (hG : Fintype.card G≤n*carries) (hP : Fintype.card P≤n^2) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e)) ≤
      n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
  have hh := initial_bound K Λ b A hA
  have hcounts := Nat.mul_le_mul hG (Nat.pow_le_pow_left hP K)
  have h := Nat.mul_le_mul_right (Λ^(2*K)*((2*K).factorial*b^(2*K))^2) hcounts
  have he : n*carries*(n^2)^K*(Λ^(2*K)*((2*K).factorial*b^(2*K))^2) =
      n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
    rw [←pow_mul,pow_add,pow_one]
    ring
  rw [he] at h
  exact hh.trans (by simpa only [mul_assoc] using h)

/-- Carry and logarithmic factors only need one additional power of n
AFTER taking the fourth power. The determinant coefficient is fixed. -/
theorem initial_fourth_bound {P G : Type*} [Fintype P] [Fintype G]
    (K Λ b n carries C : ℕ) (A : G → (Fin K → P) → Matrix (Fin (2*K)) (Fin Λ) ℤ)
    (hA : ∀ g e i j, (A g e i j).natAbs≤b)
    (hG : Fintype.card G≤n*carries) (hP : Fintype.card P≤n^2)
    (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (∑ g : G, ∑ e : Fin K → P, minorWeight (A g e))^4 ≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) := by
  have hh := Nat.pow_le_pow_left (initial_original_bound K Λ b n carries A hA hG hP) 4
  have h := Nat.mul_le_mul_left (n^(8*K+4)*((2*K).factorial*b^(2*K))^8) hcarry
  calc
    _ ≤ (n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2)^4 := hh
    _ = (n^(8*K+4)*((2*K).factorial*b^(2*K))^8)*(carries^4*Λ^(8*K)) := by
      simp only [mul_pow,←pow_mul]
      have he : (2*K+1)*4=8*K+4 := by ring
      have he' : (2*K)*4=8*K := by ring
      rw [he,he']
      ring
    _ ≤ (n^(8*K+4)*((2*K).factorial*b^(2*K))^8)*(C*n) := h
    _ = _ := by rw [show 8*K+5=(8*K+4)+1 by omega,pow_succ]; ring

end ThreeSum.TernaryPairedInitial
