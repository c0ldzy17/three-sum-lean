import Submission.ThreeSum.TernaryPairedInitial

namespace ThreeSum.TernaryPairedInitialBudget

/-- An explicitly computable upper budget: no initial minor is evaluated. -/
def upper (K Λ b n carries : ℕ) : ℕ :=
  n^(2*K+1)*carries*Λ^(2*K)*((2*K).factorial*b^(2*K))^2

theorem fourth_bound (K Λ b n carries C : ℕ)
    (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (upper K Λ b n carries)^4≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) := by
  have h := Nat.mul_le_mul_left (n^(8*K+4)*((2*K).factorial*b^(2*K))^8) hcarry
  calc
    _ = (n^(8*K+4)*((2*K).factorial*b^(2*K))^8)*(carries^4*Λ^(8*K)) := by
      unfold upper
      simp only [mul_pow,←pow_mul]
      have h1 : (2*K+1)*4=8*K+4 := by omega
      have h2 : 2*K*4=8*K := by omega
      rw [h1,h2]
      ring
    _ ≤ _ := h
    _ = _ := by
      rw [show 8*K+5=(8*K+4)+1 by omega,pow_succ]
      ring


theorem target_count_le (K Λ b n carries targets : ℕ) (ht : targets≤n*carries) :
    targets*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2≤upper K Λ b n carries := by
  unfold upper
  calc
    _ ≤ (n*carries)*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2 := by
      gcongr
    _ = _ := by rw [pow_succ]; ring

theorem target_count_fourth_bound (K Λ b n carries targets C : ℕ)
    (ht : targets≤n*carries) (hcarry : carries^4*Λ^(8*K)≤C*n) :
    (targets*n^(2*K)*Λ^(2*K)*((2*K).factorial*b^(2*K))^2)^4≤
      (C*((2*K).factorial*b^(2*K))^8)*n^(8*K+5) :=
  (Nat.pow_le_pow_left (target_count_le K Λ b n carries targets ht) 4).trans
    (fourth_bound K Λ b n carries C hcarry)

end ThreeSum.TernaryPairedInitialBudget
