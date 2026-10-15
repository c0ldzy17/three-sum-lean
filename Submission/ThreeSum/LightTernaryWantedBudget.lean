import Submission.ThreeSum.LightTernaryWantedCanonical
namespace ThreeSum.LightTernaryWantedBudget
open LightTernaryWantedCanonical

/-- Arithmetic cost depends on the bit length of the signed target. -/
theorem node_budget (P V W : ℕ) (hV : V ≤ 2^W) :
    overhead P V+stepCost V+40 ≤ 1000*(P+W+3) := by
  have hp : 1 ≤ 2^W := one_le_pow₀ (by omega : 1 ≤ (2 : ℕ))
  have hbound : 2*V+1 ≤ 2^(W+2) := by rw [pow_add]; norm_num; omega
  have hlog := Nat.log_mono_right (b := 2) hbound
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))] at hlog
  unfold overhead stepCost LightResidues.residueBudget LightTernaryDivide.time LightOutputDecodeDivide.budget
  omega

/-- With a fixed native radix and exponentially bounded target magnitude,
the actual DFS spends only a quadratic polynomial in block count per fiber. -/
theorem time_polynomial (P C V A J : ℕ) (hC : 1 ≤ C)
    (hV : V ≤ A*(P+1)^J) :
    time P C V J ≤ 1000*(A+2*P+4)*(J+1)^2*C^J := by
  have hA : A ≤ 2^A := (Nat.lt_two_pow_self).le
  have hP : P+1 ≤ 2^(P+1) := (Nat.lt_two_pow_self).le
  have hp : (P+1)^J ≤ (2^(P+1))^J := Nat.pow_le_pow_left hP J
  have hv : V ≤ 2^(A+(P+1)*J) := by
    calc
      V ≤ A*(P+1)^J := hV
      _ ≤ 2^A*(2^(P+1))^J := Nat.mul_le_mul hA hp
      _ = _ := by rw [← pow_mul,← pow_add]
  have hn := node_budget P V (A+(P+1)*J) hv
  have hl : P+(A+(P+1)*J)+3 ≤ (A+2*P+4)*(J+1) := by nlinarith
  have hlin : overhead P V+stepCost V+40 ≤ 1000*(A+2*P+4)*(J+1) := by
    calc
      _ ≤ 1000*(P+(A+(P+1)*J)+3) := hn
      _ ≤ 1000*((A+2*P+4)*(J+1)) := Nat.mul_le_mul_left _ hl
      _ = _ := by ring
  calc
    time P C V J ≤ (overhead P V+stepCost V+40)*(J+1)*C^J := time_bound P C V hC J
    _ ≤ (1000*(A+2*P+4)*(J+1))*(J+1)*C^J :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hlin)
    _ = _ := by ring
end ThreeSum.LightTernaryWantedBudget
