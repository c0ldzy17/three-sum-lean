import Submission.ThreeSum.TernaryUniformQueryTime
import Submission.ThreeSum.TernaryColoredLoopSetup

noncomputable section
namespace ThreeSum.TernaryColoredQueryBudget
open TernaryConcreteProfile TernaryColoredLoopSetup TernaryArenaSourceSetup
open TernaryLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def coefficient (P : Profile κ) : ℕ :=
  TernaryUniformQueryTime.coefficient P.m (256*(P.allocation.D+1)) P.allocation.E κ

/-- The single time value used by the real loop is bounded uniformly in
all source values, normalized lengths, free pointers and runtime fields. -/
theorem query_time_bound (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hn : 1<n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    (queryTime P n free A B C:ℝ)≤
      (coefficient P:ℝ)*(J P n+1:ℕ)^3*
        TernaryCountFrontendBudget.envelope P.m (rounds P n) := by
  have hword : ∀j≤TernaryCoverScale.radixLength P.m n,
      TernaryFrontendResources.eulerBound (N P.m j)
        (valueCap (r:=j) P.maps P.cap (baseInput P n free A B C))≤
      (256*(P.allocation.D+1))*(n+n^κ+1)^P.allocation.E := by
    intro j hj
    exact TernaryUniformQueryTime.allocated_word P.maps P.allocation (baseInput P n free A B C)
      hj hB hC (Nat.mul_le_mul_right _ hA) (le_refl _)
  have hh := TernaryUniformQueryTime.maximum_bound P.maps P.cap (baseInput P n free A B C)
    P.blockPositive hn (le_refl (n^κ)) hword
  change (queryTime P n free A B C:ℝ)≤
    (coefficient P:ℝ)*(TernaryCoverScale.radixLength P.m n+1:ℕ)^3*
      TernaryCountFrontendBudget.envelope P.m (rounds P n) at hh
  apply hh.trans
  have hr : TernaryCoverScale.radixLength P.m n≤J P n := by
    unfold J LightTernaryDimensions.J TernarySignedPadding.paddedLength LightTernaryDimensions.r Profile.M
    unfold TernaryCoverScale.radixLength
    omega
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (by exact_mod_cast Nat.pow_le_pow_left (Nat.add_le_add_right hr 1) 3)
      (Nat.cast_nonneg _)) (TernaryCountFrontendBudget.envelope_pos _ _).le

end ThreeSum.TernaryColoredQueryBudget
