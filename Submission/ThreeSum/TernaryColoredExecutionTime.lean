import Submission.ThreeSum.TernaryColoredRuntimeCertificate

noncomputable section
namespace ThreeSum.TernaryColoredExecutionTime
open Light TernaryConcreteProfile TernaryColoredLoopSetup
variable {κ : ℕ}
set_option maxHeartbeats 1000000

private theorem empty_metadata (n U : ℕ) : TernaryPreparedOriginals.Metadata n U [] [] [] := by
  refine ⟨by simp,by simp,by simp,by simp,by simp,by simp,?_,?_⟩
  all_goals intro i;exact Fin.elim0 i

/-- The driver can pay for the first call and its branch before the
normalization output lists are known. -/
theorem preparation (P : Profile κ) (n free menu c : ℕ) (μ : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]
    (hcutoff : P.cutoff≤n) :
    LightTernaryColorPreparationProof.time n (J P n) (n^κ)+10000≤P.colorTime n := by
  have hh:=TernaryColoredRuntimeCertificate.body_time_le P n free menu c [] [] [] μ
    (empty_metadata n (n^κ)) (P.inputGuards n hcutoff)
  dsimp only at hh
  omega

end ThreeSum.TernaryColoredExecutionTime
