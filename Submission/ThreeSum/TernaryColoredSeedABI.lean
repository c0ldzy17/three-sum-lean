import Submission.ThreeSum.LightTernaryColoredInitializationProof
import Submission.ThreeSum.TernaryArenaInitialSeedHeader
import Submission.ThreeSum.TernaryPreparedOriginals

noncomputable section
namespace ThreeSum.TernaryColoredSeedABI
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open LightTernarySeedScoreFactory LightTernaryControllerFactory LightTernaryPrefixFinish
open LightTernaryColoredInitializationProof
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

theorem budgeted_header (C : Config) (seedCount newSpan K bDigit n nO : ℕ) :
    budgetedValues (header C seedCount 1 1 1 0 0 0 newSpan) K bDigit n C.J nO=
      header C seedCount 1 1 1 (n^2) (n^2) (LightTernaryInitialBudgets.initial K bDigit n C.J nO) newSpan :=by
  apply List.ext_getElem
  · simp [budgetedValues]
  · intro i hi hi'
    have hi48 : i<48:=by simpa [budgetedValues] using hi
    interval_cases i <;>
      simp [budgetedValues,budgetValues,header,LightTernarySeedController.args,Config.argv,withSeed,
        LightTernarySeedScore.args,Nat.pow_two]

/-- The actual runtime twenty-three inputs, including duplicate signed/tagged
matrix pointers, yield the canonical seed template. -/
theorem template (I : Input) (A : Inputs) (p n U R F q : ℕ)
    (hleft : A.leftTagged=A.Bmatrix) (hright : A.rightTagged=A.Cmatrix) :
    LightTernaryArenaTemplate.seedValues
      (frame (values n U I.free A.Bmatrix I.nB A.Cmatrix I.nC A.Omatrix I.requesterCount A.positions A.menu A.J p R F q))
      I.free I.capacity=header (config p 0 I A 0) (q*q) 1 1 1 0 0 0 (addr I.free I.capacity 8) :=by
  simpa only [values,LightTernaryArenaTemplate.args,hleft,hright,Nat.cast_add,Nat.cast_zero] using
    TernaryArenaInitialSeedHeader.template_values I A p (n+U) R F q

/-- This is the exact forty-eight-cell seed list produced by the literal
colored initialization chunk and consumed by entry237. -/
theorem budgeted_template (I : Input) (A : Inputs) (p n U R F q K bDigit : ℕ)
    (hleft : A.leftTagged=A.Bmatrix) (hright : A.rightTagged=A.Cmatrix) :
    budgetedValues (LightTernaryArenaTemplate.seedValues
      (frame (values n U I.free A.Bmatrix I.nB A.Cmatrix I.nC A.Omatrix I.requesterCount A.positions A.menu A.J p R F q))
      I.free I.capacity) K bDigit n A.J I.requesterCount=
      header (config p 0 I A 0) (q*q) 1 1 1 (n^2) (n^2)
        (LightTernaryInitialBudgets.initial K bDigit n A.J I.requesterCount) (addr I.free I.capacity 8) :=by
  rw [template I A p n U R F q hleft hright]
  exact budgeted_header _ _ _ _ _ _ _

end ThreeSum.TernaryColoredSeedABI
