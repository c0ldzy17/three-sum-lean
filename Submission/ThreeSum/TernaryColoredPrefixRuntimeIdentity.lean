import Submission.ThreeSum.TernaryColoredLoopSetup
import Submission.ThreeSum.TernaryActualColoredRuntime

noncomputable section
namespace ThreeSum.TernaryColoredPrefixRuntimeIdentity
open Light TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaLoop
open LightTernarySeedScoreFactory TernaryConcreteProfile TernaryColoredLoopSetup
open TernaryActualSeedRuntime
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

/-- The literal data used by each positive-prefix candidate. The unused
zero prefix has empty logical data and the same fixed magnitude bounds. -/
def prefixData {p m F K N : ℕ} [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (S : Setup p m F K N E) : (j seed : ℕ)→Data (config p j S.input S.arrays seed)
  | 0, _ => {
      oldB:=fun _=>0
      oldC:=fun _=>0
      oldO:=fun _=>0
      B:=fun _ _=>0
      Cvalues:=fun _ _=>0
      O:=fun _ _=>0
      coeff:=fun _=>0
      position:=S.input.positions
      catalog:=fun _ _=>0
      logicalRows:=[]
      logicalRow:=0
      bB:=S.featureBound
      bC:=S.featureBound
      bO:=S.featureBound }
  | j+1, seed => TernaryArenaPhase.dataAt S.input S.arrays j S.featureBound S.ell
      (TernaryArenaFamilyBudget.seedAt S.enumeration) S.L S.R S.O (S.state j) (fun _ _=>0) seed

theorem prefixData_bounds {p m F K N : ℕ} [Fact p.Prime]
    {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
    (S : Setup p m F K N E) (j seed : ℕ) :
    (prefixData S j seed).bB=S.featureBound ∧
    (prefixData S j seed).bC=S.featureBound ∧
    (prefixData S j seed).bO=S.featureBound :=by
  cases j <;> exact ⟨rfl,rfl,rfl⟩

variable {κ : ℕ}

/-- The runtime ledger contains the actual fixed arena, physical candidate
data, and postselection data supplied by the actual final caller. -/
def runtimeState (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]
    (post : Input) (cleanup : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) :
    TernaryActualColoredRuntime.State P.K P.m where
  arena:=(setup P n free menu c A B C μ).arrays
  phase:=fun _=>(setup P n free menu c A B C μ).input
  seeds:=prefixData (setup P n free menu c A B C μ)
  post:=post
  cleanup:=cleanup
  keysB:=keysB
  keysC:=keysC

theorem stage_time (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))] (j : ℕ) :
    let S:=setup P n free menu c A B C μ
    prefixStageTime (k:=P.k) P.maps P.output S.input S.arrays (prefixData S (j+1))=S.timeAt j :=by
  dsimp only
  let S:=setup P n free menu c A B C μ
  rw [prefixStageTime_eq_step P.maps P.output S.input S.arrays (prefixData S (j+1))
    (S.prefixInput j) rfl rfl rfl rfl rfl]
  rw [prefixSeedTime_eq_core P.maps P.output S.input S.arrays (prefixData S (j+1)) P.radix S.L S.R]
  rfl

/-- The physical finite-sup loop budget is exactly the all-prefix budget
used by the size-only runtime analysis. -/
theorem init_time (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (μ : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]
    (post : Input) (cleanup : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) :
    (setup P n free menu c A B C μ).initTime=
      allPrefixTime (k:=P.k) P.maps P.output
        (runtimeState P n free menu c A B C μ post cleanup keysB keysC).phase
        (runtimeState P n free menu c A B C μ post cleanup keysB keysC).arena
        (runtimeState P n free menu c A B C μ post cleanup keysB keysC).seeds n :=by
  dsimp only [runtimeState,allPrefixTime]
  let S:=setup P n free menu c A B C μ
  have hstage : (Finset.range S.rounds).sup S.timeAt=
      allStageTime (k:=P.k) P.maps P.output (fun _=>S.input) S.arrays (prefixData S) n :=by
    change (Finset.range (TernaryCoverScale.radixLength P.m n)).sup S.timeAt=_
    unfold allStageTime
    exact congrArg (fun f : ℕ→ℕ => (Finset.range (TernaryCoverScale.radixLength P.m n)).sup f)
      (funext fun j => (stage_time P n free menu c A B C μ j).symm)
  have hr : S.rounds=TernaryCoverScale.radixLength P.m n:=rfl
  have hh:=congrArg (LightTernaryPrefixInit.time (config P.p 0 S.input S.arrays 0) S.rounds) hstage
  simpa only [Setup.initTime,Setup.stepTime,S,hr,Profile.p] using hh

end ThreeSum.TernaryColoredPrefixRuntimeIdentity
