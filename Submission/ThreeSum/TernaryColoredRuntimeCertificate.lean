import Submission.ThreeSum.TernaryColoredTerminalReceipt
import Submission.ThreeSum.TernaryColoredFinalReady
import Submission.ThreeSum.TernaryColoredPrefixRuntimeIdentity
import Submission.ThreeSum.TernaryColoredRuntimeBounds
import Submission.ThreeSum.TernaryColoredQueryBudget
import Submission.ThreeSum.TernaryProfileRuntime

noncomputable section
namespace ThreeSum.TernaryColoredRuntimeCertificate
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open TernaryConcreteProfile TernaryLocalParameters TernaryColoredLoopSetup
open TernaryColoredTerminalReceipt TernaryActualPrefixRuntime
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000
variable {κ : ℕ}
variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]

/-- This ledger contains the actual prefix candidate data and final compact
source, canonical selected hashes and literal original cleanup arrays. -/
def state : TernaryActualColoredRuntime.State P.K P.m :=
  TernaryColoredPrefixRuntimeIdentity.runtimeState P n free menu c A B C initial
    (TernaryColoredFinalReady.selected P n free menu c A B C initial)
    (TernaryColoredFinalReady.cleanup P n free A B C)
    (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)

/-- All runtime-model hypotheses follow from normalized original inputs,
actual dimensions and the fixed selector's proved collision budgets. -/
theorem fits (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    TernaryActualColoredRuntime.Fits (k:=P.k) P.maps P.output
      (TernaryActualGlobalQueryRuntime.zeroState (state P n free menu c A B C initial))
      P.radix κ n P.wordD P.allocation.E P.p := by
  let S:=setup P n free menu c A B C initial
  have hbp : P.radix≤P.p := by have hh : 2*P.radix<P.p:=P.basePrime;omega
  have hcoll:=collision_bounds P n free menu c A B C initial hmeta hinputs
  refine {
    dimension:=rfl
    phases:=?_
    post:=?_
    seedB:=?_
    seedC:=?_
    seedO:=?_
    nA:=hmeta.lengthA
    nB:=hmeta.lengthB
    nC:=hmeta.lengthC
    modulus:=rfl
    width:=?_
    collisionB:=hcoll.1
    collisionC:=hcoll.2 }
  · intro j hj
    exact TernaryColoredRuntimeBounds.base P n free j A B C hj hmeta.lengthA hmeta.lengthB hmeta.lengthC
  · exact TernaryColoredRuntimeBounds.selected P n free (rounds P n) A B C
      (hash P n free menu c A B C initial) (fun i=>A.getD i 0) (fun i=>B.getD i 0) (fun i=>C.getD i 0)
      (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)
      le_rfl hmeta.lengthA hmeta.lengthB hmeta.lengthC
  · intro j hj seed
    exact ((TernaryColoredPrefixRuntimeIdentity.prefixData_bounds S j seed).1).le.trans hbp
  · intro j hj seed
    exact ((TernaryColoredPrefixRuntimeIdentity.prefixData_bounds S j seed).2.1).le.trans hbp
  · intro j hj seed
    exact ((TernaryColoredPrefixRuntimeIdentity.prefixData_bounds S j seed).2.2).le.trans hbp
  · change 2*(rounds P n*fixedLength P.m)≤2*fixedLength P.m*(J P n)
    have hr : rounds P n≤J P n:=hinputs.2.1.le
    simpa only [mul_assoc,mul_comm,mul_left_comm] using
      Nat.mul_le_mul_left (2*fixedLength P.m) hr

theorem query_cap : TernaryActualGlobalQueryRuntime.queryCap (state P n free menu c A B C initial) n≤
    queryTime P n free A B C := by
  exact TernaryActualGlobalQueryRuntime.queryCap_le _ (fun _ _=>le_rfl) le_rfl

/-- The separately priced global query maximum is charged exactly once. -/
theorem query_bound (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hn : 1<n) :
    (TernaryActualGlobalQueryRuntime.queryCap (state P n free menu c A B C initial) n:ℝ)≤
      (TernaryUniformQueryTime.coefficient P.m P.wordD P.allocation.E κ:ℝ)*
        ((state P n free menu c A B C initial).arena.J+1:ℕ)^3*
          TernaryCountFrontendBudget.envelope P.m (TernaryCoverScale.radixLength P.m n) := by
  exact (Nat.cast_le.mpr (query_cap P n free menu c A B C initial)).trans
    (TernaryColoredQueryBudget.query_time_bound P n free A B C hn hmeta.lengthA hmeta.lengthB hmeta.lengthC)

/-- The complete concrete runtime ledger is bounded by the size-only
per-color time used in the final theorem. No Fits or time premise remains. -/
theorem time_le (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    TernaryActualColoredRuntime.time (k:=P.k) P.maps P.output
      (state P n free menu c A B C initial) P.allocation.E κ P.H n≤P.colorTime n := by
  have hf:=fits P n free menu c A B C initial hmeta hinputs
  exact TernaryActualGlobalQueryRuntime.time_le_uniform (b:=localFactor P.m) (Hdet:=P.H) hf
    P.K_pos P.k_pos P.good hinputs.1 (by have := P.F_gt_one;omega) le_rfl le_rfl
    (P.local_nonempty false) (P.local_nonempty true)
    (query_bound P n free menu c A B C initial hmeta hinputs.1) 19 3 (local_factor_polynomial P.m)
    (full_exponent_lt P.large 19 3 P.good P.overhead).le

/-- Direct budget for the literal preprocessing, template, initial-budget,
executed prefix initialization/loop and final compact moment reporter. -/
theorem body_time_le (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n) :
    let S:=TernaryColoredLoopSetup.setup P n free menu c A B C initial
    LightTernaryColorPreparationProof.time n (J P n) (n^κ)+
      LightTernaryArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+S.initTime+
      LightTernaryPreparedPostSelection.time
        (TernaryArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
          (TernaryColoredFinalReady.selected P n free menu c A B C initial)) P.H
        (TernaryColoredFinalReady.cleanup P n free A B C)
        (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)+10000≤P.colorTime n := by
  intro S
  have hh:=time_le P n free menu c A B C initial hmeta hinputs
  have hi : S.initTime=TernaryActualSeedRuntime.allPrefixTime (k:=P.k) P.maps P.output
      (state P n free menu c A B C initial).phase (state P n free menu c A B C initial).arena
      (state P n free menu c A B C initial).seeds n :=
    TernaryColoredPrefixRuntimeIdentity.init_time P n free menu c A B C initial
      (TernaryColoredFinalReady.selected P n free menu c A B C initial)
      (TernaryColoredFinalReady.cleanup P n free A B C)
      (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)
  unfold TernaryActualColoredRuntime.time at hh
  rw [←hi] at hh
  change LightTernaryColorPreparationProof.time n (J P n) (n^κ)+
      LightTernaryArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+S.initTime+
      (LightTernaryPreparedPostSelection.time
        (TernaryArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
          (TernaryColoredFinalReady.selected P n free menu c A B C initial)) P.H
        (TernaryColoredFinalReady.cleanup P n free A B C)
        (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial)+673)+10000≤P.colorTime n at hh
  omega

end ThreeSum.TernaryColoredRuntimeCertificate
