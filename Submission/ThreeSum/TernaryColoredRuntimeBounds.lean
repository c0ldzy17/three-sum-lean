import Submission.ThreeSum.TernaryColoredLoopAllocation
import Submission.ThreeSum.TernaryActualColoredRuntime
import Submission.ThreeSum.TernaryUniformQueryTime
import Submission.ThreeSum.TernaryArenaSelectedCollisions
import Submission.ThreeSum.TernaryArenaQueryTimeMonotone

noncomputable section
namespace ThreeSum.TernaryColoredRuntimeBounds
open TernaryConcreteProfile TernaryColoredLoopSetup TernaryArenaSourceSetup
open TernaryArenaSeedCandidate LightTernarySeedScoreFactory TernaryLocalParameters
open TernaryActualColoredRuntime
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def zeroInput (I : Input) : Input := {I with queryTime:=0}

def coefficient (P : Profile κ) : ℕ :=256*(P.allocation.D+1)

/-- Zero-query analysis retains all actual source keys and requester rows.
Only the separately charged query-time field is reset. -/
theorem zero_native (P : Profile κ) (I : Input) (n j : ℕ)
    (hj : j≤rounds P n) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(J P n)) (hw : I.weightCap≤weight P n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput I)
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  refine ⟨hB,hC,hO,?_,Nat.zero_le _⟩
  exact TernaryUniformQueryTime.allocated_word P.maps P.allocation (zeroInput I) hj hB hC hO hw

/-- Every phase's allocated source dimensions and physical requester count
satisfy the native runtime model. -/
theorem base (P : Profile κ) (n free j : ℕ) (A B C : List ℤ)
    (hj : j≤rounds P n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput (input P n free A B C))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  apply zero_native P _ n j hj hB hC (Nat.mul_le_mul_right _ hA) le_rfl

/-- Actual append outputs may have arbitrary repeated native keys; they do
not alter the counted source sizes or allocated coefficient bounds. -/
theorem source (P : Profile κ) (I : Input) (A : Inputs) (n j seed : ℕ)
    (D : Data (config P.p j I A seed))
    (hj : j≤rounds P n) (hB : I.nB≤n) (hC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(J P n)) (hw : I.weightCap≤weight P n) :
    NativeBounds (k:=P.k) P.maps P.output (zeroInput (sourceInput I A seed D))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  exact zero_native P (sourceInput I A seed D) n j hj hB hC hO hw

/-- Runtime source bounds remain valid after actual singleton compaction
and the exact selected-hash re-encoding of the original values. -/
theorem selected (P : Profile κ) (n free j : ℕ) (A B C : List ℤ)
    (H : (TernarySignedReduction.Coordinate (J P n)→ZMod P.p)→ₗ[ZMod P.p] (Fin j→ZMod P.p))
    (valuesA valuesB valuesC : ℕ→ℤ) (keysB keysC : ℕ→ℕ)
    (hj : j≤rounds P n) (hA : A.length≤n) (hB : B.length≤n) (hC : C.length≤n) :
    NativeBounds (k:=P.k) P.maps P.output
      (zeroInput (TernaryArenaPostSelection.selectedInput (input P n free A B C)
        (n^κ) P.radix A.length H valuesA valuesB valuesC keysB keysC))
      n (n^κ) κ (2^(J P n)) (coefficient P) P.allocation.E j := by
  apply zero_native P _ n j hj
  · exact (LightOriginalSurvivors.length_le keysB B.length).trans hB
  · exact (LightOriginalSurvivors.length_le keysC C.length).trans hC
  · exact Nat.mul_le_mul_right _ hA
  · exact le_rfl

end ThreeSum.TernaryColoredRuntimeBounds
