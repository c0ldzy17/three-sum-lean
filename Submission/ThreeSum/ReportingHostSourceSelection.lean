import Submission.ThreeSum.SourceBandFinite
import Submission.ThreeSum.LightCoverKeyData

/-! # Fifteen retained controls selected for one owner and occurrence -/

namespace ThreeSum.ReportingHostSourceSelection

open Light

set_option maxHeartbeats 1600000

structure Pointers where
  leftHeaders : ℕ
  rightHeaders : ℕ
  firstBank : ℕ
  bankSpan : ℕ
  occurrenceBase : ℕ
  startL : ℕ
  startR : ℕ
  sizeL : ℕ
  sizeR : ℕ
  offsetsL : ℕ
  flatL : ℕ
  offsetsR : ℕ
  flatR : ℕ
  stagesL : ℕ
  stagesR : ℕ
  maps : ℕ
  candidates : ℕ
  histL : ℕ
  histR : ℕ

def leftHead (X : Pointers) (i : ℕ) : ℕ := X.leftHeaders+6*i
def rightHead (X : Pointers) (j : ℕ) : ℕ := X.rightHeaders+6*j
def leftStageCell (X : Pointers) (i code : ℕ) : ℕ := X.firstBank+i*X.bankSpan+2*code
def rightStageCell (X : Pointers) (j code : ℕ) : ℕ := X.firstBank+j*X.bankSpan+2*code+1
def occurrenceRow (X : Pointers) (code J : ℕ) : ℕ := X.occurrenceBase+code*J

def values (X : Pointers) (srcB srcC code J : ℕ) : List ℕ :=
  [srcB+X.startL,srcC+X.startR,X.offsetsL,X.flatL,X.offsetsR,X.flatR,
    X.sizeL,X.sizeR,X.stagesL,X.stagesR,occurrenceRow X code J,
    X.maps,X.candidates,X.histL,X.histR]

structure HeaderReads (μ : ℕ→ℤ) (X : Pointers) (pair bank cover i j code : ℕ) : Prop where
  leftHeaders : μ pair=(X.leftHeaders : ℤ)
  rightHeaders : μ (pair+2)=(X.rightHeaders : ℤ)
  firstBank : μ bank=(X.firstBank : ℤ)
  bankSpan : μ (bank+2)=(X.bankSpan : ℤ)
  occurrenceBase : μ (bank+4)=(X.occurrenceBase : ℤ)
  startL : μ (leftHead X i)=(X.startL : ℤ)
  sizeL : μ (leftHead X i+1)=(X.sizeL : ℤ)
  offsetsL : μ (leftHead X i+4)=(X.offsetsL : ℤ)
  flatL : μ (leftHead X i+5)=(X.flatL : ℤ)
  startR : μ (rightHead X j)=(X.startR : ℤ)
  sizeR : μ (rightHead X j+1)=(X.sizeR : ℤ)
  offsetsR : μ (rightHead X j+4)=(X.offsetsR : ℤ)
  flatR : μ (rightHead X j+5)=(X.flatR : ℤ)
  stagesL : μ (leftStageCell X i code)=(X.stagesL : ℤ)
  stagesR : μ (rightStageCell X j code)=(X.stagesR : ℤ)
  maps : μ (cover+12)=(X.maps : ℤ)
  candidates : μ (cover+13)=(X.candidates : ℤ)
  histL : μ (cover+14)=(X.histL : ℤ)
  histR : μ (cover+15)=(X.histR : ℤ)

/-- An explicit polynomial address and intermediate-value bound for the
fixed selector. Every read occurs before its first write. -/
def space (X : Pointers) (pair bank cover srcB srcC i j code J dst : ℕ) : ℕ :=
  pair+bank+cover+dst+leftHead X i+rightHead X j+
    leftStageCell X i code+rightStageCell X j code+
    X.bankSpan+X.occurrenceBase+J+code+i+j+
    (values X srcB srcC code J).sum+100

/-- Individual address and scalar bounds for the fixed selector. Each translated
pointer occurs in its own bound, so an arbitrary already occupied prefix is
charged only once by callers. -/
structure Fits (X : Pointers) (pair bank cover srcB srcC i j code J dst stop : ℕ) : Prop where
  pair : pair+3≤stop
  bank : bank+5≤stop
  cover : cover+16≤stop
  output : dst+15≤stop
  leftHead : leftHead X i+6≤stop
  rightHead : rightHead X j+6≤stop
  leftStage : leftStageCell X i code+1≤stop
  rightStage : rightStageCell X j code+1≤stop
  occurrence : occurrenceRow X code J≤stop
  scalars : J+X.bankSpan+20≤stop
  values : ∀ v∈values X srcB srcC code J, v≤stop

theorem fits_of_space (X : Pointers) (pair bank cover srcB srcC i j code J dst stop : ℕ)
    (hs : space X pair bank cover srcB srcC i j code J dst≤stop) :
    Fits X pair bank cover srcB srcC i j code J dst stop := by
  simp only [space,values,List.sum_cons,List.sum_nil,leftHead,rightHead,leftStageCell,
    rightStageCell,occurrenceRow] at hs
  refine ⟨by omega,by omega,by omega,by omega,?_,?_,?_,?_,?_,by omega,?_⟩
  · unfold leftHead; omega
  · unfold rightHead; omega
  · unfold leftStageCell; omega
  · unfold rightStageCell; omega
  · unfold occurrenceRow; omega
  · intro v hv
    simp only [values,List.mem_cons,List.not_mem_nil,or_false] at hv
    rcases hv with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst v <;>
      (try dsimp only [occurrenceRow]) <;> omega

end ThreeSum.ReportingHostSourceSelection
