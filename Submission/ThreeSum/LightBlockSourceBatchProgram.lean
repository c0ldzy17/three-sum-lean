import Submission.ThreeSum.LightBlockSourceBatch
import Submission.ThreeSum.LightBlockSourceRetainedProgram

/-!
# Closed actual source-bank catalog program

The existing 41-procedure library is retained unchanged. Two host procedures
are appended with their actual call indices, giving a fixed 43-procedure
program. The table contains no source-function oracle and no Q enumeration.
-/

namespace ThreeSum.LightBlockSourceBatchProgram

open Light SubsetAddress

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def program : Program := LightBlockSourceRetainedProgram.program ++
  [LightBlockSourceBatchStep.body 0,LightBlockSourceBatch.body 41]

/-- The original procedure indices are unchanged by appending the hosts. -/
def sourceProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩

def programProcs : LightBlockSourceBatch.Procs program 42 :=
  ⟨41,⟨0,sourceProcs,rfl⟩,rfl⟩

theorem program_length : program.length=43 := rfl

theorem time_bound {count h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceBatch.time count h J cut ≤
      (count+1)*(LightBlockSourceRetainedProgram.factor h J+720)*(downsetCap (J*(512*h)) cut+1) := by
  have ht := LightBlockSourceRetainedProgram.time_le_factor hcut
  have hc : 1 ≤ downsetCap (J*(512*h)) cut+1 := by omega
  have hb : LightBlockSourceRetainedHost.time h J cut+700 ≤
      (LightBlockSourceRetainedProgram.factor h J+700)*(downsetCap (J*(512*h)) cut+1) := by
    have hm := Nat.mul_le_mul_left 700 hc
    nlinarith
  have h20 : 20 ≤ (LightBlockSourceRetainedProgram.factor h J+720)*
      (downsetCap (J*(512*h)) cut+1) := by
    have hm := Nat.mul_le_mul_left (LightBlockSourceRetainedProgram.factor h J+720) hc
    omega
  unfold LightBlockSourceBatch.time LightBlockSourceBatchStep.time
  calc
    _ ≤ count*((LightBlockSourceRetainedProgram.factor h J+700)*
        (downsetCap (J*(512*h)) cut+1))+20 :=
      Nat.add_le_add_right (Nat.mul_le_mul_left count (by simpa only [Nat.add_assoc] using hb)) 20
    _ ≤ count*((LightBlockSourceRetainedProgram.factor h J+720)*
        (downsetCap (J*(512*h)) cut+1))+
        (LightBlockSourceRetainedProgram.factor h J+720)*(downsetCap (J*(512*h)) cut+1) :=
      Nat.add_le_add (Nat.mul_le_mul_left count (Nat.mul_le_mul_right _ (by omega))) h20
    _ = _ := by ring

end ThreeSum.LightBlockSourceBatchProgram
