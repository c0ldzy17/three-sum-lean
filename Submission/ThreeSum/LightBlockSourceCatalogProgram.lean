import Submission.ThreeSum.LightBlockSourceCatalog
import Submission.ThreeSum.LightBlockSourceBatchProgram

/-! # Literal program and finite cost of the constructed source catalog -/

namespace ThreeSum.LightBlockSourceCatalogProgram

open Light SubsetAddress LightBlockSourceCatalog

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

def program : Program := LightBlockSourceBatchProgram.program ++
  [LightSourceOccurrenceArray.body 44,LightOutputDecodeDigits.body 45,
    LightOutputDecodeDivide.body,LightBlockSourceCatalog.body 43 42]

def sourceProcs : LightBlockSourceRetainedHost.Procs program 0 :=
  ⟨1,2,3,4,5,22,rfl,rfl,rfl,rfl,
    ⟨6,12,⟨7,8,9,10,11,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,⟨14,15,16,17,rfl,rfl,rfl,⟨18,19,20,21,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,
    ⟨23,24,25,rfl,rfl,
      ⟨26,27,28,40,29,30,31,32,33,34,35,36,37,38,39,
        rfl,rfl,rfl,rfl,rfl,rfl,rfl,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl⟩,rfl⟩

def programProcs : LightBlockSourceCatalog.Procs program 46 :=
  ⟨43,44,45,42,rfl,rfl,rfl,⟨41,⟨0,sourceProcs,rfl⟩,rfl⟩,rfl⟩

theorem program_length : program.length = 47 := rfl

def factor (h J : ℕ) : ℕ :=
  LightBlockSourceRetainedProgram.factor h J+1120+
    300*(J+1)*(Nat.log 2 (count h J+1)+2)

theorem time_bound {h J cut : ℕ} (hcut : cut ≤ J*(512*h)) :
    LightBlockSourceCatalog.time h J cut ≤
      (count h J+1)*factor h J*(downsetCap (J*(512*h)) cut+1) := by
  have hb := LightBlockSourceBatchProgram.time_bound (count := count h J) hcut
  have hr := LightSourceOccurrenceArray.time_bound (count h J) J
  have hr' : LightSourceOccurrenceArray.time (count h J) J ≤
      (count h J+1)*(300*(J+1)*(Nat.log 2 (count h J+1)+2))*
        (downsetCap (J*(512*h)) cut+1) := by
    calc
      _ ≤ (count h J+1)*(300*(J+1)*(Nat.log 2 (count h J+1)+2)) := by
        simpa only [mul_assoc,mul_comm,mul_left_comm] using hr
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  have hconst : 400 ≤ (count h J+1)*400*(downsetCap (J*(512*h)) cut+1) := by
    calc
      _ ≤ (count h J+1)*400 := by omega
      _ ≤ _ := Nat.le_mul_of_pos_right _ (by omega)
  unfold LightBlockSourceCatalog.time
  calc
    _ ≤ (count h J+1)*(300*(J+1)*(Nat.log 2 (count h J+1)+2))*
          (downsetCap (J*(512*h)) cut+1)+
        (count h J+1)*(LightBlockSourceRetainedProgram.factor h J+720)*
          (downsetCap (J*(512*h)) cut+1)+
        (count h J+1)*400*(downsetCap (J*(512*h)) cut+1) :=
      Nat.add_le_add (Nat.add_le_add hr' hb) hconst
    _ = _ := by unfold factor; ring

end ThreeSum.LightBlockSourceCatalogProgram
