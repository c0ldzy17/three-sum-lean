import Submission.ThreeSum.LightBlockSourceRetainedProgram
import Submission.ThreeSum.BlockSourceSharing

/-!
# Charge of the actual shared-histogram source host to the encoder ledger

For each band index and occurrence vector the literal host constructs both
source families. The actual source-band and occurrence iterator is still
an outer composition obligation; this bound charges its body with the
existing exact finite counts and introduces no output-subset factor.
-/

namespace ThreeSum.BlockSourceStageCosts

open Scales TrimScales StageBounds CostLedger BlockSourceSharing

def work (n : ℕ) : ℕ :=
  bandCount n*scheduleCount n*LightBlockSourceRetainedHost.time
    (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)

theorem work_le_encoderCount (n : ℕ) :
    work n ≤ LightBlockSourceRetainedProgram.factor
      (microHalf (inputBits n)) (blockCount (inputBits n))*(256*mu n+2)*encoderCount n := by
  have hcut : mu n ≤ blockCount (inputBits n)*(512*microHalf (inputBits n)) := by
    rw [width_eq]
    omega
  have ht := LightBlockSourceRetainedProgram.time_le_factor hcut
  rw [width_eq] at ht
  have hd := downset_add_one_le_fullOutputs n
  have he : bandCount n*scheduleCount n*fullOutputs n ≤ encoderCount n := by
    calc
      _ ≤ 2*(bandCount n*scheduleCount n*fullOutputs n) :=
        Nat.le_mul_of_pos_left _ (by omega)
      _ = encoderCount n := by unfold encoderCount; ring
  unfold work
  calc
    _ ≤ bandCount n*scheduleCount n*
        (LightBlockSourceRetainedProgram.factor (microHalf (inputBits n))
          (blockCount (inputBits n))*((256*mu n+2)*fullOutputs n)) :=
      Nat.mul_le_mul_left _ (ht.trans (Nat.mul_le_mul_left _ hd))
    _ = LightBlockSourceRetainedProgram.factor (microHalf (inputBits n))
        (blockCount (inputBits n))*(256*mu n+2)*(bandCount n*scheduleCount n*fullOutputs n) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he

end ThreeSum.BlockSourceStageCosts
