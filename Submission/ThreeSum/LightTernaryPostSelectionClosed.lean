import Submission.ThreeSum.LightTernaryPostSelection

/-! Both final callers have fixed program text; compact counts and all input
and workspace pointers are runtime data, including zero-initialized counts. -/
noncomputable section
set_option maxRecDepth 24000
set_option maxHeartbeats 1000000
namespace ThreeSum.LightTernaryCompactReporter
open Light TernaryMomentSchedule

def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  LightTernaryMomentReporter.closedProgram xl yl zl xr yr zr H++
    [body (127*(channels (2*H+1)).length+6)]

theorem program_eq_closed {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H = closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by
  unfold program closedProgram
  rw [LightTernaryMomentReporter.program_eq_closed,LightTernaryMomentReporter.driver_length]

end ThreeSum.LightTernaryCompactReporter

namespace ThreeSum.LightTernaryPostSelection
open Light TernaryMomentSchedule

def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightOriginalSurvivorPair.program
    (LightTernaryCompactReporter.closedProgram xl yl zl xr yr zr H)++
      [body (9+(127*(channels (2*H+1)).length+7))]

theorem program_eq_closed {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H = closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by
  unfold program libraries closedProgram
  rw [LightTernaryCompactReporter.program_eq_closed,LightTernaryMomentReporter.program_length]

@[simp] theorem libraries_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    (libraries S H).length = 127*(channels (2*H+1)).length+17 := by
  have hp : LightOriginalSurvivorPair.program.length = 9 := rfl
  simp [libraries,ReportingHostRelocation.program,LightTernaryCompactReporter.program,hp] <;> omega

@[simp] theorem program_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    (program S H).length = 127*(channels (2*H+1)).length+18 := by
  simp [program]

@[simp] theorem args_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (c : LightOriginalSurvivorPair.Layout) (scratch matrix : ℕ) :
    (args S c scratch matrix).length = 148 := rfl

/-- Every compact count in the input frame is a literal zero; the program
loads its actual values only after the original-source cleanup has run. -/
theorem input_counts_zero {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (c : LightOriginalSurvivorPair.Layout) (scratch matrix : ℕ) :
    (args S c scratch matrix).getD 34 0 = 0 ∧
    (args S c scratch matrix).getD 36 0 = 0 ∧
    (args S c scratch matrix).getD 53 0 = 0 ∧
    (args S c scratch matrix).getD 76 0 = 0 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

theorem time_bound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ → ℕ) :
    time S H c keysB keysC ≤ LightTernaryMomentReporter.time S H+280*(c.nB+c.nC)+2440+
      ((TernaryOriginalCollisions.collisionPairs (fun i : Fin c.nB => keysB i.val)).card+
       (TernaryOriginalCollisions.collisionPairs (fun i : Fin c.nC => keysC i.val)).card)*
        (c.nA*(120*c.L+330)+300) := by
  have ht := LightOriginalSurvivorPair.time_bound keysB keysC c.nA c.nB c.nC c.L
  unfold time LightTernaryCompactReporter.time
  omega

end ThreeSum.LightTernaryPostSelection
