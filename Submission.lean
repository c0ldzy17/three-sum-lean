import Submission.EndStatement
import Submission.ThreeSum.FinalSolver

/-- Complete deterministic 3SUM bound in the trusted benchmark model. -/
theorem Race.bound :
    EndStatement.ThreeSum.SolvedInTime ((981 : Rat) / 500) := by
  exact ThreeSum.solvedInTime_981_500
