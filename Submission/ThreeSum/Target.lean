import Submission.EndStatement

/-!
# Exact benchmark goal

This is deliberately a definition of the outstanding goal, not a theorem
claiming that the component proofs already imply it.  The imported machine
definition is copied unchanged from the pinned benchmark repository.
-/

namespace ThreeSum

def fullBenchmarkGoal : Prop :=
  EndStatement.ThreeSum.SolvedInTime (981 / 500 : Rat)

end ThreeSum
