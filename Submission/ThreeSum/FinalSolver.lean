import Submission.ThreeSum.LightThreeSumHybrid
import Submission.ThreeSum.ThreeSumHybridEndBridge
import Submission.ThreeSum.Target

/-!
# The complete 3SUM solver at exponent 981/500

For each fixed magnitude exponent, the actual hybrid executable handles
the finite exceptional sizes and arbitrary supplied magnitude bounds.
Its proved polynomial resource requirement permits the existing compiler
realization, and its exact running time satisfies the rational end statement.
-/

namespace ThreeSum

theorem solvedInTime_981_500 :
    EndStatement.ThreeSum.SolvedInTime (981/500 : Rat) := by
  apply ThreeSumHybridEndBridge.endStatement_of_solvers
  intro κ
  exact ⟨ThreeSumWantedHostConditions.cutoff κ,LightThreeSumHybrid.program κ,542,
    LightThreeSumHybrid.need κ,LightThreeSumHybrid.solves κ,LightThreeSumHybrid.poly_need κ⟩

theorem fullBenchmarkGoal_proved : ThreeSum.fullBenchmarkGoal :=
  solvedInTime_981_500

end ThreeSum
