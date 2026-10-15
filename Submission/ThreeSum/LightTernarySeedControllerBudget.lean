import Submission.ThreeSum.LightTernarySeedController

namespace ThreeSum.LightTernarySeedControllerBudget

/-- The actual menu scan pays for all n seed evaluations and at most one
additional selected-seed reconstruction and span extension. -/
theorem time_bound (n seedTime spanTime : ℕ) :
    LightTernarySeedController.time n seedTime spanTime≤
      (n+1)*(seedTime+spanTime+2000) := by
  unfold LightTernarySeedController.time LightTernaryRowSelector.time
  nlinarith

end ThreeSum.LightTernarySeedControllerBudget
