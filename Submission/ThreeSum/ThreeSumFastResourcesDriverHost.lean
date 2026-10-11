import Submission.ThreeSum.ThreeSumFastResourcesDriver
import Submission.ThreeSum.LightThreeSumFastDriver

/-! # Execute the complete fast driver from its concrete polynomial Need -/

namespace ThreeSum.ThreeSumFastResourcesDriver

open Light

set_option maxHeartbeats 1700000
set_option maxRecDepth 17000

theorem program_meets {lim : Limits} {colorProgram : Program} {pColor : ℕ}
    {src n free U colorTime d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (H : (need n U).Ok lim free d) (hsrc : src+n≤free)
    (hinput : Seg μ src (List.ofFn x))
    (hcolor : LightThreeSumColorDriver.ColorLaw lim colorProgram pColor ThreeSumFastResourcesColor.need
      src n free (LightThreeSumFastDriver.row free) U colorTime x) :
    Meets lim (LightThreeSumFastDriver.program colorProgram pColor) (colorProgram.length+26) d
      [src,n,free] μ (LightThreeSumFastDriver.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) :=
  LightThreeSumFastDriver.program_meets x μ H hsrc hinput hcolor

theorem program_length_510 {colorProgram : Program} (pColor : ℕ) (hlen : colorProgram.length=510) :
    (LightThreeSumFastDriver.program colorProgram pColor).length=537 := by
  rw [LightThreeSumFastDriver.program_length,hlen]

theorem program_meets_510 {lim : Limits} {colorProgram : Program} {pColor : ℕ}
    {src n free U colorTime d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hlen : colorProgram.length=510) (H : (need n U).Ok lim free d) (hsrc : src+n≤free)
    (hinput : Seg μ src (List.ofFn x))
    (hcolor : LightThreeSumColorDriver.ColorLaw lim colorProgram pColor ThreeSumFastResourcesColor.need
      src n free (LightThreeSumFastDriver.row free) U colorTime x) :
    Meets lim (LightThreeSumFastDriver.program colorProgram pColor) 536 d
      [src,n,free] μ (LightThreeSumFastDriver.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) := by
  simpa only [hlen] using program_meets x μ H hsrc hinput hcolor

end ThreeSum.ThreeSumFastResourcesDriver
