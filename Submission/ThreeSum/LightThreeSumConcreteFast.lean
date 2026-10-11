import Submission.ThreeSum.LightThreeSumColor
import Submission.ThreeSum.ThreeSumFastResourcesDriverHost
import Submission.ThreeSum.ThreeSumColorDriverCosts

/-!
# The concrete537-procedure fast solver

The actual selected-color executable supplies the color law of the closed
driver. The parameter header is built once, followed by one reusable color
row and the reusable selected-color allocation.
-/

namespace ThreeSum.LightThreeSumConcreteFast

open Light Scales StageBounds ThreeSumWantedHostConditions SharedTraversalCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 16000

def program : Program :=
  LightThreeSumFastDriver.program LightThreeSumColor.program 509

def need : ℕ→ℕ→Need := ThreeSumFastResourcesDriver.need

def time (k n : ℕ) : ℕ :=
  LightThreeSumFastDriver.time (colorBudget k n) n

theorem program_length : program.length=537 := by
  rw [program,LightThreeSumFastDriver.program_length,LightThreeSumColor.program_length]

/-- Every color call is the verified concrete510 executable, including its
    original-input witness equivalence and preservation of the input prefix. -/
theorem color_law {lim : Limits} {src n params row k : ℕ} (x : Fin n→ℤ)
    (hn : Ready k n) (hsrc : src+n≤row+6) (hparams : params+19≤row+6)
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    LightThreeSumColorDriver.ColorLaw lim LightThreeSumColor.program 509
      ThreeSumFastResourcesColor.need src n params row (n^k) (colorBudget k n) x := by
  intro color ν dd hok hread hparameters hcolor
  apply (LightThreeSumColor.program_meets color x hn hsrc hparams le_rfl hok
    hread hx hparameters hcolor).mono le_rfl
  intro r ξ H
  exact ⟨H.1,H.2.1,fun a ha => H.2.2 a (by omega)⟩

/-- The full concrete driver returns exactly the original distinct-zero-sum
    decision whenever the proved uniform size conditions hold. -/
theorem program_meets {lim : Limits} {src n free k d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hn : Ready k n) (H : (need n (n^k)).Ok lim free d)
    (hsrc : src+n≤free) (hinput : Seg μ src (List.ofFn x))
    (hx : ∀ i, |x i|≤((n^k : ℕ) : ℤ)) :
    Meets lim program 536 d [src,n,free] μ (time k n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) := by
  apply ThreeSumFastResourcesDriver.program_meets_510 x μ LightThreeSumColor.program_length
    H hsrc hinput
  apply color_law x hn _ _ hx
  · unfold LightThreeSumFastDriver.row
    omega
  · unfold LightThreeSumFastDriver.row
    omega

noncomputable section

theorem poly_need : Light.PolyNeed need := ThreeSumFastResourcesDriver.poly_need

theorem time_powerBound (k : ℕ) : PowerBound (time k) Parameters.certificateExponent :=
  ThreeSumColorDriverCosts.time_certificate (color_budget_powerBound k)

theorem time_eventually_target (k : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop, (time k n : ℝ)≤(n : ℝ)^Parameters.targetExponent :=
  ThreeSumColorDriverCosts.time_eventually_target (color_budget_powerBound k)

theorem time_endStatementBigO (k : ℕ) :
    EndStatement.BigO (time k) (981/500 : Rat) :=
  ThreeSumColorDriverCosts.time_endStatementBigO (color_budget_powerBound k)

end
end ThreeSum.LightThreeSumConcreteFast
