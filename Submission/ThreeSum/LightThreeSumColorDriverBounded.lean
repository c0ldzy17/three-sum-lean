import Submission.ThreeSum.ThreeSumColorDriverResources

/-! # Run the closed color scan from actual input and parameter arrays -/

namespace ThreeSum.LightThreeSumColorDriver

open Light ColorParameters LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 14000

def ColorLaw (lim : Limits) (colorProgram : Program) (pColor : ℕ)
    (colorNeed : ℕ→ℕ→Need) (src n params row U colorTime : ℕ) (x : Fin n→ℤ) : Prop :=
  ∀ (color : Coloring.Parameter (width n)) (ν : ℕ→ℤ) (dd : ℕ),
    (colorNeed n U).Ok lim (row+6) dd →
    Seg ν src (List.ofFn x) → Seg ν params (LightParameterInit.values n) →
    Seg ν row (fields color) →
    Meets lim colorProgram pColor dd [src,n,params,row,row+6] ν colorTime
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ ColorClassLists.witness color x) ∧ Kept ν ξ row)

theorem parameter_values_length (n : ℕ) : (LightParameterInit.values n).length=19 := rfl

theorem program_meets_bounded {lim : Limits} {colorProgram : Program} {pColor : ℕ}
    {colorNeed : ℕ→ℕ→Need} {src n params row U colorTime d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (H : (ThreeSumColorDriverResources.need colorNeed n U).Ok lim row d)
    (hsrc : src+n≤row) (hparams : params+19≤row)
    (hinput : Seg μ src (List.ofFn x)) (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : ColorLaw lim colorProgram pColor colorNeed src n params row U colorTime x) :
    Meets lim (program colorProgram pColor) (colorProgram.length+3) d
      [src,n,params,row] μ (LightColorScanHost.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ row) := by
  obtain ⟨hs,hw,hd⟩ := ThreeSumColorDriverResources.scan_bounds_of_ok H
  apply program_meets x μ H.space hs (by omega) (by omega) hw hd
    (LightColorScanHost.parameters_bits hparameters)
  intro i hi ν hkeep hrow dd hdepth
  exact hcolor (parameter hi) ν dd (ThreeSumColorDriverResources.color_of_ok H hdepth)
    (hinput.of_kept hkeep (by simpa only [List.length_ofFn] using hsrc))
    (hparameters.of_kept hkeep (by simpa only [parameter_values_length] using hparams)) hrow

end ThreeSum.LightThreeSumColorDriver
