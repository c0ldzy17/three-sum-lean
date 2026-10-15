import Submission.ThreeSum.TernaryFastProgramResources

noncomputable section
namespace ThreeSum.TernaryFastProgramBudget
open Light StageBounds ArithmeticStageBounds LightColorParametersCosts
open Filter
open scoped Topology

theorem color_count : PowerBound (fun n=>ColorParameters.count (width n)) 0 := by
  have hp := width_powerBound.pow 2
  have hh := (PowerBound.const 81).mul hp
  simpa only [ColorParameters.count,zero_mul,mul_zero,zero_add] using hh

/-- The actual finite coloring enumeration adds only a subpolynomial
factor to the running time of the included per-color program. -/
theorem scan {T : ℕ→ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 0≤a) :
    PowerBound (fun n=>LightColorScanHost.time (T n) n) a := by
  have hc := color_count
  have h100 := ((PowerBound.const 100).mul hc).mono_exponent (by simpa only [zero_add] using ha)
  have hinner := (h100.add_same hT).add_same ((PowerBound.const 3000).mono_exponent ha)
  have hmain : PowerBound
      (fun n=>ColorParameters.count (width n)*(100*ColorParameters.count (width n)+T n+3000)) a := by
    simpa only [zero_add] using hc.mul hinner
  have hh := (hmain.add_same ((PowerBound.const 100).mono_exponent ha)).add_same
    ((PowerBound.const 100).mono_exponent ha)
  simpa only [LightColorScanHost.time,LightColorScan.time] using hh

/-- All actual once-per-input setup and the complete coloring scan retain
the child's proved exponent. No caller address enters the time bound. -/
theorem full {m b p K κ : ℕ} [Fact p.Prime] (hm : 0<m) (hb : 1<b)
    {T : ℕ→ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 0≤a) :
    PowerBound (fun n=>LightTernaryFastProgramProof.time (TernaryCoverScale.outputSize m) b p K κ (T n) n) a := by
  have hg : PowerBound (TernaryGlobalPreludeTime.uniformTime (TernaryCoverScale.outputSize m) b p K κ) 0 := by
    intro δ hδ
    simpa only [zero_add] using
      TernaryGlobalPreludeTime.uniform_eventually (p:=p) (K:=K) (κ:=κ) hm hb hδ
  exact ((hg.mono_exponent ha).add_same (scan hT ha)).add_same
    ((PowerBound.const 1000).mono_exponent ha)

end ThreeSum.TernaryFastProgramBudget
