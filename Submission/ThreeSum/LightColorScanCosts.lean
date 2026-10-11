import Submission.ThreeSum.LightColorScanHost

/-! # The finite color scan preserves a per-color power bound -/

namespace ThreeSum.LightColorScanCosts

open ColorParameters LightColorParametersCosts StageBounds

noncomputable section

theorem time_powerBound {T : ℕ → ℕ} {a : ℝ} (hT : PowerBound T a) (ha : 0 ≤ a) :
    PowerBound (fun n => LightColorScanHost.time (T n) n) a := by
  have h100 : PowerBound (fun n => 100*count (width n)) 0 := by
    simpa only [zero_add] using (PowerBound.const 100).mul count_powerBound
  have hround : PowerBound (fun n => 100*count (width n)+T n+3000) a :=
    ((h100.mono_exponent ha).add_same hT).add_same ((PowerBound.const 3000).mono_exponent ha)
  have hmul : PowerBound (fun n => count (width n)*(100*count (width n)+T n+3000)) a := by
    simpa only [zero_add] using count_powerBound.mul hround
  change PowerBound (fun n => count (width n)*(100*count (width n)+T n+3000)+100+100) a
  exact (hmul.add_same ((PowerBound.const 100).mono_exponent ha)).add_same
    ((PowerBound.const 100).mono_exponent ha)

def depthOverhead (n : ℕ) : ℕ := count (width n)+4

theorem depthOverhead_powerBound : PowerBound depthOverhead 0 :=
  count_powerBound.add_same (PowerBound.const 4)

end
end ThreeSum.LightColorScanCosts
