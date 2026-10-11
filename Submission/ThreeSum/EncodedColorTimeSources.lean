import Submission.ThreeSum.EncodedColorTimeScales

/-! # Running time of the executed occurrence-shared source banks -/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources CostLedger

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

noncomputable section

theorem retained_factor_powerBound :
    PowerBound (fun n => LightBlockSourceRetainedProgram.factor (half n) (blocks n)) 0 := by
  have hw := sum_zero width_powerBound (PowerBound.const 1)
  have hj := sum_zero blocks_powerBound (PowerBound.const 1)
  have hl := sum_zero local_width_powerBound (PowerBound.const 1)
  have hp := sum_zero local_product_log_powerBound (PowerBound.const 1)
  have he := sum_zero endpoint_log_powerBound (PowerBound.const 1)
  have h1 := product_zero (PowerBound.const 1200) (power_zero hw 2)
  have h2 := product_zero (product_zero (PowerBound.const 300) hj) hl
  have h3 := product_zero (PowerBound.const 600) hw
  have h4a := product_zero (PowerBound.const 300) (power_zero hw 2)
  have h4b := sum_zero (sum_zero (product_zero (PowerBound.const 150) local_width_powerBound)
    (product_zero (PowerBound.const 464) hp)) (PowerBound.const 250)
  have h4 := sum_zero (sum_zero h4a (product_zero blocks_powerBound h4b)) (PowerBound.const 400)
  have h5 := product_zero (PowerBound.const 314) he
  have h6 := product_zero (PowerBound.const 12000) (power_zero hw 4)
  simpa only [LightBlockSourceRetainedProgram.factor,width] using
    sum_zero (sum_zero (sum_zero (sum_zero (sum_zero (sum_zero h1 h2) h3) h4) h5) h6)
      (PowerBound.const 1122)

theorem catalog_factor_powerBound :
    PowerBound (fun n => LightBlockSourceCatalogProgram.factor (half n) (blocks n)) 0 := by
  have hj := sum_zero blocks_powerBound (PowerBound.const 1)
  have hr := sum_zero occurrence_log_powerBound (PowerBound.const 2)
  exact sum_zero (sum_zero retained_factor_powerBound (PowerBound.const 1120))
    (product_zero (product_zero (PowerBound.const 300) hj) hr)

theorem controls_factor_powerBound :
    PowerBound (fun n => SourceControlCosts.factor (half n) (blocks n)) 0 := by
  have hw := sum_zero width_powerBound (PowerBound.const 1)
  have h1 := product_zero (PowerBound.const 1400) (power_zero hw 2)
  have h2 := product_zero (PowerBound.const 20) blocks_powerBound
  have h3 := product_zero (PowerBound.const 14) local_product_log_powerBound
  have h4 := product_zero (PowerBound.const 14) endpoint_log_powerBound
  simpa only [SourceControlCosts.factor,width] using
    sum_zero (sum_zero (sum_zero (sum_zero h1 h2) h3) h4) (PowerBound.const 2044)

theorem source_factor_powerBound (k : ℕ) :
    PowerBound (fun n =>
      LightBlockSourceCatalogProgram.factor (half n) (blocks n)*(256*mu n+2)+
        2032*(Nat.log 2 (n^k+1)+Nat.log 2 (maxMod n+radix n+1)+1)+
        SourceControlCosts.factor (half n) (blocks n)+5705) 0 := by
  have hc := sum_zero (product_zero (PowerBound.const 256) mu_powerBound) (PowerBound.const 2)
  have hb := sum_zero (sum_zero (input_log_powerBound k) moduli_log_powerBound) (PowerBound.const 1)
  exact sum_zero (sum_zero (sum_zero (product_zero catalog_factor_powerBound hc)
    (product_zero (PowerBound.const 2032) hb)) controls_factor_powerBound) (PowerBound.const 5705)

theorem source_time_powerBound (k : ℕ) :
    PowerBound (fun n => SourceFiniteCosts.time n (maxMod n) (n^k) (radix n))
      (1+epsilon*(E-bandShift)) := by
  have he : (0 : ℝ) ≤ 1+epsilon*(E-bandShift) := by
    have h := E_bounds.1
    unfold epsilon bandShift
    linarith
  have hh := (source_factor_powerBound k).mul encoder_powerBound
  simp only [zero_add] at hh
  exact hh.add_same ((PowerBound.const 4859).mono_exponent he)

theorem sources_time_powerBound (k : ℕ) :
    PowerBound (fun n => EncodedColorSourcesCosts.time n (maxMod n) (n^k) (radix n))
      (1+epsilon*(E-bandShift)) := by
  have he : (0 : ℝ) ≤ 1+epsilon*(E-bandShift) := by
    have h := E_bounds.1
    unfold epsilon bandShift
    linarith
  have hJ := (product_zero (PowerBound.const 20) blocks_powerBound).mono_exponent he
  have hh := ((source_time_powerBound k).add_same hJ).add_same
    ((PowerBound.const 1020).mono_exponent he)
  simpa only [EncodedColorSourcesCosts.time_eq,blocks] using hh

theorem sources_time_certificate (k : ℕ) :
    PowerBound (fun n => EncodedColorSourcesCosts.time n (maxMod n) (n^k) (radix n))
      certificateExponent :=
  (sources_time_powerBound k).mono_exponent (all_costs_le_certificate _ (by simp [costLedger]))

end
end ThreeSum.EncodedColorTime
