import Submission.ThreeSum.TernaryParameters

/-!
# Quantitative budget for a fixed-depth scalar-score construction

This certificate explicitly pays a representation-cap loss at every prime
selection step and a conservative fourth power of the prime-window size.
These are numerical inequalities.  The corresponding executable and its
cost contracts must still be supplied before applying the end bridge.
-/

noncomputable section
namespace ThreeSum.TernaryShortLedger

open ThreeSum.TernaryParameters

def chainDepth : ℕ := 100000
def representationExponent : ℝ := 1 / 10000000000
def radixExponent : ℝ := 1 + partitionEntropy / Hpi
def polynomialReserve : ℝ := 1 / 10000
def scoreOverhead : ℝ :=
  representationExponent * (chainDepth + 1) +
    4 * radixExponent / chainDepth + polynomialReserve
def shortCertificate : ℝ := 19205 / 10000

theorem radixExponent_bounds : 1 < radixExponent ∧ radixExponent < 313 / 250 := by
  have hp := Hpi_pos
  have hg := partitionEntropy_bounds
  have hh := Hpi_bounds
  constructor
  · unfold radixExponent
    have hq : 0 < partitionEntropy / Hpi := div_pos (by linarith) hp
    linarith
  · unfold radixExponent
    have hq : partitionEntropy / Hpi < (63 / 250 : ℝ) := by
      apply (div_lt_iff₀ hp).mpr
      linarith [hh.1, hg.2]
    linarith

theorem paid_representation_loss :
    representationExponent * (chainDepth + 1) = (100001 / 10000000000 : ℝ) := by
  norm_num [representationExponent, chainDepth]

theorem scoreOverhead_bound : scoreOverhead < (161 / 1000000 : ℝ) := by
  have hr := radixExponent_bounds.2
  unfold scoreOverhead chainDepth representationExponent polynomialReserve
  norm_num
  linarith

theorem all_costs_with_overhead_lt_shortCertificate :
    ∀ t ∈ costLedger, t + scoreOverhead < shortCertificate := by
  intro t ht
  have hcost := all_costs_lt_certificate t ht
  have hover := scoreOverhead_bound
  dsimp [certificateExponent, shortCertificate] at *
  linarith

theorem shortCertificate_lt_target : shortCertificate < targetExponent := by
  norm_num [shortCertificate, targetExponent]

theorem all_costs_with_overhead_lt_target :
    ∀ t ∈ costLedger, t + scoreOverhead < targetExponent := by
  intro t ht
  exact (all_costs_with_overhead_lt_shortCertificate t ht).trans shortCertificate_lt_target

end ThreeSum.TernaryShortLedger
