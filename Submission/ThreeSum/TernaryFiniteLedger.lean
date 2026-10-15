import Submission.ThreeSum.TernaryEntropyRates
import Submission.ThreeSum.TernaryDimensionBounds

/-! Finite principal dimension charges from actual typed tables and prime.
No program runtime contract is inferred from this dimension certificate. -/
noncomputable section
namespace ThreeSum.TernaryFiniteLedger
open Filter Real TernaryParameters TernaryEntropyRates TernaryCoverScale
open scoped Topology

def bankCharge (m : ℕ) : ℝ := 2*bankEntropy/outputRate m
def queryCharge (m : ℕ) : ℝ := 1+2*(outputRate m-primeRate m+queryEntropy)/outputRate m
def endpointCharge (m : ℕ) : ℝ := 2*endpointRate m/outputRate m
def histogramCharge (m : ℕ) : ℝ := 2*primeRate m/outputRate m
def incidenceCharge (m : ℕ) : ℝ := 1+2*(outputRate m-primeRate m)/outputRate m

theorem bank_charge_tendsto :
    Tendsto bankCharge atTop (𝓝 (2*bankEntropy/Hpi)) :=
  tendsto_const_nhds.div actual_output_rate Hpi_pos.ne'

theorem query_charge_tendsto :
    Tendsto queryCharge atTop (𝓝 (2-partitionEntropy/Hpi+2*queryEntropy/Hpi)) := by
  have h := (((actual_output_rate.sub actual_prime_rate).add_const queryEntropy).const_mul 2).div
    actual_output_rate Hpi_pos.ne'
  have hh := h.const_add 1
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne']
    ring

theorem endpoint_charge_tendsto :
    Tendsto endpointCharge atTop (𝓝 (2*Halpha/Hpi)) :=
  (actual_endpoint_rate.const_mul 2).div actual_output_rate Hpi_pos.ne'

theorem histogram_charge_tendsto :
    Tendsto histogramCharge atTop (𝓝 (1+partitionEntropy/Hpi)) := by
  have h := (actual_prime_rate.const_mul 2).div actual_output_rate Hpi_pos.ne'
  convert h using 1
  · rfl
  · field_simp [Hpi_pos.ne']

theorem incidence_charge_tendsto :
    Tendsto incidenceCharge atTop (𝓝 (2-partitionEntropy/Hpi)) := by
  have h := ((actual_output_rate.sub actual_prime_rate).const_mul 2).div
    actual_output_rate Hpi_pos.ne'
  have hh := h.const_add 1
  convert hh using 1
  · rfl
  · field_simp [Hpi_pos.ne']
    ring

def GoodBlock (m : ℕ) : Prop :=
  0 < m ∧ bankCharge m<certificateExponent ∧ queryCharge m<certificateExponent ∧
    endpointCharge m<certificateExponent ∧ histogramCharge m<certificateExponent ∧
    incidenceCharge m<certificateExponent

theorem goodBlock_eventually : ∀ᶠ m : ℕ in atTop, GoodBlock m := by
  have h := ledger_individual_bounds
  filter_upwards [eventually_gt_atTop (0 : ℕ),
    bank_charge_tendsto.eventually (gt_mem_nhds h.1),
    query_charge_tendsto.eventually (gt_mem_nhds h.2.1),
    endpoint_charge_tendsto.eventually (gt_mem_nhds h.2.2.1),
    histogram_charge_tendsto.eventually (gt_mem_nhds h.2.2.2.1),
    incidence_charge_tendsto.eventually (gt_mem_nhds h.2.2.2.2)] with m hm hB hQ hA hP hI
  exact ⟨hm,hB,hQ,hA,hP,hI⟩

theorem positive_slopes_eventually :
    ∀ᶠ m : ℕ in atTop, 0 < outputRate m ∧ primeRate m < outputRate m := by
  have hh := actual_output_rate.eventually (lt_mem_nhds Hpi_pos)
  have hlim : 0 < Hpi-(Hpi+partitionEntropy)/2 := by
    linarith [analytic_admissibility.2.2.1]
  have hs := (actual_output_rate.sub actual_prime_rate).eventually (lt_mem_nhds hlim)
  filter_upwards [hh,hs] with m hm hs
  exact ⟨hm,by linarith⟩

theorem scale_ge_coefficient (C c d : ℕ) : c ≤ scale C c d := by
  have hc : c ≤ scaleAux C c d := by unfold scaleAux; omega
  have ht : scaleAux C c d ≤ 2*scaleAux C c d := by omega
  have hp : 2*scaleAux C c d ≤ 2^(2*scaleAux C c d) :=
    (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))).le
  exact hc.trans (ht.trans hp)

/-- One exact fixed block satisfies the actual finite ledger and the
representation cap. Enlarging the carry envelope selects arbitrarily large
members of the already verified explicit scale family. -/
theorem simultaneous_fixed_block (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) := by
  obtain ⟨N,hN⟩ := eventually_atTop.mp goodBlock_eventually
  refine ⟨max c N,le_max_left _ _,hN _ ?_⟩
  exact (le_max_right c N).trans (scale_ge_coefficient _ _ _)

theorem simultaneous_fixed_cost_block (C c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale C c' d) ∧
      0 < outputRate (scale C c' d) ∧ primeRate (scale C c' d) < outputRate (scale C c' d) := by
  have hgood : ∀ᶠ m : ℕ in atTop, GoodBlock m ∧ 0 < outputRate m ∧ primeRate m < outputRate m := by
    filter_upwards [goodBlock_eventually,positive_slopes_eventually] with m hg hp
    exact ⟨hg,hp⟩
  obtain ⟨N,hN⟩ := eventually_atTop.mp hgood
  refine ⟨max c N,le_max_left _ _,hN _ ?_⟩
  exact (le_max_right c N).trans (scale_ge_coefficient _ _ _)

theorem simultaneous_representation_and_ledger (c d : ℕ) :
    ∃ c' : ℕ, c ≤ c' ∧ GoodBlock (scale 40000000000 c' d) ∧
      ∀ᶠ n : ℕ in atTop,
        ((localFactor 40000000000 c' d)^
          (radixLength (scale 40000000000 c' d) n) : ℝ) ≤
            (n : ℝ)^(1/10000000000 : ℝ) := by
  obtain ⟨c',hc',hg⟩ := simultaneous_fixed_block 40000000000 c d
  exact ⟨c',hc',hg,fixed_representation_eventually c' d⟩

end ThreeSum.TernaryFiniteLedger
