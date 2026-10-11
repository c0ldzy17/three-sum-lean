import Submission.ThreeSum.LightReportingWantedDispatchStored
import Submission.ThreeSum.ReportingHostWantedConsumerScanData
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedMassStored

/-!
# Execute the complete original physical wanted array

The invariant preserves the initial physical wanted order, all original
source data and all fixed dense metadata. The mutable counter is exactly
the mass of the ascending executed prefix until the first successful call.
-/

namespace ThreeSum.LightReportingWantedScanStored

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedConsumerData SharedReportingBankResourceBounds SharedTraversalCosts

set_option maxHeartbeats 3200000
set_option maxRecDepth 22000
set_option linter.unusedSectionVars false

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ))
    (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hg : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (half n) (blocks n))
    (hthreshold : threshold n A B C hsA hsB hsC≤9*(magnitude n)^8)
    (hok : (wantedScanNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d) :
    Meets lim LightReportingWantedScan.program 152 d
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (count n A B C hsA hsB hsC)) μ (scanTime H.encoded)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ LightReportingWantedScan.Accepted (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)) ∧
        LightReportingWantedScan.Counter (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)
          (config free n A B C hsA hsB hsC).counter r ν ∧
        KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
          (config free n A B C hsA hsB hsC).counter 1) := by
  let cfg := config free n A B C hsA hsB hsC
  let N := count n A B C hsA hsB hsC
  let Inv := fun ν => KeptBut μ ν cfg.layoutHeader cfg.counter 1
  have hcount : N≤wantedScanCount n :=
    wanted_scan_count_le (incidence_length_le_magnitude H.encoded) (count_le_product H.encoded)
  have hspace : N+1≤lim.space := by
    have henv := wanted_scan_count_envelope n
    have hh := hok.cells
    change cfg.layoutHeader+wantedEnvelope n≤lim.space at hh
    omega
  have hD : d+N+1≤lim.depth := by
    have hh := hok.depth
    change d+(wantedEnvelope n+wantedScanCount n+4)≤lim.depth at hh
    omega
  have hstep : ∀ i<N, ∀ ν, ∀ e, e+i≤d+N+1 → Inv ν →
      ν cfg.counter=(prefixMass (mass H.encoded) i : ℤ) →
      Meets lim LightReportingWantedDispatch.program 151 e (LightReportingWantedDispatch.arguments cfg i)
        ν (stepTime H.encoded i)
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ threshold n A B C hsA hsB hsC<prefixMass (mass H.encoded) i+mass H.encoded i ∨ hit H.encoded i) ∧
          ξ cfg.counter=((prefixMass (mass H.encoded) i+mass H.encoded i : ℕ) : ℤ) ∧
          Inv ξ ∧ KeptBut ν ξ cfg.layoutHeader cfg.counter 1) := by
    intro i hi ν e he hInv hcounter
    let s : Fin (count n A B C hsA hsB hsC) := ⟨i,hi⟩
    obtain ⟨Hν,HQν⟩ := retained_of_keptBut H.encoded H.catalog hInv
    have hmeta := (initial_dense_metadata H).of_keptBut hInv
    have hindices := slot_indices H.encoded s
    have hreads := slot_reads_of_keptBut H.encoded s hInv
    have hneed : (wantedNeed n U).Ok lim cfg.layoutHeader (e+1) :=
      wanted_scan_at_depth_of_ok hcount (by omega) hok
    have hmass : labelMass n A B C hsA hsB hsC (label H.encoded s)≤3*(magnitude n)^7 := by
      rw [← mass_at H.encoded s]
      exact mass_le H.encoded i hp hg
    have hrun := LightReportingWantedDispatchStored.program_meets (d := e) Hν HQν hx (label H.encoded s)
      hi hindices.1 hindices.2 (label_position H.encoded s) (label_output H.encoded s)
      hreads.1 hreads.2 hp hg (label_key H.encoded s) hcounter hmeta.1 hmeta.2.1
      (prefix_mass_le H.encoded hi.le hp hg) hmass hthreshold hneed
    let QR := fun (r : ℤ) ξ => (r=0 ∨ r=1) ∧
      (r=1 ↔ threshold n A B C hsA hsB hsC<prefixMass (mass H.encoded) i+mass H.encoded i ∨ hit H.encoded i) ∧
      ξ cfg.counter=((prefixMass (mass H.encoded) i+mass H.encoded i : ℕ) : ℤ) ∧
      Inv ξ ∧ KeptBut ν ξ cfg.layoutHeader cfg.counter 1
    have hrun' := hrun.mono (R' := QR) le_rfl (fun r ξ hr => by
      refine ⟨hr.1,?_,?_,?_,hr.2.2.2⟩
      · simpa only [← mass_at H.encoded s,← hit_at H.encoded s,s,threshold,half,blocks] using hr.2.1
      · simpa only [← mass_at H.encoded s] using hr.2.2.1
      · exact hInv.trans hr.2.2.2)
    have ht := stepTime_at H.encoded s
    change stepTime H.encoded i = _ at ht
    rw [ht]
    exact hrun'
  have hscan := LightReportingWantedScan.program_meets (C := cfg) (mass := mass H.encoded)
    (hit := hit H.encoded) (stepTime := stepTime H.encoded) (Inv := Inv)
    (threshold := threshold n A B C hsA hsB hsC) (n := N) (N := N) (D := d+N) (d := d)
    hok.space hspace hD le_rfl le_rfl SameOn.refl H.dense.1 hstep
  exact hscan.mono le_rfl (fun r ν hr => ⟨hr.1,hr.2.1,hr.2.2.1,hr.2.2.2.2⟩)

/-- At the actual schedule the selected modulus, complete prefix magnitudes
and dense threshold need no input-dependent numeric assumptions. -/
theorem program_meets_of_radix {lim : Limits} {μ : ℕ→ℤ} {free n U d : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : ThreeSumReportingSetupData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ)) (hR : 4≤radix n)
    (hok : (wantedScanNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader d) :
    Meets lim LightReportingWantedScan.program 152 d
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC)
        (count n A B C hsA hsB hsC)) μ (scanTime H.encoded)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ LightReportingWantedScan.Accepted (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)) ∧
        LightReportingWantedScan.Counter (mass H.encoded) (hit H.encoded)
          (threshold n A B C hsA hsB hsC) (count n A B C hsA hsB hsC)
          (config free n A B C hsA hsB hsC).counter r ν ∧
        KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
          (config free n A B C hsA hsB hsC).counter 1) :=
  program_meets H hx EncodedColorPrimeReadyData.selected_pos (wanted_selected_guard hR)
    (wanted_stored_threshold_le H.encoded) hok

end ThreeSum.LightReportingWantedScanStored
