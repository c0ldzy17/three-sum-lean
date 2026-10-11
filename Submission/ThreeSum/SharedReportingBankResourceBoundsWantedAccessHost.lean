import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedAccess

/-! # Individual selector bounds from the proved wanted Need -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds ReportingHostWantedLayout
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000

theorem WantedSourceEnds.fits {X : Pointers}
    {pair bank cover srcB srcC i j code h J cut stop out limit : ℕ}
    (H : WantedSourceEnds X pair bank cover srcB srcC i j code h J cut stop)
    (hs : stop≤limit) (hout : out+15≤limit) (hscalar : J+X.bankSpan+20≤limit) :
    ReportingHostSourceSelection.Fits X pair bank cover srcB srcC i j code J out limit := by
  refine ⟨H.pairHeader.trans hs,H.bankHeader.trans hs,H.coverHeader.trans hs,hout,
    H.leftHead.trans hs,H.rightHead.trans hs,H.leftCell.trans hs,H.rightCell.trans hs,
    ?_,hscalar,fun v hv => (H.values v hv).trans hs⟩
  exact (Nat.le_add_right _ _).trans (H.occurrence.trans hs)

theorem wanted_selector_scalars_le (n : ℕ) :
    blocks n+SourceBandBankLayout.span (half n) (blocks n) (LightBlockQuery.sourceCut (half n) (blocks n))+20≤
      wantedEnvelope n := by
  have hs := source_span_le_magnitude n
  have hj := (components n).blocksBound
  have hm : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  have h3 : (magnitude n+1)^3≤(magnitude n+1)^10 := Nat.pow_le_pow_right (by omega) (by decide)
  have h1 : 1≤(magnitude n+1)^10 := Nat.one_le_pow _ _ (by omega)
  unfold wantedEnvelope LightBlockQuery.sourceCut
  omega

theorem wanted_record_scalars_le {n K : ℕ} (hK : K≤blocks n) :
    blocks n+512*half n+K+BlockSourceEncoding.modulus (half n) (blocks n)+
      LightBlockQuery.sourceCut (half n) (blocks n)+localPrime (half n)+localBucketCap (half n)+1024≤
      wantedEnvelope n := by
  have H := components n
  have hj := H.blocksBound
  have hL := H.localWidthBound
  have hp := H.prime
  have hc := wanted_cap_le_magnitude n
  have hm := wanted_modulus_le_magnitude n
  have hcut := (primitive_bounds n).2.2.1
  have hlin := linear_le_magnitude n
  have hM : magnitude n≤(magnitude n+1)^10 :=
    (Nat.le_succ _).trans (Nat.le_self_pow (by decide) _)
  unfold wantedEnvelope LightBlockQuery.sourceCut
  omega

theorem wanted_access_output_le {lim : Limits} {dst n U K N NB NC d : ℕ}
    (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostWantedLayout.access dst (blocks n)+20≤lim.space := by
  have H := wanted_buffers_of_ok hK hN hB hC hok
  have hw := H.numeric
  have he := wanted_work_eq dst (half n) (blocks n) K N NB NC
  have hf := wanted_work_formula (half n) (blocks n) K N NB NC
  unfold ReportingHostWantedLayout.access decoded
  omega

theorem wanted_source_fits_of_ok {lim : Limits}
    {pair bank cover srcB srcC NB NC n U occ i j code stop dst out d : ℕ}
    (H : WantedSourceEnds
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) stop)
    (hstop : stop≤dst) (hout : out+15≤lim.space)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostSourceSelection.Fits
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (blocks n) out lim.space := by
  have he := hok.cells
  have hs : wantedEnvelope n≤lim.space := by change dst+wantedEnvelope n≤lim.space at he; omega
  exact H.fits (by omega) hout ((wanted_selector_scalars_le n).trans hs)

theorem wanted_access_fits_of_ok {lim : Limits}
    {pair bank cover srcB srcC NB NC n U K N occ i j code stop dst d : ℕ}
    (H : WantedSourceEnds
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) stop)
    (hstop : stop≤dst) (hK : K≤blocks n) (hN : N≤3*(magnitude n)^3) (hB : NB≤n) (hC : NC≤n)
    (hok : (wantedNeed n U).Ok lim dst d) :
    ReportingHostSourceSelection.Fits
      (retained pair bank cover NB NC (BandScales.bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ i j code)
      pair bank cover srcB srcC i j code (blocks n)
      (ReportingHostWantedLayout.access dst (blocks n)+5) lim.space :=
  wanted_source_fits_of_ok H hstop (by have hh := wanted_access_output_le hK hN hB hC hok; omega) hok

end ThreeSum.SharedReportingBankResourceBounds
