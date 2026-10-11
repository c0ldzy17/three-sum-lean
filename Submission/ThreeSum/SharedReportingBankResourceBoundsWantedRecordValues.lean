import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedAccessHost
import Submission.ThreeSum.ReportingHostWantedControls

/-! # All twenty selected reporter values fit the actual word limit -/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light BandRawA BandCandidateRows ReportingHostWantedControls
open ReportingHostSourceSelection

set_option maxHeartbeats 300000
set_option maxRecDepth 14000

theorem wanted_record_values_word {lim : Limits} {f : ℕ→ℤ}
    {n g idx pair bank cover NB NC h J cut occ code srcB srcC report stop : ℕ}
    {rs : List Record}
    (H : WantedSourceEnds
      (LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c
      code h J cut stop)
    (hstop : stop≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hav : |f (labelAt n g rs idx).position|≤lim.word)
    (ho : (labelAt n g rs idx).owner≤lim.space)
    (hb : (ownerRecord n g rs idx).b≤lim.space)
    (hc : (ownerRecord n g rs idx).c≤lim.space)
    (hcat : LightReportingWantedAccess.catalog n g rs idx report J NB NC code≤lim.space) :
    ∀ z∈ReportingHostWantedControls.record
      (ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report), |z|≤lim.word := by
  have hnat (v : ℕ) (hv : v≤lim.space) : |(v : ℤ)|≤lim.word := by
    simpa using (Int.ofNat_le.mpr hv).trans hw
  intro z hz
  simp only [ReportingHostWantedControls.record,ofAccess,List.mem_cons,List.not_mem_nil,or_false] at hz
  rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact hav
  · exact hnat _ ho
  · exact hnat _ hb
  · exact hnat _ hc
  · exact hnat _ hcat
  all_goals
    apply hnat
    exact (H.values _ (by simp [ReportingHostSourceSelection.values])).trans hstop

theorem wanted_record_values_of_allocation {lim : Limits} {f : ℕ→ℤ}
    {n g records idx pair bank cover NB NC h J cut occ code srcB srcC report stop : ℕ}
    {rs : List Record}
    (H : WantedSourceEnds
      (LightReportingWantedAccess.selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c
      code h J cut stop)
    (hidx : idx<(items n g rs).length)
    (hi : (ownerRecord n g rs idx).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs idx).c<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J)
    (hrecords : records+4*rs.length≤stop) (hsrcB : srcB+NB≤stop) (hsrcC : srcC+NC≤stop)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤stop)
    (hstop : stop≤lim.space) (hw : (lim.space : ℤ)≤lim.word)
    (hav : |f (labelAt n g rs idx).position|≤lim.word) :
    ∀ z∈ReportingHostWantedControls.record
      (ofAccess f n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report), |z|≤lim.word := by
  have ho := (at_bounds hidx).1
  have hb := hi.trans_le (BandPartition.size_le NB g)
  have hc := hj.trans_le (BandPartition.size_le NC g)
  have he := SharedReportingBankAccess.record_end (free := report) (J := J) hk hi hj
  have hf := SharedReportingBankHeader.payload_le_finish report h J NB NC g
  apply wanted_record_values_word H hstop hw hav (by omega) (by omega) (by omega)
  unfold LightReportingWantedAccess.catalog
  omega

end ThreeSum.SharedReportingBankResourceBounds
