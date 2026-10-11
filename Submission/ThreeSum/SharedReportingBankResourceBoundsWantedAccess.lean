import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedHost
import Submission.ThreeSum.ReportingHostSourceSelectionStored

/-!
# Every selected persistent row remains before the counter

The bounds keep the selected B and C bands independent. Each incidence and
occurrence is selected by its retained physical label, and every translated
pointer is bounded individually by the already occupied prefix.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 2800000
set_option maxRecDepth 15000

theorem wanted_band_row_ends {base n g m i : ℕ} (hi : i<BandPartition.size n g) :
    base+6*i+6≤SourceBandLayout.work base n g m ∧
    SourceBandLayout.offsets base n g m i+m+1≤SourceBandLayout.work base n g m ∧
    SourceBandLayout.flat base n g m i+SourceBandLayout.len n g i≤SourceBandLayout.work base n g m := by
  have hh := SourceBandLayout.header_end (base := base) (m := m) hi
  have hf := SourceBandLayout.flat_end_le_work (base := base) (m := m) hi
  have hl := SourceBandLayout.len_le_cap n g i
  refine ⟨?_,?_,(Nat.add_le_add_left hl _).trans hf⟩
  · unfold SourceBandLayout.flat SourceBandLayout.cursor SourceBandLayout.offsets SourceBandLayout.codes at hf
    omega
  · unfold SourceBandLayout.flat SourceBandLayout.cursor at hf
    omega

theorem wanted_cover_ends (cover h J : ℕ) :
    cover+20≤LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.scheduleMaps (LightLocalCoverInit.base cover) h+2*(512*h)*scheduleSize h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.candidates (LightLocalCoverInit.base cover) h+scheduleSize h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.hist0 (LightLocalCoverInit.base cover) h+LightLocalCoverSchedule.rows h*localPrime h≤
      LightCoverKeyData.keyEnd cover h J ∧
    LightLocalCoverLayout.hist1 (LightLocalCoverInit.base cover) h+LightLocalCoverSchedule.rows h*localPrime h≤
      LightCoverKeyData.keyEnd cover h J := by
  have hb := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base cover) h
  have ht := LightLocalCoverRetention.table_ends_le (LightLocalCoverInit.base cover) h
  have he := LightCoverKeyData.afterCover_le_keyEnd cover h J
  change LightLocalCoverMetadata.nextFree (LightLocalCoverInit.base cover) h≤_ at he
  refine ⟨hb.trans he,?_,ht.2.2.2.2.trans he,ht.2.1.trans he,ht.2.2.1.trans he⟩
  simpa only [LightLocalCoverMetadata.nextFree,Nat.mul_comm] using he

structure WantedSourceEnds (X : Pointers) (pair bank cover srcB srcC i j code h J cut stop : ℕ) : Prop where
  pairHeader : pair+3≤stop
  bankHeader : bank+5≤stop
  coverHeader : cover+16≤stop
  leftHead : ReportingHostSourceSelection.leftHead X i+6≤stop
  rightHead : ReportingHostSourceSelection.rightHead X j+6≤stop
  leftCell : leftStageCell X i code+1≤stop
  rightCell : rightStageCell X j code+1≤stop
  sourceL : srcB+X.startL+X.sizeL≤stop
  sourceR : srcC+X.startR+X.sizeR≤stop
  offsetsL : X.offsetsL+modulus h J+1≤stop
  offsetsR : X.offsetsR+modulus h J+1≤stop
  flatL : X.flatL+X.sizeL≤stop
  flatR : X.flatR+X.sizeR≤stop
  occurrence : occurrenceRow X code J+J≤stop
  maps : X.maps+2*(512*h)*scheduleSize h≤stop
  candidates : X.candidates+scheduleSize h≤stop
  histL : X.histL+LightLocalCoverSchedule.rows h*localPrime h≤stop
  histR : X.histR+LightLocalCoverSchedule.rows h*localPrime h≤stop
  stagesL : X.stagesL+(J*(512*h)+1)*SubsetAddress.downsetCap (J*(512*h)) cut≤stop
  stagesR : X.stagesR+(J*(512*h)+1)*SubsetAddress.downsetCap (J*(512*h)) cut≤stop

theorem wanted_selected_ends {pair bank cover srcB srcC NB NC g h J cut occ i j code stop : ℕ}
    (hg : 0<g) (hi : i<BandPartition.size NB g) (hj : j<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J)
    (hsrcB : srcB+NB≤stop) (hsrcC : srcC+NC≤stop)
    (hpair : SourceBandPairData.next pair NB NC g (modulus h J)≤stop)
    (hbank : SourceBandBankData.finish bank NB NC g h J cut≤stop)
    (hocc : occ+LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : LightCoverKeyData.keyEnd cover h J≤stop) :
    WantedSourceEnds (retained pair bank cover NB NC g h J cut occ i j code)
      pair bank cover srcB srcC i j code h J cut stop := by
  have hp := SourceBandPairData.ordered pair NB NC g (modulus h J)
  have hleftWork : SourceBandLayout.work (SourceBandPairData.leftBase pair) NB g (modulus h J)≤stop :=
    hp.2.1.trans (hp.2.2.le.trans hpair)
  have hrightWork : SourceBandLayout.work (SourceBandPairData.rightBase pair NB g (modulus h J)) NC g (modulus h J)≤stop := by
    exact hp.2.2.le.trans hpair
  have hleft := wanted_band_row_ends (base := SourceBandPairData.leftBase pair) (m := modulus h J) hi
  have hright := wanted_band_row_ends (base := SourceBandPairData.rightBase pair NB g (modulus h J))
    (m := modulus h J) hj
  have hstartL := SourceBandLayout.start_add_len hg hi
  have hstartR := SourceBandLayout.start_add_len hg hj
  have hstopL := BandPartition.stop_le NB g i
  have hstopR := BandPartition.stop_le NC g j
  have hbankBase : bank+5≤SourceBandBankData.finish bank NB NC g h J cut := by
    unfold SourceBandBankData.finish SourceBandBankData.first SourceBandBankLayout.baseAt
    omega
  have hsourceL := SharedReportingBankSources.source_bounds (base := bank) (NB := NB) (NC := NC) (h := h) (J := J) (cut := cut)
    (hi.trans_le (le_max_left _ _)) hk
  have hsourceR := SharedReportingBankSources.source_bounds (base := bank) (NB := NB) (NC := NC) (h := h) (J := J) (cut := cut)
    (hj.trans_le (le_max_right _ _)) hk
  have hcoverEnds := wanted_cover_ends cover h J
  have hmul := Nat.mul_le_mul_right J (show code+1≤LightBlockSourceCatalog.count h J from hk)
  simp only [Nat.add_mul,one_mul] at hmul
  refine ⟨?_,hbankBase.trans hbank,?_,hleft.1.trans hleftWork,hright.1.trans hrightWork,
    ?_,?_,?_,?_,hleft.2.1.trans hleftWork,hright.2.1.trans hrightWork,
    hleft.2.2.trans hleftWork,hright.2.2.trans hrightWork,?_,
    hcoverEnds.2.1.trans hcover,hcoverEnds.2.2.1.trans hcover,
    hcoverEnds.2.2.2.1.trans hcover,hcoverEnds.2.2.2.2.trans hcover,
    hsourceL.2.2.1.trans hbank,hsourceR.2.2.2.trans hbank⟩
  · unfold SourceBandPairData.leftBase at hp
    omega
  · omega
  · change SharedReportingBankSources.leftCell bank h J cut i code+1≤stop
    omega
  · change SharedReportingBankSources.rightCell bank h J cut j code+1≤stop
    omega
  · change srcB+BandPartition.start g i+SourceBandLayout.len NB g i≤stop
    omega
  · change srcC+BandPartition.start g j+SourceBandLayout.len NC g j≤stop
    omega
  · change occ+code*J+J≤stop
    omega

theorem WantedSourceEnds.values {X : Pointers} {pair bank cover srcB srcC i j code h J cut stop : ℕ}
    (H : WantedSourceEnds X pair bank cover srcB srcC i j code h J cut stop) :
    ∀ v∈ReportingHostSourceSelection.values X srcB srcC code J, v≤stop := by
  intro v hv
  simp only [ReportingHostSourceSelection.values,List.mem_cons,List.not_mem_nil,or_false] at hv
  rcases hv with hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv|hv <;> subst v
  all_goals
    have h1 := H.sourceL
    have h2 := H.sourceR
    have h3 := H.offsetsL
    have h4 := H.offsetsR
    have h5 := H.flatL
    have h6 := H.flatR
    have h7 := H.occurrence
    have h8 := H.maps
    have h9 := H.candidates
    have h10 := H.histL
    have h11 := H.histR
    have h12 := H.stagesL
    have h13 := H.stagesR
    omega

theorem wanted_catalog_bounds {pair bank cover report NB NC g h J occ i j code stop K : ℕ}
    (hi : i<BandPartition.size NB g) (hj : j<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J) (hK : K≤LightSwitchDepth.depth J)
    (hbank : SourceBandBankData.finish bank NB NC g h J (LightBlockQuery.sourceCut h J)≤report)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤stop) :
    SharedReportingBankAccess.recordAt report J NB NC g code i j+5*(K+1)≤stop ∧
    ∀ k≤K, ReportingHostLevelData.Bounds h J k
      (SharedReportingBankAccess.levelCatalog report h J NB NC g code i j k)
      (retained pair bank cover NB NC g h J (LightBlockQuery.sourceCut h J) occ i j code).stagesL
      (retained pair bank cover NB NC g h J (LightBlockQuery.sourceCut h J) occ i j code).stagesR stop := by
  have he := (SharedReportingBankAccess.record_end (free := report) hk hi hj).trans
    ((SharedReportingBankHeader.payload_le_finish report h J NB NC g).trans hreport)
  refine ⟨?_,?_⟩
  · unfold SharedReportingBankHeader.levels at he
    omega
  · intro k hkk
    exact SharedReportingBankAccess.bounds hk hi hj (by unfold SharedReportingBankHeader.levels; omega) hbank hreport

end ThreeSum.SharedReportingBankResourceBounds
