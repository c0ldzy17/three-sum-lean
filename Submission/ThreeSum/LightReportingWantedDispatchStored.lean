import Submission.ThreeSum.ReportingHostWantedConsumerData

/-!
# Run an actual physical wanted slot from the retained encoded color

The slot's original label and two physical integer indices are supplied by
the emitted array. Every source, catalog, mask, allocation and selected
value used by the fixed152 executable is derived from the retained payload.
-/

namespace ThreeSum.LightReportingWantedDispatchStored

open Light Scales BandScales BandRawA RawReporting RawIncidences GlobalEncoding
open EncodedColorNormalizedData EncodedColorWantedConsumerData ThreeSumWantedHostData
open ReportingHostWantedOriginal ReportingHostWantedPhysical ReportingHostWantedLayout
open ReportingHostWantedConsumerData SharedReportingBankResourceBounds

set_option maxHeartbeats 3800000
set_option maxRecDepth 24000
set_option linter.unusedSectionVars false

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {free n U d s raw output old threshold : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (HQ : ThreeSumReportingSetupData.Catalog μ free n A B C hsA hsB hsC)
    (hx : ∀ i, |x i|≤(U : ℤ))
    (w : Label n A B C hsA hsB hsC)
    (hs : s<count n A B C hsA hsB hsC)
    (hraw : raw<3*(config free n A B C hsA hsB hsC).N)
    (hout : output<OutputDecodeRecords.localCount (half n)^blocks n)
    (hpos : w.1.val=raw%(config free n A B C hsA hsB hsC).N)
    (he : w.2.2=LightOutputDecodeOriginal.output (half n) (blocks n) output)
    (hleft : μ ((config free n A B C hsA hsB hsC).pairs+2*s)=(raw : ℤ))
    (hright : μ ((config free n A B C hsA hsB hsC).pairs+2*s+1)=(output : ℤ))
    (hp : 0<EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    (hguard : 4*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)≤globalModulus (half n) (blocks n))
    (hkey : globalModulus (half n) (blocks n) ∣
      valueAt A.length (bandSize n) (records n A B C hsA hsB hsC) (fun j => A.getD j 0) w.1.val %
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      lift w.2.1*(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)+
      ThreeSumReportingSetupData.shift n A B C hsA hsB hsC-globalKey w.2.2)
    (hcounter : μ (config free n A B C hsA hsB hsC).counter=(old : ℤ))
    (hthreshold : μ ((config free n A B C hsA hsB hsC).counter+1)=(threshold : ℤ))
    (hcap : μ ((config free n A B C hsA hsB hsC).counter+2)=(representationCap (half n) (blocks n) : ℤ))
    (hold : old≤3*(magnitude n)^7)
    (hmass : labelMass n A B C hsA hsB hsC w≤3*(magnitude n)^7)
    (hthresholdBound : threshold≤9*(magnitude n)^8)
    (hok : (wantedNeed n U).Ok lim (config free n A B C hsA hsB hsC).layoutHeader (d+1)) :
    Meets lim LightReportingWantedDispatch.program 151 d
      (LightReportingWantedDispatch.arguments (config free n A B C hsA hsB hsC) s) μ
      (LightReportingWantedDispatch.time (config free n A B C hsA hsB hsC) (wantedDecodeV n)
        (recordTime free n A B C hsA hsB hsC w output old threshold))
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+labelMass n A B C hsA hsB hsC w ∨ labelHit n A B C hsA hsB hsC w) ∧
        ν (config free n A B C hsA hsB hsC).counter=((old+labelMass n A B C hsA hsB hsC w : ℕ) : ℤ) ∧
        KeptBut μ ν (config free n A B C hsA hsB hsC).layoutHeader
          (config free n A B C hsA hsB hsC).counter 1) := by
  let cfg := config free n A B C hsA hsB hsC
  let rs := records n A B C hsA hsB hsC
  let L := LightReportingWantedLayout.layout cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
  let occ := occurrence free n A B C hsA hsB hsC
  let code := OutputDecodeOccurrenceCode.code cfg.scheduleSize cfg.layerCount cfg.J output
  let S := ReportingHostWantedRecordData.selected (fun j => A.getD j 0) A.length B.length C.length
    (bandSize n) cfg.pair cfg.bank cfg.cover cfg.h cfg.J occ cfg.srcB cfg.srcC cfg.report rs w output
  let Q := fun (r : ℤ) ν => (r=0 ∨ r=1) ∧
    (r=1 ↔ threshold<old+labelMass n A B C hsA hsB hsC w ∨ labelHit n A B C hsA hsB hsC w) ∧
    ν cfg.counter=((old+labelMass n A B C hsA hsB hsC w : ℕ) : ℤ) ∧
    KeptBut μ ν cfg.layoutHeader cfg.counter 1
  have hNI : cfg.N=(items A.length (bandSize n) rs).length := incidence_length_eq ..
  have hNI0 := incidence_length_eq free n A B C hsA hsB hsC
  have hL : L=LightReportingWantedLayout.layout cfg.layoutHeader (half n) (blocks n)
      (LightSwitchDepth.depth (blocks n)) (items A.length (bandSize n) rs).length B.length C.length := by
    dsimp only [L]
    rw [hNI]
    rfl
  have hSL : S.NL=leftCount rs B.length w := rfl
  have hSR : S.NR=rightCount rs C.length w := rfl
  have hpos' : w.1.val=raw%(items A.length (bandSize n) rs).length := hpos.trans (congrArg (raw%·) hNI)
  have hpos0 : w.1.val=raw%(items A.length (bandSize n) (records n A B C hsA hsB hsC)).length := hpos'
  have hi : w.1.val<cfg.N := by rw [hNI]; exact w.1.isLt
  obtain ⟨_,hiB,hiC⟩ := owner_bands hi
  have hB := (ThreeSumColorBudgets.normalized_lengths H).2.1
  have hC := (ThreeSumColorBudgets.normalized_lengths H).2.2
  have hN : cfg.N≤3*(magnitude n)^3 := incidence_length_le_magnitude H
  have hN' : (items A.length (bandSize n) rs).length≤3*(magnitude n)^3 := by rw [← hNI]; exact hN
  have hK : cfg.K≤blocks n := depth_le_blocks n
  have hends : PersistentEnds cfg (positions free n A B C hsA hsB hsC) occ (bandSize n) (mu n)
      rs.length (count n A B C hsA hsB hsC) := persistent_ends H
  have hbank : SourceBandBankData.finish cfg.bank B.length C.length (bandSize n) (half n) (blocks n)
      (LightBlockQuery.sourceCut (half n) (blocks n))≤cfg.report := by
    rw [cut_eq_mu]
    exact hends.bank
  have hreport : SharedReportingBankHeader.finish cfg.report cfg.h cfg.J cfg.NB cfg.NC (bandSize n)≤cfg.counter := hends.report
  have hbefore : cfg.counter+4=cfg.layoutHeader := rfl
  have hc : cfg.counter≤cfg.layoutHeader := by dsimp only [cfg,rs] at *; omega
  have hbuf := wanted_buffers_of_ok hK hN hB hC hok
  have hdep := wanted_depth_of_ok hK hN hB hC hok
  have hd50 : d+1+50≤lim.depth :=
    (Nat.add_le_add_left (show 50≤wantedDepth (half n) (blocks n) cfg.K cfg.N B.length C.length from
      Nat.le_add_left 50 _) (d+1)).trans hdep
  have hd : d+5<lim.depth := by dsimp only [cfg,rs] at *; omega
  have haccess : access cfg.layoutHeader cfg.J+20≤lim.space := wanted_access_output_le hK hN hB hC hok
  have hspace : cfg.layoutHeader+38+2*cfg.J≤lim.space := by
    unfold access decoded at haccess
    dsimp only [cfg,rs] at *; omega
  have hg : cfg.cover+4≤cfg.layoutHeader := by
    have hh := (wanted_cover_ends cfg.cover cfg.h cfg.J).1.trans hends.cover
    dsimp only [cfg,rs] at *; omega
  have hcode : code<LightBlockSourceCatalog.count cfg.h cfg.J :=
    OutputDecodeOccurrenceCode.source_code_lt cfg.h cfg.J output
  have hselectedEnds := wanted_selected_ends (occ := occ) (cut := LightBlockQuery.sourceCut (half n) (blocks n))
    (BandScales.bandSize_pos n) hiB hiC hcode hends.srcB hends.srcC hends.pair
    (hbank.trans (by have hb := hends.reportBeforeCounter; dsimp only [cfg,rs] at *; omega)) hends.occurrence hends.cover
  have hfit := wanted_access_fits_of_ok (N := cfg.N) hselectedEnds hc hK hN hB hC hok
  have hval := incidence_value_bound H hx hi
  have hvalWord := wanted_integer_word_of_ok hval hok
  let AP := fun ν => SegN ν cfg.layoutHeader (ReportingHostWantedLayout.values L) ∧ Kept μ ν cfg.layoutHeader
  let BP := fun ν => LightWantedDecode.Stored ν (decoded cfg.layoutHeader)
      (items A.length (bandSize n) rs).length cfg.h cfg.J raw output ∧
    Seg ν (access cfg.layoutHeader cfg.J) (ReportingHostWantedControls.record S) ∧
    SegN ν cfg.layoutHeader (ReportingHostWantedLayout.values L) ∧ Kept μ ν cfg.layoutHeader
  have retained (ν : ℕ→ℤ) (hk : Kept μ ν cfg.layoutHeader) :=
    retained_of_kept H HQ (fun a ha => hk a (ha.trans_le hc))
  apply LightReportingWantedDispatch.program_meets (L := L) (A := AP) (B := BP) (Q := Q)
    hok.space (by dsimp only [cfg,rs] at *; omega) hspace
  · have hgRead := (ReportingHostWantedRecordData.cover_scalars H.cover).1
    exact (wanted_layout_meets hK hN hB hC hg (by dsimp only [cfg,rs] at *; omega) hgRead hcap hok).mono le_rfl
      (fun r ν hr => ⟨hr.1,hr.2.1,fun a ha => hr.2.2 a (Or.inl ha)⟩)
  · intro ν hν
    obtain ⟨Hν,HQν⟩ := retained ν hν.2
    have HBν : SourceBandBankData.Stored ν (fun j => B.getD j 0) (fun j => C.getD j 0)
        cfg.bank B.length C.length (bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)
        (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) := by
      rw [cut_eq_mu]
      exact Hν.sources.banks
    have hraw' : raw<3*(items A.length (bandSize n) rs).length := by rw [← hNI]; exact hraw
    have hiB' : (ownerRecord A.length (bandSize n) rs (raw%(items A.length (bandSize n) rs).length)).b<
        BandPartition.size B.length (bandSize n) := by rw [← hpos']; exact hiB
    have hiC' : (ownerRecord A.length (bandSize n) rs (raw%(items A.length (bandSize n) rs).length)).c<
        BandPartition.size C.length (bandSize n) := by rw [← hpos']; exact hiC
    have hdecode := LightReportingWantedDecodeAccess.program_meets_fits (d := d+1)
      (decoded := decoded cfg.layoutHeader) (dst := access cfg.layoutHeader cfg.J) (work := L.work)
      (n := A.length) (g := bandSize n) (rs := rs) (NB := B.length) (NC := C.length)
      (h := half n) (J := blocks n) (pair := cfg.pair) (bank := cfg.bank) (cover := cfg.cover)
      (srcB := cfg.srcB) (srcC := cfg.srcC) (report := cfg.report) (occ := occ)
      (pairs := cfg.pairs) (slot := s) (masks := cfg.masks)
      (raw_stored Hν) (records_stored Hν) hraw' hout
      (wanted_left_index_le hN hraw) (wanted_right_index_le hout)
      Hν.sources.buckets HBν Hν.cover HQν hiB' hiC' hok.space (by dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.values; rw [hNI] at hh; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.owners; rw [hNI] at hh; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.positions; rw [hNI] at hh; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.records; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (hends.srcB.trans (by unfold decoded; omega))
      (hends.srcC.trans (by unfold decoded; omega))
      (hends.pair.trans (by unfold decoded; omega))
      (hbank.trans (by have hh := hends.reportBeforeCounter; unfold decoded; omega))
      hends.occurrence (hends.cover.trans (by unfold decoded; omega))
      (hends.report.trans (by unfold decoded; omega))
      (by unfold access; rfl)
      (by have hh := wanted_work_eq cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
          have hf := wanted_work_formula cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC
          change access cfg.layoutHeader cfg.J+20≤
            (LightReportingWantedLayout.layout cfg.layoutHeader cfg.h cfg.J cfg.K cfg.N cfg.NB cfg.NC).work
          unfold access decoded
          dsimp only [cfg,rs] at *; omega)
      (by have hh := hends.pairs; unfold decoded; dsimp only [cfg,rs] at *; omega)
      (hends.masks.trans (by unfold decoded; omega))
      ((hν.2 _ (by have hh := hends.pairs; dsimp only [cfg,rs] at *; omega)).trans hleft)
      ((hν.2 _ (by have hh := hends.pairs; dsimp only [cfg,rs] at *; omega)).trans hright)
      (masks_read Hν) hbuf.decoder (by simpa only [cfg,rs,hNI0] using (wanted_words_of_ok hN hok).2.1)
      (by simpa only [code,cfg,rs,config,half,blocks,LightReportingWantedAccess.selection,← hpos0] using hfit)
      (by simpa only [cfg,rs,← hpos0] using hvalWord)
    have hdecode' := hdecode.mono (R' := fun _ ξ => BP ξ) le_rfl (fun _ ξ hr => by
      refine ⟨hr.2.1,?_,?_,?_⟩
      · simpa only [S,ReportingHostWantedRecordData.selected,ReportingHostWantedControls.ofAccess_record,
          cfg,rs,config,half,blocks,← hpos0] using hr.2.2.1
      · exact hν.1.of_kept hr.2.2.2 (by simp only [ReportingHostWantedLayout.values,List.length_map,List.length_cons,List.length_nil,decoded]; omega)
      · exact fun a ha => (hr.2.2.2 a (by unfold decoded; dsimp only [cfg,rs] at *; omega)).trans (hν.2 a ha))
    simpa only [LightReportingWantedDispatch.decodeArguments,cfg,rs,config,half,blocks,incidences,
      BandRawA.values_length,EncodedColorWantedConsumerData.records] using hdecode'
  · intro ν hν
    obtain ⟨Hν,HQν⟩ := retained ν hν.2.2.2
    have HBν : SourceBandBankData.Stored ν (fun j => B.getD j 0) (fun j => C.getD j 0)
        cfg.bank B.length C.length (bandSize n) (half n) (blocks n)
        (LightBlockQuery.sourceCut (half n) (blocks n)) occ
        (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ)
        (ThreeSumReportingSetupData.shift n A B C hsA hsB hsC) := by
      rw [cut_eq_mu]
      exact Hν.sources.banks
    have hrun := LightReportingWantedRecordNeed.program_meets (d := d+1)
      (pair := cfg.pair) (bank := cfg.bank) (cover := cfg.cover) (occ := occ)
      (srcB := cfg.srcB) (srcC := cfg.srcC) (report := cfg.report) (records := cfg.records)
      (dst := cfg.layoutHeader) (counter := cfg.counter) (K := cfg.K) w
      Hν.sources.buckets HBν Hν.cover HQν hiB hiC hout he hp hguard le_rfl hK hkey
      hν.2.1 (by have hh := hν.2.2.1; rw [hL] at hh; exact hh) hν.1 (by omega)
      ((hν.2.2.2 _ (by dsimp only [cfg,rs] at *; omega)).trans hcounter)
      ((hν.2.2.2 _ (by dsimp only [cfg,rs] at *; omega)).trans hthreshold)
      hselectedEnds hends.records hends.srcB hends.srcC hbank hreport hN' hB hC
      hold hmass hthresholdBound (normalized_read Hν).2.1 (normalized_read Hν).2.2
      (normalized_bound H hx).2.1 (normalized_bound H hx).2.2 hval hok
    have hrun' := hrun.mono (R' := Q) le_rfl (fun r ξ hr => by
      refine ⟨hr.1,hr.2.1,hr.2.2.1,?_⟩
      intro a ha
      exact (hr.2.2.2 a ⟨by unfold packed access decoded; dsimp only [cfg,rs] at *; omega,ha.2⟩).trans (hν.2.2.2 a ha.1))
    dsimp only [S,cfg,rs,config,half,blocks] at hSL hSR
    simpa only [LightReportingWantedDispatch.recordArguments,recordTime,labelMass,labelHit,fiber,
      hSL,hSR,cfg,config,half,blocks,BlockSourceEncoding.modulus,Scales.radix,Scales.localRadix,
      ThreeSumReportingSetupData.shift] using hrun'

end ThreeSum.LightReportingWantedDispatchStored
