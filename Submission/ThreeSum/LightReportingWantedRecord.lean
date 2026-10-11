import Submission.ThreeSum.ReportingHostWantedRecordData
import Submission.ThreeSum.LightReportingWantedRecordCall
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedAccess

/-!
# The actual record loader decides its selected original owner fiber

All reporting semantics below are derived from the retained source/cover/
catalog constructors and the actual decoder. The scratch geometry is the
executed layout; the capacity follows from the original physical counts.
-/

namespace ThreeSum.LightReportingWantedRecord

open Light Finset BandRawA BandCandidateRows GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting BlockEncoding BlockForced BlockMaskLayout BlockCoefficientRows
open ReportingHostWantedOriginal ReportingHostWantedControls ReportingHostWantedLayout
open ReportingHostFrontierLayout ReportingHostSourceSelectionStored OutputDecodeRecords
open ReportingHostWantedRecordData SharedReportingBankResourceBounds

set_option maxHeartbeats 3500000
set_option maxRecDepth 20000
set_option linter.unusedSectionVars false

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n NB NC g pair bank cover h J p occ srcB srcC report output dst counter K old threshold V d i : ℕ}
    {rs : List Record} {shift : ℤ}
    (w : Wanted h J (AType n g rs))
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (BlockSourceEncoding.modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output)
    (hg : 0<g) (hp : 0<p) (hguard : 4*(p : ℤ)≤globalModulus h J)
    (hK : K≤LightSwitchDepth.depth J) (hKJ : K≤J)
    (hkey : globalModulus h J∣valueAt n g rs fA w.1.val%(p : ℤ)+
      lift w.2.1*(p : ℤ)+shift-globalKey w.2.2)
    (hselected : Seg μ (access dst J)
      (record (selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output)))
    (hlayout : SegN μ dst (values (LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC)))
    (hdecoded : LightWantedDecode.Stored μ (decoded dst) (items n g rs).length h J i output)
    (hcounter : counter+4≤dst)
    (hcounterRead : μ counter=(old : ℤ)) (hthreshold : μ (counter+1)=(threshold : ℤ))
    (hends : WantedSourceEnds
      (LightReportingWantedAccess.selection n g rs w.1.val pair bank cover NB NC h J
        (LightBlockQuery.sourceCut h J) occ (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output))
      pair bank cover srcB srcC (ownerRecord n g rs w.1.val).b (ownerRecord n g rs w.1.val).c
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output) h J
      (LightBlockQuery.sourceCut h J) counter)
    (hbank : SourceBandBankData.finish bank NB NC g h J (LightBlockQuery.sourceCut h J)≤report)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤counter)
    (hbuffers : WantedBuffers lim dst h J K (items n g rs).length NB NC V)
    (hqueries : ∀ k≤K, ReportingHostLevelData.Scratch lim h J k
      (catalogs n NB NC g report h J rs w output k)
      (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b).card
      (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c).card
      (LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC).maskBase
      (LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC).work)
    (hw : (lim.space : ℤ)≤lim.word)
    (hrecordSpace : LightReportingWantedRecordCall.space (access dst J) dst cover counter h J K≤lim.space)
    (hselectedWords : ∀ z∈record (selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output), |z|≤lim.word)
    (hguardWord : ((old+rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w+threshold+2 : ℕ) : ℤ)≤lim.word)
    (hword : (LightReportingTerminal.word h J : ℤ)≤lim.word)
    (hreadB : ∀ j<NB, μ (srcB+j)=fB j) (hreadC : ∀ j<NC, μ (srcC+j)=fC j)
    (hvaluesB : ∀ j<NB, |fB j|≤lim.word) (hvaluesC : ∀ j<NC, |fC j|≤lim.word)
    (htarget : ∀ j<NB, |valueAt n g rs fA w.1.val+fB j|≤lim.word)
    (hcountWord : ((NB*NC : ℕ) : ℤ)≤lim.word)
    (hd : d+wantedDepth h J K (items n g rs).length NB NC≤lim.depth) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    let D := catalogs n NB NC g report h J rs w output
    Meets lim LightReportingWantedRecordCall.program 138 d
      [access dst J,dst,h,J,K,BlockSourceEncoding.modulus h J,cover,counter] μ
      (LightReportingWanted.time p shift (left rs fB w) (right rs fC w)
        S.NL S.NR old threshold (localItems h J n NB NC g p rs fA fB fC shift w) w D K+4000)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w ∨
          Terminal h J n NB NC g p rs fA fB fC shift w K) ∧
        ν counter=((old+rootMass (localItems h J n NB NC g p rs fA fB fC shift w) w : ℕ) : ℤ) ∧
        KeptBut μ ν (packed dst J) counter 1) := by
  let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
  let D := catalogs n NB NC g report h J rs w output
  let L := LightReportingWantedLayout.layout dst h J K (items n g rs).length NB NC
  let A := finiteAIndices n g rs (owner rs w)
  let B := finiteBandPositions NB g (ownerRecord n g rs w.1.val).b
  let C := finiteBandPositions NC g (ownerRecord n g rs w.1.val).c
  let a := fun i : AType n g rs => valueAt n g rs fA i.val
  let b := fun i : Fin NB => fB i.val
  let c := fun i : Fin NC => fC i.val
  let I := rawOn h J (p : ℤ) shift (A ×ˢ (B ×ˢ C)) a b c
  have hI : I=localItems h J n NB NC g p rs fA fB fC shift w := rfl
  have haCard : A.card≤(items n g rs).length := by
    simpa only [Fintype.card_fin] using (Finset.card_le_univ A)
  have hbCard : B.card≤NB := by simpa only [Fintype.card_fin] using (Finset.card_le_univ B)
  have hcCard : C.card≤NC := by simpa only [Fintype.card_fin] using (Finset.card_le_univ C)
  have hcapacity := capacity_le (shift := shift) A B C a b c w
    (by exact_mod_cast hp) hguard haCard hbCard hcCard
  have hgeo := make_bounds (root := ReportingHostWantedLayout.root dst J)
    (K := K) (W := LightBlockQuery.width h J) (G := groupSize h)
    (T := 2^(LightBlockQuery.width h J)) hcapacity
  change Bounds L (ReportingHostWantedLayout.root dst J) K (LightBlockQuery.width h J)
    (groupSize h) (2^(LightBlockQuery.width h J)) (capacity I w) at hgeo
  have hterminal := terminal_count_le h J K
  have hdepth := wanted_depth (shift := shift) A B C a b c w hKJ (by exact_mod_cast hp) hguard haCard hbCard hcCard hd
  have hd' : d<lim.depth := by
    unfold wantedDepth at hd
    omega
  have hsource := sources (fA := fA) (pair := pair) (cover := cover) (srcB := srcB) (srcC := srcC)
    (report := report) w HB hi hj houtput he
  have hcatalog (k : ℕ) (hk : k≤K) := catalog (fA := fA) (pair := pair) (bank := bank) (cover := cover)
    (occ := occ) (srcB := srcB) (srcC := srcC) w HQ hi hj houtput he
    (show k<SharedReportingBankHeader.levels J by unfold SharedReportingBankHeader.levels; omega) (hk.trans hKJ)
  have hcatBounds := wanted_catalog_bounds (pair := pair) (cover := cover) (occ := occ)
    hi hj (OutputDecodeOccurrenceCode.source_code_lt h J output) hK hbank hreport
  have hmeta : ∀ k≤K, SegN μ (S.catalog+5*k) ((D k).record h k) := fun k hk => (hcatalog k hk).1
  have hcatStored : ∀ (k : ℕ) (hk : k≤K),
      ReportingHostLevelData.Stored μ (D k) (hk.trans hKJ) (p : ℤ) shift B C b c w.2.2 :=
    fun k hk => (hcatalog k hk).2
  have hcatBounds' : ∀ k≤K, ReportingHostLevelData.Bounds h J k (D k) S.baseL S.baseR counter := hcatBounds.2
  have hmetaEnd : S.catalog+5*(K+1)≤counter := hcatBounds.1
  have hraw := raw_rows (w := w) hdecoded he
  have hscalars := cover_scalars HC
  have hbuckets := ReportingHostWantedRecordData.buckets (fA := fA) (bank := bank) (cover := cover)
    (occ := occ) (srcB := srcB) (srcC := srcC) (report := report) (output := output) w HP hi hj
  have hcoverInput := ReportingHostWantedRecordData.cover_input (fA := fA) (NB := NB) (NC := NC)
    (pair := pair) (bank := bank) (occ := occ) (srcB := srcB) (srcC := srcC)
    (report := report) (output := output) w HC
  have hreads := source_reads (pair := pair) (bank := bank) (cover := cover) (h := h) (J := J)
    (occ := occ) (report := report) (output := output) (fA := fA) w hg hi hj hreadB hreadC
  have hv : S.av=a w.1 := selected_value fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
  have hcounts : S.NL=leftCount rs NB w ∧ S.NR=rightCount rs NC w := ⟨rfl,rfl⟩
  have ha : |a w.1|≤lim.word := by
    rw [← hv]
    exact hselectedWords S.av (by simp only [record,List.mem_cons]; exact Or.inl rfl)
  have hlocalB (j : ℕ) (hj' : j<S.NL) : BandPartition.start g (ownerRecord n g rs w.1.val).b+j<NB :=
    SourceBandLayout.input_index hg hi hj'
  have hlocalC (j : ℕ) (hj' : j<S.NR) : BandPartition.start g (ownerRecord n g rs w.1.val).c+j<NC :=
    SourceBandLayout.input_index hg hj hj'
  have hcountL : S.NL≤NB := (SourceBandLayout.len_le_cap NB g _).trans (min_le_left _ _)
  have hcountR : S.NR≤NC := (SourceBandLayout.len_le_cap NC g _).trans (min_le_left _ _)
  have hcountLocal : ((S.NL*S.NR : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.mul_le_mul hcountL hcountR)).trans hcountWord
  have hoccEnd : S.occ+J≤counter := hends.occurrence
  have hreportRun := LightReportingWanted.program_meets (μ := μ) (d := d+1)
    (srcL := S.srcL) (srcR := S.srcR) (offsetsL := S.offsetsL) (offsetsR := S.offsetsR)
    (flatL := S.flatL) (flatR := S.flatR) (NL := S.NL) (NR := S.NR) (occ := S.occ)
    (maps := S.maps) (candidates := S.candidates) (histL := S.histL) (histR := S.histR)
    (root := L.root) (catalogs := S.catalog) (rawRows := rawRows dst J) (rows := packed dst J)
    (cover := cover) (counter := counter) (baseL := S.baseL) (baseR := S.baseR)
    (masks := L.masks) (childL := L.childL) (childR := L.childR) (counts := L.counts)
    (selected := L.selected) (maskBase := L.maskBase) (work := L.work)
    (terminalMasks := L.terminalMasks) (masksL := L.masksL) (masksR := L.masksR)
    (base := L.base) (bitBase := L.bitBase) (rowOut := L.rowOut)
    p shift (left rs fB w) (right rs fC w) A B C a b c w D hKJ
    ⟨mem_owner rs w,hkey⟩ hw hsource hcatStored hcatBounds' hqueries hmeta hmetaEnd
    (rawRows_before_packed dst J) (by change packed dst J+J≤ReportingHostWantedLayout.root dst J; rfl)
    (by unfold rawRows decoded; omega) hscalars.1 (by have hh := hends.coverHeader; omega)
    hraw hcounterRead hthreshold hguardWord
    hgeo.frontier hgeo.masks hgeo.childL hgeo.childR hgeo.counts hgeo.selected
    hbuffers.parameters hbuffers.pack hbuckets.1 hbuckets.2
    hends.sourceL hends.sourceR hends.offsetsL hends.offsetsR hends.flatL hends.flatR
    (by unfold packed access decoded; omega)
    (Or.inr hends.occurrence) hends.maps hends.candidates hends.histL hends.histR
    hgeo.terminalFrontier
    ((Nat.add_le_add_left hterminal _).trans hgeo.terminalMasks)
    ((Nat.add_le_add_left hterminal _).trans hgeo.masksL)
    ((Nat.add_le_add_left hterminal _).trans hgeo.masksR)
    ((terminal_stop_mono hterminal).trans hgeo.stop) hgeo.bits hgeo.rowOut
    hbuffers.terminal hword (fun j hj' => occurrences (fA := fA) (pair := pair) (cover := cover)
      (srcB := srcB) (srcC := srcC) (report := report) w HB houtput he hj')
    hcoverInput hreads.1 hreads.2 (fun j hj' => hvaluesB _ (hlocalB j hj'))
    (fun j hj' => hvaluesC _ (hlocalC j hj')) ha (fun j hj' => htarget _ (hlocalB j hj'))
    hcountLocal (by omega)
  have hreportCall : Meets lim LightReportingWanted.program 137 (d+1)
      (arguments S L dst cover counter h J K) μ
      (LightReportingWanted.time p shift (left rs fB w) (right rs fC w)
        S.NL S.NR old threshold I w D K)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+rootMass I w ∨
          Terminal h J n NB NC g p rs fA fB fC shift w K) ∧
        ν counter=((old+rootMass I w : ℕ) : ℤ) ∧ KeptBut μ ν (packed dst J) counter 1) := by
    simpa only [arguments,hv,Terminal,← hI,← hcounts.1,← hcounts.2,a] using hreportRun
  exact LightReportingWantedRecordCall.program_meets hselected hlayout hscalars.2.1 hscalars.2.2
    hw hd' hrecordSpace hselectedWords hbuffers.values hreportCall

end ThreeSum.LightReportingWantedRecord
