import Submission.ThreeSum.ReportingHostWantedOriginal
import Submission.ThreeSum.ReportingHostWantedControls
import Submission.ThreeSum.SharedReportingBankAccess

/-!
# Original-domain facts carried by the two actual wanted records

All source stages, buckets, occurrence rows, and per-level catalogs below
come from the retained concrete constructors. The decoder supplies the
unaltered original Q masks used by the guarded reporter.
-/

namespace ThreeSum.ReportingHostWantedRecordData

open Light Finset BandRawA BandCandidateRows GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting BlockEncoding BlockForced BlockMaskLayout BlockCoefficientRows
open ReportingHostWantedOriginal ReportingHostWantedControls ReportingHostWantedLayout
open ReportingHostSourceSelectionStored OutputDecodeRecords

set_option maxHeartbeats 2300000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

def selected (fA : ℕ→ℤ) (n NB NC g pair bank cover h J occ srcB srcC report : ℕ)
    (rs : List Record) (w : Wanted h J (AType n g rs)) (output : ℕ) : Selection :=
  ofAccess fA n g rs w.1.val pair bank cover NB NC h J (LightBlockQuery.sourceCut h J) occ
    (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output) srcB srcC report

def catalogs (n NB NC g report h J : ℕ) (rs : List Record)
    (w : Wanted h J (AType n g rs)) (output k : ℕ) : ReportingHostLevelData.Catalog :=
  SharedReportingBankAccess.levelCatalog report h J NB NC g
    (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output)
    (ownerRecord n g rs w.1.val).b (ownerRecord n g rs w.1.val).c k

theorem selected_value (fA : ℕ→ℤ) (n NB NC g pair bank cover h J occ srcB srcC report : ℕ)
    (rs : List Record) (w : Wanted h J (AType n g rs)) (output : ℕ) :
    (selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output).av=
      valueAt n g rs fA w.1.val := by
  change fA (BandRawA.labelAt n g rs w.1.val).position=(values fA (items n g rs)).getD w.1.val 0
  exact (values_getD fA w.1.isLt).symm

theorem selected_counts (fA : ℕ→ℤ) (n NB NC g pair bank cover h J occ srcB srcC report : ℕ)
    (rs : List Record) (w : Wanted h J (AType n g rs)) (output : ℕ) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    S.NL=leftCount rs NB w ∧ S.NR=rightCount rs NC w := ⟨rfl,rfl⟩

theorem localItems_eq_product (fA fB fC : ℕ→ℤ) (n NB NC g h J p : ℕ)
    (rs : List Record) (shift : ℤ) (w : Wanted h J (AType n g rs)) :
    localItems h J n NB NC g p rs fA fB fC shift w=
      rawOn h J (p : ℤ) shift
        (finiteAIndices n g rs (owner rs w) ×ˢ
          (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b ×ˢ
            finiteBandPositions NC g (ownerRecord n g rs w.1.val).c))
        (fun i => valueAt n g rs fA i.val) (fun i => fB i.val) (fun i => fC i.val) := rfl

section Stored

variable {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
  {n NB NC g pair bank cover h J p occ srcB srcC report output : ℕ}
  {rs : List Record} {shift : ℤ} (w : Wanted h J (AType n g rs))

theorem sources
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    ReportingHostLevelData.Sources μ (p : ℤ) shift
      (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
      (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
      (fun i : Fin NB => fB i.val) (fun i : Fin NC => fC i.val) w.2.2 S.baseL S.baseR := by
  rw [he]
  exact sources_decoded (pair := pair) (cover := cover) HB hi hj houtput

theorem catalog
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output)
    {k : ℕ} (hk : k<SharedReportingBankHeader.levels J) (hkJ : k≤J) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    let D := catalogs n NB NC g report h J rs w output k
    SegN μ (S.catalog+5*k) (D.record h k) ∧
      ReportingHostLevelData.Stored μ D hkJ (p : ℤ) shift
        (finiteBandPositions NB g (ownerRecord n g rs w.1.val).b)
        (finiteBandPositions NC g (ownerRecord n g rs w.1.val).c)
        (fun i : Fin NB => fB i.val) (fun i : Fin NC => fC i.val) w.2.2 := by
  rw [he]
  exact SharedReportingBankAccess.original HQ houtput hi hj hk hkJ

theorem buckets
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (BlockSourceEncoding.modulus h J) shift)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    SourceBuckets.Stored μ (fun i => LightSourceResidues.key p (BlockSourceEncoding.modulus h J) 0 (left rs fB w i))
      S.NL (BlockSourceEncoding.modulus h J) S.offsetsL S.flatL ∧
    SourceBuckets.Stored μ (fun i => LightSourceResidues.key p (BlockSourceEncoding.modulus h J) shift (right rs fC w i))
      S.NR (BlockSourceEncoding.modulus h J) S.offsetsR S.flatR :=
  ⟨(HP.left _ hi).buckets,(HP.right _ hj).buckets⟩

theorem occurrences
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J
      (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (houtput : output<localCount h^J) (he : w.2.2=LightOutputDecodeOriginal.output h J output)
    {t : ℕ} (ht : t<J) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    μ (S.occ+t)=(occurrenceIndices (outputOccurrences w.2.2) t : ℤ) := by
  rw [he]
  exact occurrence_rows_decoded HB houtput t ht

theorem cover_input (HC : LightCoverKeyData.Stored μ cover h J) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    BlockSourceCoverInput.Input μ h S.maps S.candidates S.histL S.histR :=
  BlockSourceCoverInput.of_cover HC.data HC.rows HC.indices

theorem source_reads (hg : 0<g)
    (hi : (ownerRecord n g rs w.1.val).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs w.1.val).c<BandPartition.size NC g)
    (hreadB : ∀ i<NB, μ (srcB+i)=fB i) (hreadC : ∀ i<NC, μ (srcC+i)=fC i) :
    let S := selected fA n NB NC g pair bank cover h J occ srcB srcC report rs w output
    (∀ i<S.NL, μ (S.srcL+i)=left rs fB w i) ∧
      (∀ i<S.NR, μ (S.srcR+i)=right rs fC w i) := by
  constructor
  · intro i hi'
    have hh := hreadB _ (SourceBandLayout.input_index hg hi hi')
    simpa only [selected,ofAccess,LightReportingWantedAccess.selection,retained,
      ReportingHostWantedOriginal.left,Nat.add_assoc] using hh
  · intro i hi'
    have hh := hreadC _ (SourceBandLayout.input_index hg hj hi')
    simpa only [selected,ofAccess,LightReportingWantedAccess.selection,retained,
      ReportingHostWantedOriginal.right,Nat.add_assoc] using hh

theorem raw_rows {dst N i : ℕ}
    (HD : LightWantedDecode.Stored μ (decoded dst) N h J i output)
    (he : w.2.2=LightOutputDecodeOriginal.output h J output) :
    SegN μ (rawRows dst J) (rawMasks (outputRows w.2.2)) := by
  intro t ht
  have ht' : t<J := by simpa only [List.length_map,rawMasks_length] using ht
  have hh := HD.rows.masks ⟨t,ht'⟩
  simpa only [he,rawRows,rawMasks,outputRows,List.getElem_map,List.getElem_ofFn] using hh

end Stored

theorem cover_scalars {μ : ℕ→ℤ} {cover h J : ℕ} (HC : LightCoverKeyData.Stored μ cover h J) :
    μ (cover+3)=(groupSize h : ℤ) ∧ μ (cover+6)=(localPrime h : ℤ) ∧
      μ (cover+7)=(localBucketCap h : ℤ) := by
  refine ⟨?_,?_,?_⟩
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,
      LightLocalCounts.values,LightLocalCoverMetadata.values]
      using HC.header.getD (i := 3) (by simp [LightLocalCoverInit.values,
        LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values]) 0
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,
      LightLocalCounts.values,LightLocalCoverMetadata.values]
      using HC.header.getD (i := 6) (by simp [LightLocalCoverInit.values,
        LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values]) 0
  · simpa [LightLocalCoverInit.values,LightLocalParameters.values,
      LightLocalCounts.values,LightLocalCoverMetadata.values]
      using HC.header.getD (i := 7) (by simp [LightLocalCoverInit.values,
        LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values]) 0

end ThreeSum.ReportingHostWantedRecordData
