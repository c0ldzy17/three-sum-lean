import Submission.ThreeSum.LightReportingSourceSelect
import Submission.ThreeSum.ReportingHostLevelData

/-!
# Selected controls from the actual retained original-source catalogs

The selector's concrete header reads follow from the existing band,
occurrence-bank and local-cover constructors. Its two independently chosen
bands supply the unchanged physical buckets and the exact original-output
source stages. No output-subset loop or source reconstruction is involved.
-/

namespace ThreeSum.ReportingHostSourceSelectionStored

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding
open ReportingHostSourceSelection OutputDecodeRecords BlockCoefficientRows

set_option maxHeartbeats 2300000
set_option maxRecDepth 12000

def retained (pair bank cover NL NR g h J cut occ i j code : ℕ) : Pointers where
  leftHeaders := SourceBandPairData.leftBase pair
  rightHeaders := SourceBandPairData.rightBase pair NL g (modulus h J)
  firstBank := SourceBandBankData.first bank
  bankSpan := SourceBandBankLayout.span h J cut
  occurrenceBase := occ
  startL := BandPartition.start g i
  startR := BandPartition.start g j
  sizeL := SourceBandLayout.len NL g i
  sizeR := SourceBandLayout.len NR g j
  offsetsL := SourceBandLayout.offsets (SourceBandPairData.leftBase pair) NL g (modulus h J) i
  flatL := SourceBandLayout.flat (SourceBandPairData.leftBase pair) NL g (modulus h J) i
  offsetsR := SourceBandLayout.offsets (SourceBandPairData.rightBase pair NL g (modulus h J)) NR g (modulus h J) j
  flatR := SourceBandLayout.flat (SourceBandPairData.rightBase pair NL g (modulus h J)) NR g (modulus h J) j
  stagesL := LightBlockSourceBatchLayout.leftBase
    (SourceBandBankLayout.baseAt (SourceBandBankData.first bank) h J cut i)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut code
  stagesR := LightBlockSourceBatchLayout.rightBase
    (SourceBandBankLayout.baseAt (SourceBandBankData.first bank) h J cut j)
    (LightBlockSourceCatalog.count h J) (J*(512*h)) cut code
  maps := LightLocalCoverLayout.scheduleMaps (LightLocalCoverInit.base cover) h
  candidates := LightLocalCoverLayout.candidates (LightLocalCoverInit.base cover) h
  histL := LightLocalCoverLayout.hist0 (LightLocalCoverInit.base cover) h
  histR := LightLocalCoverLayout.hist1 (LightLocalCoverInit.base cover) h

theorem header_reads {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J cut occ i j code : ℕ} {shift : ℤ}
    (HP : SourceBandPairData.Stored μ fB fC pair NL NR g p (modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NL NR g h J cut occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (hi : i<BandPartition.size NL g) (hj : j<BandPartition.size NR g)
    (hk : code<LightBlockSourceCatalog.count h J) :
    HeaderReads μ (retained pair bank cover NL NR g h J cut occ i j code)
      pair bank cover i j code := by
  obtain ⟨hL,_,hR,_⟩ := SourceBandPairSlices.heads_read HP
  obtain ⟨hfirst,_,hspan,_,hocc⟩ := HB.heads_read
  have hLi : i<SourceBandPairSlices.count NL NR g := hi.trans_le (le_max_left _ _)
  have hRj : j<SourceBandPairSlices.count NL NR g := hj.trans_le (le_max_right _ _)
  have HL := HP.left i hi
  have HR := HP.right j hj
  have BL := HB.banks i hLi code hk
  have BR := HB.banks j hRj code hk
  refine ⟨hL,hR,hfirst,hspan,hocc,HL.headStart,HL.headLength,HL.headOffsets,HL.headFlat,
    HR.headStart,HR.headLength,HR.headOffsets,HR.headFlat,?_,?_,?_,?_,?_,?_⟩
  · exact BL.headerLeft
  · exact BR.headerRight
  · simpa [retained,LightLocalCoverInit.values,LightLocalParameters.values,
      LightLocalCounts.values,LightLocalCoverMetadata.values]
      using HC.header.getD (i := 12) (by simp [LightLocalCoverInit.values,
        LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values]) 0
  · simpa [retained,LightLocalCoverInit.values,LightLocalParameters.values,
      LightLocalCounts.values,LightLocalCoverMetadata.values]
      using HC.header.getD (i := 13) (by simp [LightLocalCoverInit.values,
        LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values]) 0
  · simpa [retained,LightLocalCoverInit.values,LightLocalParameters.values,
      LightLocalCounts.values,LightLocalCoverMetadata.values]
      using HC.header.getD (i := 14) (by simp [LightLocalCoverInit.values,
        LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values]) 0
  · simpa [retained,LightLocalCoverInit.values,LightLocalParameters.values,
      LightLocalCounts.values,LightLocalCoverMetadata.values]
      using HC.header.getD (i := 15) (by simp [LightLocalCoverInit.values,
        LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values]) 0

theorem buckets {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J cut occ i j code : ℕ} {shift : ℤ}
    (HP : SourceBandPairData.Stored μ fB fC pair NL NR g p (modulus h J) shift)
    (hi : i<BandPartition.size NL g) (hj : j<BandPartition.size NR g) :
    let X := retained pair bank cover NL NR g h J cut occ i j code
    SourceBuckets.Stored μ (fun t => LightSourceResidues.key p (modulus h J) 0 (fB (X.startL+t)))
      X.sizeL (modulus h J) X.offsetsL X.flatL ∧
    SourceBuckets.Stored μ (fun t => LightSourceResidues.key p (modulus h J) shift (fC (X.startR+t)))
      X.sizeR (modulus h J) X.offsetsR X.flatR :=
  ⟨(HP.left i hi).buckets,(HP.right j hj).buckets⟩

theorem sources_decoded {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J occ i j output : ℕ} {shift : ℤ}
    (HB : SourceBandBankData.Stored μ fB fC bank NL NR g h J (LightBlockQuery.sourceCut h J) occ (p : ℤ) shift)
    (hi : i<BandPartition.size NL g) (hj : j<BandPartition.size NR g)
    (hk : output<localCount h^J) :
    let code := OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output
    let X := retained pair bank cover NL NR g h J (LightBlockQuery.sourceCut h J) occ i j code
    ReportingHostLevelData.Sources μ (p : ℤ) shift
      (BandRawA.finiteBandPositions NL g i) (BandRawA.finiteBandPositions NR g j)
      (fun t : Fin NL => fB t.val) (fun t : Fin NR => fC t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J)) X.stagesL X.stagesR := by
  have hLi : i<SourceBandPairSlices.count NL NR g := hi.trans_le (le_max_left _ _)
  have hRj : j<SourceBandPairSlices.count NL NR g := hj.trans_le (le_max_right _ _)
  exact ⟨(SourceBandFinite.decoded HB hLi hk).left,(SourceBandFinite.decoded HB hRj hk).right⟩

theorem occurrence_rows_decoded {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {pair bank cover NL NR g p h J cut occ i j output : ℕ} {shift : ℤ}
    (HB : SourceBandBankData.Stored μ fB fC bank NL NR g h J cut occ (p : ℤ) shift)
    (hk : output<localCount h^J) (t : ℕ) (ht : t<J) :
    let code := OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output
    let X := retained pair bank cover NL NR g h J cut occ i j code
    μ (occurrenceRow X code J+t)=
      (occurrenceIndices (BlockEncoding.outputOccurrences
        ((GlobalKeyEnumeration.globalRecords h J).getD output (outputDefault h J))) t : ℤ) := by
  have H := HB.rows _ (OutputDecodeOccurrenceCode.source_code_lt h J output) t ht
  rw [← BlockSourceOccurrenceOrder.row_coordinate ht,
    BlockSourceOccurrenceOrder.decoded_occurrences hk] at H
  exact H

theorem cover_input {μ : ℕ→ℤ} {pair bank cover NL NR g h J cut occ i j code : ℕ}
    (HC : LightCoverKeyData.Stored μ cover h J) :
    let X := retained pair bank cover NL NR g h J cut occ i j code
    BlockSourceCoverInput.Input μ h X.maps X.candidates X.histL X.histR :=
  BlockSourceCoverInput.of_cover HC.data HC.rows HC.indices

theorem program_meets_fits {lim : Limits} {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {d pair bank cover srcB srcC NL NR g p h J cut occ i j code dst : ℕ} {shift : ℤ}
    (HP : SourceBandPairData.Stored μ fB fC pair NL NR g p (modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NL NR g h J cut occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (hi : i<BandPartition.size NL g) (hj : j<BandPartition.size NR g)
    (hk : code<LightBlockSourceCatalog.count h J) (hw : (lim.space : ℤ)≤lim.word)
    (hs : Fits (retained pair bank cover NL NR g h J cut occ i j code)
      pair bank cover srcB srcC i j code J dst lim.space) :
    Meets lim LightReportingSourceSelect.program 0 d [pair,bank,cover,srcB,srcC,i,j,code,J,dst] μ 6000
      (fun result ν => result=(dst : ℤ) ∧
        SegN ν dst (values (retained pair bank cover NL NR g h J cut occ i j code) srcB srcC code J) ∧
        SameOutside μ ν dst 15) :=
  LightReportingSourceSelect.program_meets_fits _ (header_reads HP HB HC hi hj hk) hw hs

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {fB fC : ℕ→ℤ}
    {d pair bank cover srcB srcC NL NR g p h J cut occ i j code dst : ℕ} {shift : ℤ}
    (HP : SourceBandPairData.Stored μ fB fC pair NL NR g p (modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NL NR g h J cut occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (hi : i<BandPartition.size NL g) (hj : j<BandPartition.size NR g)
    (hk : code<LightBlockSourceCatalog.count h J) (hw : (lim.space : ℤ)≤lim.word)
    (hs : space (retained pair bank cover NL NR g h J cut occ i j code)
      pair bank cover srcB srcC i j code J dst≤lim.space) :
    Meets lim LightReportingSourceSelect.program 0 d [pair,bank,cover,srcB,srcC,i,j,code,J,dst] μ 6000
      (fun result ν => result=(dst : ℤ) ∧
        SegN ν dst (values (retained pair bank cover NL NR g h J cut occ i j code) srcB srcC code J) ∧
        SameOutside μ ν dst 15) :=
  LightReportingSourceSelect.program_meets _ (header_reads HP HB HC hi hj hk) hw hs

end ThreeSum.ReportingHostSourceSelectionStored
