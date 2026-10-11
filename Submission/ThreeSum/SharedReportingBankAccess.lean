import Submission.ThreeSum.SharedReportingBankHeader

/-! # Constant-time row addresses and original-output reporting interfaces -/

namespace ThreeSum.SharedReportingBankAccess

open Light GlobalEncoding BlockIndexedQuery OutputDecodeRecords
open SharedReportingBankRows SharedReportingBankHeader SharedReportingBankLevels
open SharedReportingBankData SharedReportingBankSources

set_option maxHeartbeats 2000000
set_option maxRecDepth 12000

def slot (NB NC g s i j : ℕ) : ℕ :=
  rank (BandPartition.size NB g) (BandPartition.size NC g) s i j
def recordAt (free J NB NC g s i j : ℕ) : ℕ :=
  rowRecord (records free) (levels J) (slot NB NC g s i j)
def payloadAt (free h J NB NC g s i j : ℕ) : ℕ :=
  rowBase (payload free h J NB NC g) h J (levels J) (slot NB NC g s i j)
def levelCatalog (free h J NB NC g s i j k : ℕ) : ReportingHostLevelData.Catalog :=
  catalogAt (payloadAt free h J NB NC g s i j) h J k

theorem header_reads {μ : ℕ → ℤ} {free h J NB NC g : ℕ} {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift) :
    μ free=(records free : ℤ) ∧ μ (free+1)=(payload free h J NB NC g : ℤ) ∧
    μ (free+2)=(levels J : ℤ) ∧ μ (free+3)=(LightBlockSourceCatalog.count h J : ℤ) ∧
    μ (free+4)=(BandPartition.size NB g : ℤ) ∧ μ (free+5)=(BandPartition.size NC g : ℤ) ∧
    μ (free+6)=(SharedReportingBankHeader.finish free h J NB NC g : ℤ) ∧
    μ (free+7)=(SharedReportingBankLayout.localChoose h : ℤ) ∧
    μ (free+8)=(SharedReportingBankLayout.localPairs h : ℤ) := by
  exact ⟨by simpa [SegN,header] using H.heads.getD (i := 0) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 1) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 2) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 3) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 4) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 5) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 6) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 7) (by simp [SegN,header]) 0,
    by simpa [SegN,header] using H.heads.getD (i := 8) (by simp [SegN,header]) 0⟩

theorem record_end {free h J NB NC g s i j : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    recordAt free J NB NC g s i j+5*levels J ≤ payload free h J NB NC g := by
  have hr := rank_lt hs hi hj
  have hh := Nat.mul_le_mul_left (5*levels J) (show
    rank (BandPartition.size NB g) (BandPartition.size NC g) s i j+1 ≤ total h J NB NC g by exact hr)
  unfold recordAt slot rowRecord payload
  nlinarith

theorem row_end {free h J NB NC g s i j : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    baseAt (payloadAt free h J NB NC g s i j) h J (levels J) ≤
      SharedReportingBankHeader.finish free h J NB NC g := by
  unfold payloadAt
  rw [rowBase_next]
  exact rowBase_mono _ h J (levels J) (rank_lt hs hi hj)

theorem level_end {free h J NB NC g s i j k : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J) :
    (levelCatalog free h J NB NC g s i j k).indexBase+LightReportingPrefixCatalog.count h k ≤
      SharedReportingBankHeader.finish free h J NB NC g ∧
    (levelCatalog free h J NB NC g s i j k).ptrBase+LightReportingPrefixCatalog.count h k ≤
      SharedReportingBankHeader.finish free h J NB NC g ∧
    (levelCatalog free h J NB NC g s i j k).boxBase+LightReportingPrefixCatalog.count h k*
      LightReportingSuffixCatalog.stride ((J-k)*(512*h)) (levelCatalog free h J NB NC g s i j k).boxCut ≤
      SharedReportingBankHeader.finish free h J NB NC g := by
  have hend := catalog_end (payloadAt free h J NB NC g s i j) h J k
  have hbefore := (baseAt_mono (payloadAt free h J NB NC g s i j) h J
    (show k+1 ≤ levels J from hk)).trans (row_end hs hi hj)
  exact ⟨hend.1.trans hbefore,hend.2.1.trans hbefore,hend.2.2.trans hbefore⟩

theorem entry {μ : ℕ → ℤ} {free h J NB NC g s i j k : ℕ} {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J) (hkJ : k ≤ J) :
    Entry μ (recordAt free J NB NC g s i j+5*k) (levelCatalog free h J NB NC g s i j k) hkJ
      (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (BlockSourceOccurrenceOrder.representative h J s))
      (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (BlockSourceOccurrenceOrder.representative h J s)) := by
  obtain ⟨hk',Hk⟩ := H.row hs hi hj k hk
  exact Hk

theorem bounds {source free h J NB NC g s i j k stop : ℕ}
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J)
    (hsource : SourceBandBankData.finish source NB NC g h J (2*h*J) ≤ free)
    (hstop : SharedReportingBankHeader.finish free h J NB NC g ≤ stop) :
    ReportingHostLevelData.Bounds h J k (levelCatalog free h J NB NC g s i j k)
      (leftBase source h J (2*h*J) i s) (rightBase source h J (2*h*J) j s) stop := by
  have hl := source_bounds (base := source) (NB := NB) (NC := NC) (cut := 2*h*J)
    (hi.trans_le (le_max_left _ _)) hs
  have hr := source_bounds (base := source) (NB := NB) (NC := NC) (cut := 2*h*J)
    (hj.trans_le (le_max_right _ _)) hs
  have hf : free ≤ stop := (Nat.le_add_right free 9).trans
    ((records_le_payload free h J NB NC g).trans ((payload_le_finish free h J NB NC g).trans hstop))
  have he := level_end (free := free) hs hi hj hk
  exact ⟨hl.2.2.1.trans (hsource.trans hf),hr.2.2.2.trans (hsource.trans hf),
    he.1.trans hstop,he.2.1.trans hstop,he.2.2.trans hstop⟩

theorem original {μ : ℕ → ℤ} {free h J NB NC g output i j k : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : SharedReportingBankHeader.Stored μ free h J NB NC g fB fC p shift)
    (houtput : output < localCount h^J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hk : k < levels J) (hkJ : k ≤ J) :
    let s := OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output
    SegN μ (recordAt free J NB NC g s i j+5*k) ((levelCatalog free h J NB NC g s i j k).record h k) ∧
    ReportingHostLevelData.Stored μ (levelCatalog free h J NB NC g s i j k) hkJ p shift
      (BandRawA.finiteBandPositions NB g i) (BandRawA.finiteBandPositions NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD output (OutputDecodeRecords.outputDefault h J)) := by
  have hs : OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J output <
      LightBlockSourceCatalog.count h J := OutputDecodeOccurrenceCode.source_code_lt h J output
  have Hk := entry H hs hi hj hk hkJ
  refine ⟨Hk.header,?_⟩
  simpa only [SourceBandFinite.source_eq_finiteBandPositions] using
    reporting_decoded p shift (SourceBandPartition.source NB g i) (SourceBandPartition.source NC g j)
      (fun t : Fin NB => fB t.val) (fun t : Fin NC => fC t.val) houtput Hk

end ThreeSum.SharedReportingBankAccess
