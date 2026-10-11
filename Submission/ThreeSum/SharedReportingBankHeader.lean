import Submission.ThreeSum.SharedReportingBankRows
import Submission.ThreeSum.LightSwitchDepth

/-! # A retained header for the complete shared reporting catalog bank -/

namespace ThreeSum.SharedReportingBankHeader

open Light GlobalEncoding SharedReportingBankRows SharedReportingBankLevels
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1900000

def levels (J : ℕ) : ℕ := LightSwitchDepth.depth J+1
def records (free : ℕ) : ℕ := free+9
def payload (free h J NB NC g : ℕ) : ℕ :=
  records free+5*levels J*total h J NB NC g
def finish (free h J NB NC g : ℕ) : ℕ :=
  rowBase (payload free h J NB NC g) h J (levels J) (total h J NB NC g)
def header (free h J NB NC g : ℕ) : List ℕ :=
  [records free,payload free h J NB NC g,levels J,LightBlockSourceCatalog.count h J,
    BandPartition.size NB g,BandPartition.size NC g,finish free h J NB NC g,
    localChoose h,localPairs h]

theorem levels_pos (J : ℕ) : 0 < levels J := by unfold levels; omega
theorem records_le_payload (free h J NB NC g : ℕ) :
    records free ≤ payload free h J NB NC g := Nat.le_add_right _ _
theorem payload_le_finish (free h J NB NC g : ℕ) :
    payload free h J NB NC g ≤ finish free h J NB NC g := Nat.le_add_right _ _
theorem header_length (free h J NB NC g : ℕ) : (header free h J NB NC g).length=9 := rfl

theorem levels_of_after {μ ν : ℕ → ℤ} {record base h J K low : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g) (heq : ∀ a, low ≤ a → ν a=μ a)
    (hrecord : low ≤ record) (hbase : low ≤ base) : Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hlo := catalog_low base h J k
  refine ⟨hkJ,⟨?_,Hk.tables.of_after heq (hbase.trans hlo.1)
    (hbase.trans hlo.2.1) (hbase.trans hlo.2.2)⟩⟩
  intro i hi
  exact (heq _ (by omega)).trans (Hk.header i hi)

theorem done_of_after {μ ν : ℕ → ℤ} {record base h J K NB NC g processed low : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Done μ record base h J K NB NC g processed fB fC p shift)
    (heq : ∀ a, low ≤ a → ν a=μ a) (hrecord : low ≤ record) (hbase : low ≤ base) :
    Done ν record base h J K NB NC g processed fB fC p shift := by
  intro s hs i hi j hj hr
  exact levels_of_after (H s hs i hi j hj hr) heq
    (hrecord.trans (Nat.le_add_right _ _)) (hbase.trans (Nat.le_add_right _ _))

theorem levels_of_kept {μ ν : ℕ → ℤ} {record base h J K bound : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ}
    (H : Built μ record base h J K f g) (heq : Kept μ ν bound)
    (hrecord : record+5*K ≤ bound) (hbase : baseAt base h J K ≤ bound) :
    Built ν record base h J K f g := by
  intro k hk
  obtain ⟨hkJ,Hk⟩ := H k hk
  have hend := catalog_end base h J k
  have hbefore := (baseAt_mono base h J (show k+1 ≤ K by omega)).trans hbase
  refine ⟨hkJ,Hk.of_kept heq (by omega) (hend.1.trans hbefore)
    (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩

structure Stored (μ : ℕ → ℤ) (free h J NB NC g : ℕ) (fB fC : ℕ → ℤ) (p shift : ℤ) : Prop where
  heads : SegN μ free (header free h J NB NC g)
  rows : Done μ (records free) (payload free h J NB NC g) h J (levels J) NB NC g
    (total h J NB NC g) fB fC p shift

theorem Stored.of_kept {μ ν : ℕ → ℤ} {free h J NB NC g bound : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift) (heq : Kept μ ν bound)
    (hbound : finish free h J NB NC g ≤ bound) : Stored ν free h J NB NC g fB fC p shift := by
  have hmeta := (records_le_payload free h J NB NC g).trans
    ((payload_le_finish free h J NB NC g).trans hbound)
  refine ⟨?_,?_⟩
  · intro i hi
    have hi' : i < 9 := by simpa [SegN,header] using hi
    exact (heq _ (by unfold records at hmeta; omega)).trans (H.heads i hi)
  · intro s hs i hi j hj hr
    have Hrow := H.rows s hs i hi j hj hr
    apply levels_of_kept Hrow heq
    · have hh := Nat.mul_le_mul_left (5*levels J) (show
        rank (BandPartition.size NB g) (BandPartition.size NC g) s i j+1 ≤ total h J NB NC g by omega)
      have hp := (payload_le_finish free h J NB NC g).trans hbound
      unfold rowRecord payload at *
      nlinarith
    · rw [rowBase_next]
      exact (rowBase_mono _ h J (levels J) (show
        rank (BandPartition.size NB g) (BandPartition.size NC g) s i j+1 ≤ total h J NB NC g by omega)).trans hbound

theorem Stored.row {μ : ℕ → ℤ} {free h J NB NC g s i j : ℕ}
    {fB fC : ℕ → ℤ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) :
    Built μ (rowRecord (records free) (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      (rowBase (payload free h J NB NC g) h J (levels J) (rank (BandPartition.size NB g) (BandPartition.size NC g) s i j))
      h J (levels J)
      (BlockIndexedQuery.leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val)
        (BlockSourceOccurrenceOrder.representative h J s))
      (BlockIndexedQuery.rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val)
        (BlockSourceOccurrenceOrder.representative h J s)) :=
  H.rows s hs i hi j hj (rank_lt hs hi hj)

end ThreeSum.SharedReportingBankHeader
