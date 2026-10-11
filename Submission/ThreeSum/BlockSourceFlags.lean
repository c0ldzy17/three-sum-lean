import Submission.ThreeSum.BlockSourceRows
import Submission.ThreeSum.LightSourceTrim
import Submission.ThreeSum.LightLocalCoverSchedule

/-!
# Concrete trimming flags equal the original independent endpoint conditions

The exact greedy occurrence-to-candidate bridge connects retained candidate
bucket tables to the unchanged `mapAt` schedule. A product of row flags is
therefore exactly the original `LeftAllowed` or `RightAllowed` condition.
-/

namespace ThreeSum.BlockSourceFlags

open BlockRows BlockIndex BlockEncoding BlockCoefficientRows
open LocalHashMoments LocalCoverBounds GlobalEncoding

set_option maxHeartbeats 1200000

def candidateIndices (h s : ℕ) : ℕ := (LightLocalCoverSchedule.indices h).getD s 0

@[simp] theorem candidateIndices_fin (h : ℕ) (s : Occurrence h) :
    candidateIndices h s.val = LightLocalCoverSchedule.candidateAt h s := rfl

theorem candidateIndices_lt {h s : ℕ} (hs : s < scheduleSize h) :
    candidateIndices h s < LightLocalCoverSchedule.rows h :=
  LightLocalCoverSchedule.candidateAt_lt h ⟨s,hs⟩

def bits {J L : ℕ} (S : Finset (Coord J L)) : ℕ → ℕ :=
  LightMaskBits.bit (J*L) (SubsetAddress.subsetMask (indexSet S))

def leftCount (h k : ℕ) : ℕ → ℕ :=
  LocalCoverMatrix.leftCount (LightLocalCoverSchedule.candidate h k) h

def rightCount (h k : ℕ) : ℕ → ℕ :=
  LocalCoverMatrix.rightCount (LightLocalCoverSchedule.candidate h k) h

theorem mapRow_extend {h : ℕ} (s : Occurrence h) (b : Bool) :
    mapRow h b s.val = OneHotMask.extend (fun i => (mapAt h s (i,b)).val) := by
  simp only [mapRow,s.isLt,dite_true]

theorem left_row_iff {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) (j : Fin J) :
    LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
      (occurrenceIndices o) (candidateIndices h) (bits S)
      (mapRow h false) (mapRow h true) (leftCount h) j.val = 1 ↔
        (row S j).card=h ∧
        HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h (o j))
          (HashFamily.hashValue (mapAt h (o j)) (LocalGraph.leftWord (row S j))) ≤ localBucketCap h := by
  unfold LightSourceTrim.rowFlag LightSourceRowFlag.flag
  rw [occurrenceIndices_fin,candidateIndices_fin]
  change LightSourceFlagTest.flag (LightSourceRowScan.count (BlockSourceRows.bits S j) (512*h)) h
    (leftCount h (LightLocalCoverSchedule.candidateAt h (o j))
      (LightResidues.residue (localPrime h) 1
        (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h false (o j).val)
          (mapRow h true (o j).val) (512*h) : ℤ))) (localBucketCap h) = 1 ↔ _
  rw [LightSourceFlagTest.flag_eq_one,BlockSourceRows.count_eq_card]
  unfold leftCount
  rw [LightLocalCoverSchedule.leftCount_candidateAt h (o j)
    (LightResidues.residue_lt (localPrime_pos h) 1 _)]
  have he : ((LightResidues.residue (localPrime h) 1
      (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h false (o j).val)
        (mapRow h true (o j).val) (512*h) : ℤ) : ℕ) : LocalField h) =
      HashFamily.hashValue (mapAt h (o j)) (LocalGraph.leftWord (row S j)) := by
    rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
      mapRow_extend,mapRow_extend,BlockSourceRows.left_hash,GlobalEncoding.rawHash_cast]
  rw [he]

theorem right_row_iff {h J : ℕ} (o : Occurrences h J)
    (S : Finset (Coord J (512*h))) (j : Fin J) :
    LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
      (occurrenceIndices o) (candidateIndices h) (bits S)
      (mapRow h true) (mapRow h false) (rightCount h) j.val = 1 ↔
        (row S j).card=h ∧
        HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h (o j))
          (HashFamily.hashValue (mapAt h (o j)) (LocalGraph.rightWord (row S j))) ≤ localBucketCap h := by
  unfold LightSourceTrim.rowFlag LightSourceRowFlag.flag
  rw [occurrenceIndices_fin,candidateIndices_fin]
  change LightSourceFlagTest.flag (LightSourceRowScan.count (BlockSourceRows.bits S j) (512*h)) h
    (rightCount h (LightLocalCoverSchedule.candidateAt h (o j))
      (LightResidues.residue (localPrime h) 1
        (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h true (o j).val)
          (mapRow h false (o j).val) (512*h) : ℤ))) (localBucketCap h) = 1 ↔ _
  rw [LightSourceFlagTest.flag_eq_one,BlockSourceRows.count_eq_card]
  unfold rightCount
  rw [LightLocalCoverSchedule.rightCount_candidateAt h (o j)
    (LightResidues.residue_lt (localPrime_pos h) 1 _)]
  have he : ((LightResidues.residue (localPrime h) 1
      (LightSourceRowScan.hash (BlockSourceRows.bits S j) (mapRow h true (o j).val)
        (mapRow h false (o j).val) (512*h) : ℤ) : ℕ) : LocalField h) =
      HashFamily.hashValue (mapAt h (o j)) (LocalGraph.rightWord (row S j)) := by
    rw [LightResidueHistogram.residue_zmod (localPrime_pos h),one_mul,
      mapRow_extend,mapRow_extend,BlockSourceRows.right_hash,GlobalEncoding.rawHash_cast]
  rw [he]

theorem left_product {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) :
    SourceFlagProduct.product
      (LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
        (occurrenceIndices o) (candidateIndices h) (bits S)
        (mapRow h false) (mapRow h true) (leftCount h)) J =
      if LeftAllowed o S then 1 else 0 := by
  apply SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (left_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (left_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)

theorem right_product {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) :
    SourceFlagProduct.product
      (LightSourceTrim.rowFlag (512*h) h (localPrime h) (localBucketCap h)
        (occurrenceIndices o) (candidateIndices h) (bits S)
        (mapRow h true) (mapRow h false) (rightCount h)) J =
      if RightAllowed o S then 1 else 0 := by
  apply SourceFlagProduct.product_eq_indicator
  · exact fun _ _ => LightSourceTrim.rowFlag_le ..
  · constructor
    · intro hall j
      exact (right_row_iff o S j).mp (hall j.val j.isLt)
    · intro hall j hj
      exact (right_row_iff o S ⟨j,hj⟩).mpr (hall ⟨j,hj⟩)

end ThreeSum.BlockSourceFlags
