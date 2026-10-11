import Submission.ThreeSum.OutputDecodeOccurrenceCode
import Submission.ThreeSum.BlockSourceSharing

/-!
# Exact source-bank order and reuse by decoded global outputs

A source-bank row is the big-endian radix expansion of its physical index.
Its representative carries a fixed legal output subset solely to reuse the
original source definitions. No output-subset choice enters the stored row
or the source function. The actual global-output decoder supplies exactly
the bank index needed by a query.
-/

namespace ThreeSum.BlockSourceOccurrenceOrder

open GlobalEncoding BlockEncoding BlockCoefficientRows OutputDecodeOrder
open OutputDecodeRecords OutputDecodeOccurrenceCode GlobalKeyEnumeration

def occurrences (h J k : ℕ) : Occurrences h J := fun j =>
  ⟨(indices (scheduleSize h) J k).getD j.val 0,indices_getD_lt (schedule_pos h) j.isLt⟩

def representative (h J k : ℕ) : GlobalOutput h J :=
  fun j => (occurrences h J k j,(blockDefault h).2)

@[simp] theorem outputOccurrences_representative (h J k : ℕ) :
    outputOccurrences (representative h J k) = occurrences h J k := rfl

theorem row_coordinate {h J k j : ℕ} (hj : j < J) :
    occurrenceIndices (outputOccurrences (representative h J k)) j =
      (indices (scheduleSize h) J k).getD j 0 := by
  rw [occurrenceIndices_fin _ ⟨j,hj⟩]
  rfl

theorem decoded_occurrences {h J k : ℕ} (hk : k < localCount h^J) :
    outputOccurrences (representative h J (code (scheduleSize h) (layerCount h) J k)) =
      outputOccurrences ((globalRecords h J).getD k (outputDefault h J)) := by
  funext j
  apply Fin.ext
  change (indices (scheduleSize h) J (code (scheduleSize h) (layerCount h) J k)).getD j.val 0 = _
  rw [source_code_coordinate h J k j.isLt]
  exact (original_occurrence_index hk j).symm

theorem leftSource_decoded {β : Type*} [Fintype β] [DecidableEq β]
    {h J k : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (hk : k < localCount h^J) :
    BlockIndexedQuery.leftSource P B b
      (representative h J (code (scheduleSize h) (layerCount h) J k)) =
    BlockIndexedQuery.leftSource P B b ((globalRecords h J).getD k (outputDefault h J)) :=
  BlockSourceSharing.leftSource_eq_of_occurrences P B b (decoded_occurrences hk)

theorem rightSource_decoded {β : Type*} [Fintype β] [DecidableEq β]
    {h J k : ℕ} (P d : ℤ) (B : Finset β) (b : β → ℤ) (hk : k < localCount h^J) :
    BlockIndexedQuery.rightSource P d B b
      (representative h J (code (scheduleSize h) (layerCount h) J k)) =
    BlockIndexedQuery.rightSource P d B b ((globalRecords h J).getD k (outputDefault h J)) :=
  BlockSourceSharing.rightSource_eq_of_occurrences P d B b (decoded_occurrences hk)

end ThreeSum.BlockSourceOccurrenceOrder
