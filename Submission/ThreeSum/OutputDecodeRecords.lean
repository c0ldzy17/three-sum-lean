import Submission.ThreeSum.OutputDecodeOrder
import Submission.ThreeSum.BlockCoefficientRows

/-! # A physical global-record index decodes to the original occurrence and mask rows -/

namespace ThreeSum.OutputDecodeRecords

open GlobalEncoding GlobalKeyEnumeration LocalHashMoments LocalCoverBounds
open OutputDecodeOrder RadixKeyLists

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def layerCount (h : ℕ) : ℕ := outputCount (512*h) h
def localCount (h : ℕ) : ℕ := scheduleSize h*layerCount h

theorem layerCount_pos (h : ℕ) : 0 < layerCount h := Nat.choose_pos (by omega)
theorem schedule_pos (h : ℕ) : 0 < scheduleSize h := by
  unfold scheduleSize scheduleLength
  positivity

theorem localCount_pos (h : ℕ) : 0 < localCount h := Nat.mul_pos (schedule_pos h) (layerCount_pos h)

def blockDefault (h : ℕ) : OutputBlock h :=
  (⟨0,schedule_pos h⟩,layerRecord h ⟨0,layerCount_pos h⟩)

def outputDefault (h J : ℕ) : GlobalOutput h J := fun _ => blockDefault h

theorem localRecords_getD {h i : ℕ} (hi : i < localCount h) :
    (localRecords h).getD i (blockDefault h) =
      (⟨i/layerCount h,(Nat.div_lt_iff_lt_mul (layerCount_pos h)).mpr hi⟩,
        layerRecord h ⟨i%layerCount h,Nat.mod_lt _ (layerCount_pos h)⟩) := by
  have hq : i/layerCount h < scheduleSize h := (Nat.div_lt_iff_lt_mul (layerCount_pos h)).mpr hi
  have hr : i%layerCount h < layerCount h := Nat.mod_lt _ (layerCount_pos h)
  have hidx : i/layerCount h*layerCount h+i%layerCount h=i := by
    simpa only [Nat.mul_comm] using Nat.div_add_mod i (layerCount h)
  have hocc : (List.finRange (scheduleSize h)).getD (i/layerCount h) (blockDefault h).1 =
      ⟨i/layerCount h,hq⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_finRange] using hq)]
    apply Fin.ext
    simp
  have hmask : (layers h).getD (i%layerCount h) (blockDefault h).2 =
      layerRecord h ⟨i%layerCount h,hr⟩ := by
    rw [List.getD_eq_getElem _ _ (by simpa only [layers_length,layerCount] using hr)]
    simp only [layers,List.getElem_ofFn]
  unfold localRecords List.product
  conv_lhs => rw [← hidx]
  rw [getD_flatMap_uniform _ _ (layerCount h) (by simp [layers_length,layerCount])
    (blockDefault h).1 (blockDefault h) (by simpa only [List.length_finRange] using hq) hr]
  rw [hocc,List.getD_map_of_lt _ (by simpa only [layers_length,layerCount] using hr) (blockDefault h).2 (blockDefault h),hmask]

def localIndex (h J k j : ℕ) : ℕ := (indices (localCount h) J k).getD j 0
def occurrenceIndex (h J k j : ℕ) : ℕ := localIndex h J k j/layerCount h
def maskIndex (h J k j : ℕ) : ℕ := localIndex h J k j%layerCount h

theorem localIndex_lt {h J k j : ℕ} (hj : j < J) : localIndex h J k j < localCount h :=
  indices_getD_lt (localCount_pos h) hj

theorem occurrenceIndex_lt {h J k j : ℕ} (hj : j < J) :
    occurrenceIndex h J k j < scheduleSize h :=
  (Nat.div_lt_iff_lt_mul (layerCount_pos h)).mpr (localIndex_lt hj)

theorem maskIndex_lt (h J k j : ℕ) : maskIndex h J k j < layerCount h :=
  Nat.mod_lt _ (layerCount_pos h)

theorem globalRecords_map_ofFn (h J : ℕ) :
    (globalRecords h J).map List.ofFn = tuples (localRecords h) J := by
  simp [globalRecords,List.map_map,Function.comp_def,ofFn_tupleOfList]

theorem globalRecords_length' (h J : ℕ) : (globalRecords h J).length=localCount h^J := by
  rw [globalRecords_length]
  simp only [localCount,layerCount,mul_pow]

theorem globalRecords_getD_ofFn {h J k : ℕ} (hk : k < localCount h^J) :
    List.ofFn ((globalRecords h J).getD k (outputDefault h J)) =
      (tuples (localRecords h) J).getD k [] := by
  have hi : k < (globalRecords h J).length := by rwa [globalRecords_length']
  have he := List.getD_map_of_lt (fun q : GlobalOutput h J => List.ofFn q) hi (outputDefault h J) []
  rw [globalRecords_map_ofFn] at he
  exact he.symm

theorem global_record_block {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    ((globalRecords h J).getD k (outputDefault h J)) j =
      (localRecords h).getD (localIndex h J k j.val) (blockDefault h) := by
  have hs : List.ofFn ((globalRecords h J).getD k (outputDefault h J)) =
      (indices (localCount h) J k).map (fun i => (localRecords h).getD i (blockDefault h)) := by
    rw [globalRecords_getD_ofFn hk]
    have he := tuples_getD_indices (localRecords h) (blockDefault h)
      (by simpa only [localRecords_length,localCount,layerCount] using localCount_pos h) J k
      (by simpa only [localRecords_length,localCount,layerCount] using hk)
    simpa only [localRecords_length,localCount,layerCount] using he
  have hc := congrArg (fun xs : List (OutputBlock h) => xs.getD j.val (blockDefault h)) hs
  have hleft : (List.ofFn ((globalRecords h J).getD k (outputDefault h J))).getD j.val (blockDefault h) =
      ((globalRecords h J).getD k (outputDefault h J)) j := by
    rw [List.getD_eq_getElem _ _ (by simpa only [List.length_ofFn] using j.isLt)]
    simp only [List.getElem_ofFn]
  rw [hleft,List.getD_map_of_lt _ (by rw [indices_length]; exact j.isLt) 0 (blockDefault h)] at hc
  exact hc

theorem original_occurrence_index {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    (((globalRecords h J).getD k (outputDefault h J)) j).1.val = occurrenceIndex h J k j.val := by
  rw [global_record_block hk j,localRecords_getD (localIndex_lt j.isLt)]
  rfl

theorem original_output_mask {h J k : ℕ} (hk : k < localCount h^J) (j : Fin J) :
    SubsetAddress.subsetMask ((((globalRecords h J).getD k (outputDefault h J)) j).2.val) =
      LocalMaskGraph.maskAt (512*h) (2*h) (maskIndex h J k j.val) := by
  rw [global_record_block hk j,localRecords_getD (localIndex_lt j.isLt)]
  exact LocalMaskGraph.subsetMask_setAt (maskIndex_lt h J k j.val)

theorem source_occurrence_index {h J k j : ℕ} (hk : k < localCount h^J) (hj : j < J) :
    BlockCoefficientRows.occurrenceIndices
      (BlockEncoding.outputOccurrences ((globalRecords h J).getD k (outputDefault h J))) j =
        occurrenceIndex h J k j := by
  rw [BlockCoefficientRows.occurrenceIndices_fin _ ⟨j,hj⟩]
  exact original_occurrence_index hk ⟨j,hj⟩

theorem original_global_key {h J k : ℕ} (hk : k < localCount h^J) :
    (globalKeys h J).getD k 0 =
      globalKey ((globalRecords h J).getD k (outputDefault h J)) := by
  rw [globalKeys_eq_map]
  exact List.getD_map_of_lt _ (by rwa [globalRecords_length']) (outputDefault h J) 0

end ThreeSum.OutputDecodeRecords
