import Submission.ThreeSum.ReportingHostPrefixMasks
import Submission.ThreeSum.ReportingHostPairSegments

/-!
# Complete shared prefix records in the physical product-constructor order

The semantic list is obtained from the actual tuple list, without filtering,
reordering, or coalescing equal left/right projections. It connects both
constructed integer arrays to every exact global prefix-mask pair.
-/

namespace ThreeSum.ReportingHostPrefixOrder

open ThreeSum.SubsetAddress ReportingHostPrefixCatalog ReportingHostPairEnumeration
open ReportingHostPrefixMasks ReportingHostPairSegments

set_option maxHeartbeats 600000

/-- The exact record order shared by both physical positional products. -/
def prefixes (h k : ℕ) : List (Prefix h k) :=
  (RadixKeyLists.tuples (pairs (512*h) h) k).attach.map fun t =>
    ofTuple t.val ((RadixKeyLists.mem_tuples _ _ _).mp t.property).1
      ((RadixKeyLists.mem_tuples _ _ _).mp t.property).2

theorem prefixes_length (h k : ℕ) :
    (prefixes h k).length = ((512*h).choose (2*h)*(2*h).choose h)^k := by
  simp only [prefixes,List.length_map,List.length_attach,RadixKeyLists.tuples_length,pairs_length]

theorem prefixes_tuple (h k : ℕ) :
    (prefixes h k).map tuple = RadixKeyLists.tuples (pairs (512*h) h) k := by
  unfold prefixes
  simp only [List.map_map,Function.comp_def,tuple_ofTuple]
  simp

theorem mem_prefixes {h k : ℕ} (p : Prefix h k) : p ∈ prefixes h k := by
  have hm : tuple p ∈ (prefixes h k).map tuple := by
    rw [prefixes_tuple]
    exact tuple_mem p
  obtain ⟨q,hq,he⟩ := List.mem_map.mp hm
  exact (tuple_injective he) ▸ hq

theorem prefixes_nodup (h k : ℕ) : (prefixes h k).Nodup := by
  apply List.Nodup.of_map
  rw [prefixes_tuple]
  exact RadixKeyLists.tuples_nodup _ (pairs_nodup _ _) _

def leftSets (h J k : ℕ) : List (Finset (Fin (J*(512*h)))) :=
  (prefixes h k).map (leftSet (J := J))

def rightSets (h J k : ℕ) : List (Finset (Fin (J*(512*h)))) :=
  (prefixes h k).map (rightSet (J := J))

def preL (h J k i : ℕ) : Finset (Fin (J*(512*h))) := ((leftSets h J k)[i]?).getD ∅
def preR (h J k i : ℕ) : Finset (Fin (J*(512*h))) := ((rightSets h J k)[i]?).getD ∅

theorem left_values {h J k : ℕ} (hk : k ≤ J) :
    RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ) (leftMasks (512*h) h) k =
      (leftSets h J k).map (fun S => (subsetMask S : ℤ)) := by
  rw [leftMasks,RadixKeyLists.values_eq_map,← prefixes_tuple]
  simp only [List.map_map,leftSets,Function.comp_def,leftHash_eq_mask hk]

theorem right_values {h J k : ℕ} (hk : k ≤ J) :
    RadixKeyLists.values ((2^(512*h) : ℕ) : ℤ) (rightMasks (512*h) h) k =
      (rightSets h J k).map (fun S => (subsetMask S : ℤ)) := by
  rw [rightMasks,RadixKeyLists.values_eq_map,← prefixes_tuple]
  simp only [List.map_map,rightSets,Function.comp_def,rightHash_eq_mask hk]

theorem preL_get {h J k i : ℕ} (hi : i < (prefixes h k).length) :
    preL h J k i = leftSet (J := J) (prefixes h k)[i] := by
  simp only [preL,leftSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem preR_get {h J k i : ℕ} (hi : i < (prefixes h k).length) :
    preR h J k i = rightSet (J := J) (prefixes h k)[i] := by
  simp only [preR,rightSets,List.getElem?_map,List.getElem?_eq_getElem hi,Option.map_some,
    Option.getD_some]

theorem preL_card {h J k i : ℕ} (hk : k ≤ J) (hi : i < (prefixes h k).length) :
    (preL h J k i).card = k*h := by rw [preL_get hi]; exact leftSet_card hk _

theorem preR_card {h J k i : ℕ} (hk : k ≤ J) (hi : i < (prefixes h k).length) :
    (preR h J k i).card = k*h := by rw [preR_get hi]; exact rightSet_card hk _

theorem exists_index {h J k : ℕ} (p : Prefix h k) :
    ∃ i < (prefixes h k).length, preL h J k i = leftSet (J := J) p ∧
      preR h J k i = rightSet (J := J) p := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (mem_prefixes p)
  exact ⟨i,hi,by rw [preL_get hi,he],by rw [preR_get hi,he]⟩

theorem maskPair_unique {h J k i j : ℕ} (hk : k ≤ J)
    (hi : i < (prefixes h k).length) (hj : j < (prefixes h k).length)
    (hL : subsetMask (preL h J k i) = subsetMask (preL h J k j))
    (hR : subsetMask (preR h J k i) = subsetMask (preR h J k j)) : i=j := by
  rw [preL_get hi,preL_get hj] at hL
  rw [preR_get hi,preR_get hj] at hR
  have he := maskPair_injective hk (Prod.ext hL hR)
  exact (prefixes_nodup h k).getElem_inj_iff.mp he

end ThreeSum.ReportingHostPrefixOrder
