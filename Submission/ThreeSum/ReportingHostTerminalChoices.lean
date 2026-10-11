import Submission.ThreeSum.ReportingHostPositive
import Submission.ThreeSum.BlockSourceBuckets

/-!
# Finite terminal completions in the actual mask enumerator's order

At any valid reporting prefix, a full balanced endpoint needs exactly
`(J-k)*h` of the remaining query coordinates. Enumerating that one layer
contains every retained completion and costs no more than the terminal
Boolean-cube allowance. The selected bucket pair masses sum to at most the
unchanged original raw prefix count.
-/

namespace ThreeSum.ReportingHostTerminalChoices

open Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open QueryCoordinates
open scoped BigOperators

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def choices {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Coord J (512*h))) :=
  (missingSets (querySet k (outputRows q)) ((J-k)*h)).map unindexSet

theorem choices_length {h J k : ℕ} (q : GlobalOutput h J) (hk : k≤J) :
    (choices q k).length = ((J-k)*(2*h)).choose ((J-k)*h) := by
  simp only [choices,List.length_map,missingSets_length]
  rw [querySet_card hk (outputRows q) (fun i => LayerCounts.mem_vertices.mp (q i).2.property)]

theorem choices_length_le {h J k : ℕ} (q : GlobalOutput h J) (hk : k≤J) :
    (choices q k).length ≤ 2^((J-k)*(2*h)) := by
  rw [choices_length q hk]
  exact Nat.choose_le_two_pow _ _

theorem choices_nodup {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : (choices q k).Nodup := by
  apply (missingSets_nodup _ _).map
  intro S T he
  simpa only [index_unindex] using congrArg indexSet he

theorem mem_choices {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (S : Finset (Coord J (512*h))) :
    S ∈ choices q k ↔ S ⊆ remaining (prefixIndices J k) (outputRows q) ∧ S.card=(J-k)*h := by
  constructor
  · rintro hS
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hS
    have ht := (missingSets_mem _ _ _).mp hT
    constructor
    · apply (indexSet_subset _ _).mp
      simpa only [index_unindex,querySet] using ht.1
    · simpa only [unindexSet,Finset.card_map] using ht.2
  · rintro ⟨hS,hcard⟩
    apply List.mem_map.mpr
    refine ⟨indexSet S,(missingSets_mem _ _ _).mpr ⟨?_,?_⟩,unindex_index S⟩
    · exact (indexSet_subset _ _).mpr hS
    · simpa only [indexSet_card] using hcard

theorem residual_card {h J k : ℕ} (t : ChoiceTuple h J) (hk : k≤J) :
    (residual (prefixIndices J k) t).card=(J-k)*h := by
  rw [BlockForced.residual,join_card_of_balance _ _ (fun i _ => (LocalGraph.edge_data (edge (t i))).1),
    Finset.card_compl,Fintype.card_fin,prefixIndices_card hk]

theorem completion_as_completed {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre) :
    completions q k pre=completedTuples q (prefixIndices J k) (prefixRows pre) := by
  rw [← completions_eq_completedTuples,take_prefixRows pre hp.1 hk]

theorem completion_residual_mem {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) :
    residual (prefixIndices J k) t ∈ choices q k := by
  apply (mem_choices q k _).mpr
  exact ⟨residual_subset q _ t (Finset.mem_filter.mp ht).2.1,residual_card t hk⟩

theorem completion_endpoints {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) :
    prefixLeft (prefixIndices J k) (prefixRows pre) ∪ residual (prefixIndices J k) t=leftSubset t ∧
      prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ residual (prefixIndices J k) t)=rightSubset t := by
  rw [completion_as_completed q pre hk hp] at ht
  exact ⟨forced_left_completion q _ _ t ht,
    forced_right_completion q _ _ (fun i hi => (hp.2 i (mem_prefixIndices.mp hi)).1) t ht⟩

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def pairMass {h J : ℕ} (P shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512*h)))) (S : Finset (Coord J (512*h))) : ℕ :=
  leftWeights (outputOccurrences q) P B b (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S)*
    rightWeights (outputOccurrences q) P shift C c
      (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
        (remaining (prefixIndices J k) (outputRows q) \ S))

theorem pairMass_sum_le_prefixQuery {h J k : ℕ} (P shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%P+lift w.2.1*P+shift)-globalKey w.2.2) :
    ((choices w.2.2 k).map (pairMass P shift B C b c w.2.2 k pre)).sum ≤
      prefixQuery (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w k pre := by
  rw [← List.sum_toFinset _ (choices_nodup w.2.2 k)]
  rw [prefixQuery_eq_bucketPrefixMass,bucketPrefixMass,if_pos hkey,
    completion_as_completed w.2.2 pre hk hp,
    completed_bucket_sum P shift B C b c w.2.2 _ _
      (fun i hi => (hp.2 i (mem_prefixIndices.mp hi)).1)]
  apply Finset.sum_le_sum_of_subset
  intro S hS
  exact Finset.mem_powerset.mpr ((mem_choices w.2.2 k S).mp (List.mem_toFinset.mp hS)).1

end ThreeSum.ReportingHostTerminalChoices
