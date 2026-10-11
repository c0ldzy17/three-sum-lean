import Submission.ThreeSum.BlockIndex
import Submission.ThreeSum.StoredReporting
import Submission.ThreeSum.SubsetTransport
import Submission.ThreeSum.SubsetStages
import Mathlib.Data.Fintype.Fin

/-!
# Exact bridge from row-major machine masks to the block reporting query

The explicit coordinate equivalence sends the remaining blocks to a
contiguous suffix. Transport of finite subset sums identifies the machine's
Möbius value with the concrete forced-prefix count used by reporting.
-/

namespace ThreeSum.BlockIndexedQuery

open Finset BlockRows BlockIndex BlockForced BlockEncoding GlobalEncoding
open LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open scoped BigOperators

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

@[simp] theorem prefixIndices_card {J k : ℕ} (hk : k ≤ J) :
    (prefixIndices J k).card = k := by
  simpa only [prefixIndices,Nat.min_eq_right hk] using (Fin.card_filter_val_lt (n := J) (m := k))

def suffixStage (J L k : ℕ) : ℕ := (J-k)*L

theorem suffixStage_le (J L k : ℕ) : suffixStage J L k ≤ J*L :=
  Nat.mul_le_mul_right L (Nat.sub_le _ _)

theorem index_suffixDomain {J L k : ℕ} (hk : k ≤ J) :
    indexSet (suffixDomain (L := L) (prefixIndices J k)) =
      SubsetStages.suffix (J*L) (suffixStage J L k) := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  have hsub : J*L-(J-k)*L = k*L := by
    rw [← Nat.sub_mul,Nat.sub_sub_self hk]
  simp only [mem_indexSet,suffixDomain,mem_join,Finset.mem_compl,mem_prefixIndices,
    Finset.mem_univ,and_true,not_lt,SubsetStages.mem_suffix,suffixStage,coordEquiv_val,hsub]
  constructor
  · intro h
    exact (Nat.mul_le_mul_right L h).trans (Nat.le_add_right _ _)
  · intro h
    by_contra hn
    have hi : i.val+1 ≤ k := by omega
    have hm := Nat.mul_le_mul_right L hi
    simp only [Nat.succ_mul] at hm
    have ha := a.isLt
    omega

def leftPrefix {J L : ℕ} (k : ℕ) (u : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (prefixLeft (prefixIndices J k) u)

def rightPrefix {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (prefixRight (prefixIndices J k) Q u)

def querySet {J L : ℕ} (k : ℕ) (Q : Fin J → Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (remaining (prefixIndices J k) Q)

theorem leftPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (leftPrefix k u) (querySet k Q) := by
  exact (Finset.disjoint_map _).mpr (join_disjoint_compl (prefixIndices J k) u Q)

theorem rightPrefix_disjoint_query {J L : ℕ} (k : ℕ) (Q u : Fin J → Finset (Fin L)) :
    Disjoint (rightPrefix k Q u) (querySet k Q) := by
  exact (Finset.disjoint_map _).mpr
    (join_disjoint_compl (prefixIndices J k) (fun i => Q i \ u i) Q)

theorem querySet_subset_suffix {J L k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L)) :
    querySet k Q ⊆ SubsetStages.suffix (J*L) (suffixStage J L k) := by
  rw [← index_suffixDomain hk]
  exact (indexSet_subset _ _).mpr (join_subset _ (fun _ _ => Finset.subset_univ _))

theorem leftPrefix_card {J L h k : ℕ} (hk : k ≤ J) (u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ prefixIndices J k, (u i).card = h) : (leftPrefix k u).card = k*h := by
  rw [leftPrefix,indexSet_card,prefixLeft,join_card_of_balance _ _ hu,prefixIndices_card hk]

theorem rightPrefix_card {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (rightPrefix k Q u).card = k*h := by
  have hc : ∀ i ∈ prefixIndices J k, (Q i \ u i).card = h := by
    intro i hi
    rw [Finset.card_sdiff_of_subset (hu i hi).1,hQ i,(hu i hi).2]
    omega
  rw [rightPrefix,indexSet_card,prefixRight,join_card_of_balance _ _ hc,prefixIndices_card hk]

theorem querySet_card {J L h k : ℕ} (hk : k ≤ J) (Q : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h) : (querySet k Q).card = (J-k)*(2*h) := by
  rw [querySet,indexSet_card,remaining,join_card_of_balance _ _ (fun i _ => hQ i),
    Finset.card_compl,Fintype.card_fin,prefixIndices_card hk]

private theorem sizes_le {J h k : ℕ} (hk : k ≤ J) : k*h+(J-k)*(2*h) ≤ 2*h*J := by
  calc
    _ ≤ k*(2*h)+(J-k)*(2*h) :=
      Nat.add_le_add_right (Nat.mul_le_mul_left k (by omega)) _
    _ = (k+(J-k))*(2*h) := (Nat.add_mul _ _ _).symm
    _ = _ := by rw [Nat.add_sub_of_le hk]; ring

theorem left_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, (u i).card = h) :
    (leftPrefix k u ∪ querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (leftPrefix_disjoint_query k Q u),
    leftPrefix_card hk u hu,querySet_card hk Q hQ]
  exact sizes_le hk

theorem right_union_card_le {J L h k : ℕ} (hk : k ≤ J) (Q u : Fin J → Finset (Fin L))
    (hQ : ∀ i, (Q i).card = 2*h)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ Q i ∧ (u i).card = h) :
    (rightPrefix k Q u ∪ querySet k Q).card ≤ 2*h*J := by
  rw [Finset.card_union_of_disjoint (rightPrefix_disjoint_query k Q u),
    rightPrefix_card hk Q u hQ hu,querySet_card hk Q hQ]
  exact sizes_le hk

section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftSource {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h))
    (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ))

def rightSource {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (q : GlobalOutput h J) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h))
    (fun S => (rightWeights (outputOccurrences q) P d C c S : ℤ))

theorem leftWeights_le_card {h J : ℕ} (o : Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (Coord J (512*h))) :
    leftWeights o P B b S ≤ B.card := by
  unfold leftWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ B, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem rightWeights_le_card {h J : ℕ} (o : Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (S : Finset (Coord J (512*h))) :
    rightWeights o P d C c S ≤ C.card := by
  unfold rightWeights
  split_ifs with ha
  · calc
      _ ≤ ∑ _j ∈ C, (1 : ℕ) := Finset.sum_le_sum (fun _ _ => by split_ifs <;> omega)
      _ = _ := by simp
  · omega

theorem leftSource_abs_le {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (S : Finset (Fin (J*(512*h)))) : |leftSource P B b q S| ≤ B.card := by
  unfold leftSource SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast leftWeights_le_card (outputOccurrences q) P B b _

theorem rightSource_abs_le {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (q : GlobalOutput h J) (S : Finset (Fin (J*(512*h)))) : |rightSource P d C c q S| ≤ C.card := by
  unfold rightSource SubsetTransport.reindex
  rw [Int.abs_natCast]
  exact_mod_cast rightWeights_le_card (outputOccurrences q) P d C c _

def queryValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (k : ℕ)
    (u : Fin J → Finset (Fin (512*h))) : ℤ :=
  Subset.mobius (fun S =>
    SubsetStages.stageValue (leftSource P B b q) (suffixStage J (512*h) k) (leftPrefix k u ∪ S) *
    SubsetStages.stageValue (rightSource P d C c q) (suffixStage J (512*h) k)
      (rightPrefix k (outputRows q) u ∪ S)) (querySet k (outputRows q))

theorem queryValue_eq_transformPrefixValue {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512*h))) (hk : k ≤ J) :
    queryValue P d B C b c q k u =
      transformPrefixValue P d B C b c q (prefixIndices J k) u := by
  unfold queryValue SubsetStages.stageValue
  rw [← index_suffixDomain hk]
  exact SubsetTransport.mobius_partial_product_map (coordEquiv J (512*h)) _ _ _ _ _ _

theorem queryValue_eq_bucket_sum {h J k : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512*h))) (hk : k ≤ J)
    (hu : ∀ i ∈ prefixIndices J k, u i ⊆ outputRows q i ∧ (u i).card = h) :
    queryValue P d B C b c q k u =
      (∑ t ∈ completedTuples q (prefixIndices J k) u,
        leftBucket P B b t * rightBucket P d C c t : ℕ) := by
  rw [queryValue_eq_transformPrefixValue P d B C b c q u hk]
  exact transformPrefixValue_eq_bucket_sum P d B C b c q _ u hu

end Histograms

end ThreeSum.BlockIndexedQuery
