import Submission.ThreeSum.BandRawAIndex
import Submission.ThreeSum.BandWeightedScore

/-!
# Each physical A incidence retains exactly its owner's B/C product

The products in this file are mathematical counting domains. The actual
catalog is still constructed by the verified quadratic owner loop and
linear band copies. Distinct owner products are disjoint because their
physical A incidence indices differ, even when their values coincide.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 1900000
set_option maxRecDepth 8000

def aIndices (n g : ℕ) (rs : List Record) (s : ℕ) : Finset ℕ :=
  (range (row n g s (rs.getD s default)).length).image (fun j => count n g rs s+j)

def bandPositions (n g a : ℕ) : Finset ℕ :=
  (range (bandLength n g a)).image (fun j => BandPartition.start g a+j)

def ownerProduct (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  aIndices nA g rs s ×ˢ (bandPositions nB g (rs.getD s default).b ×ˢ
    bandPositions nC g (rs.getD s default).c)

def allProducts (nA nB nC g : ℕ) (rs : List Record) : Finset (ℕ × ℕ × ℕ) :=
  (range rs.length).biUnion (ownerProduct nA nB nC g rs)

theorem bandLength_eq_score_length (n g a : ℕ) :
    bandLength n g a=BandWeightedScore.length n g a :=
  (BandWeightedScore.length_eq_partition n g a).symm

theorem mem_aIndices {n g s k : ℕ} {rs : List Record} :
    k ∈ aIndices n g rs s ↔
      ∃ j < (row n g s (rs.getD s default)).length, k=count n g rs s+j := by
  constructor
  · intro hk
    obtain ⟨j,hj,he⟩ := mem_image.mp hk
    exact ⟨j,mem_range.mp hj,he.symm⟩
  · rintro ⟨j,hj,he⟩
    exact mem_image.mpr ⟨j,mem_range.mpr hj,he.symm⟩

theorem mem_aIndices_iff_owner {n g s k : ℕ} {rs : List Record} (hs : s < rs.length) :
    k ∈ aIndices n g rs s ↔
      k < (items n g rs).length ∧ (labelAt n g rs k).owner=s := by
  constructor
  · intro hk
    obtain ⟨j,hj,rfl⟩ := mem_aIndices.mp hk
    exact ⟨index_lt_items hs hj,by rw [items_getD hs hj]⟩
  · rintro ⟨hk,ho⟩
    obtain ⟨t,ht,j,hj,he⟩ := items_index hk
    have heLabel := items_getD ht hj
    rw [← he] at heLabel
    have hts : t=s := by simpa only [heLabel] using ho
    subst t
    exact mem_aIndices.mpr ⟨j,hj,he⟩

theorem mem_bandPositions {n g a p : ℕ} :
    p ∈ bandPositions n g a ↔
      BandPartition.start g a ≤ p ∧ p < BandPartition.stop n g a := by
  constructor
  · intro hp
    obtain ⟨j,hj,rfl⟩ := mem_image.mp hp
    have hj' : j < bandLength n g a := mem_range.mp hj
    unfold bandLength at hj'
    omega
  · rintro ⟨hs,he⟩
    exact mem_image.mpr ⟨p-BandPartition.start g a,
      mem_range.mpr (by unfold bandLength; omega),by omega⟩

theorem bandPositions_lt {n g a p : ℕ} (hp : p ∈ bandPositions n g a) : p < n :=
  (mem_bandPositions.mp hp).2.trans_le (BandPartition.stop_le n g a)

theorem mem_ownerProduct {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) :
    t ∈ ownerProduct nA nB nC g rs s ↔
      t.1 < (items nA g rs).length ∧ (labelAt nA g rs t.1).owner=s ∧
        t.2.1 ∈ bandPositions nB g (rs.getD s default).b ∧
        t.2.2 ∈ bandPositions nC g (rs.getD s default).c := by
  simp only [ownerProduct,mem_product,mem_aIndices_iff_owner hs,and_assoc]

theorem ownerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hst : s ≠ t) :
    Disjoint (ownerProduct nA nB nC g rs s) (ownerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro x hx hy
  have hs' := (mem_ownerProduct hs).mp hx
  have ht' := (mem_ownerProduct ht).mp hy
  exact hst (hs'.2.1.symm.trans ht'.2.1)

theorem mem_allProducts {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ} :
    t ∈ allProducts nA nB nC g rs ↔
      t.1 < (items nA g rs).length ∧
        t.2.1 ∈ bandPositions nB g (ownerRecord nA g rs t.1).b ∧
        t.2.2 ∈ bandPositions nC g (ownerRecord nA g rs t.1).c := by
  constructor
  · intro ht
    obtain ⟨s,hs,hp⟩ := mem_biUnion.mp ht
    obtain ⟨hi,ho,hb,hc⟩ := (mem_ownerProduct (mem_range.mp hs)).mp hp
    refine ⟨hi,?_,?_⟩
    · simpa only [ownerRecord,ho] using hb
    · simpa only [ownerRecord,ho] using hc
  · rintro ⟨hi,hb,hc⟩
    have hs := (at_bounds hi).1
    apply mem_biUnion.mpr
    refine ⟨(labelAt nA g rs t.1).owner,mem_range.mpr hs,?_⟩
    exact (mem_ownerProduct hs).mpr ⟨hi,rfl,hb,hc⟩

theorem sum_aIndices (F : ℕ → ℕ) (n g : ℕ) (rs : List Record) (s : ℕ) :
    (∑ k ∈ aIndices n g rs s, F k)=
      ∑ j ∈ range (row n g s (rs.getD s default)).length, F (count n g rs s+j) := by
  unfold aIndices
  exact sum_image (fun i _ j _ he => by omega)

theorem sum_bandPositions (F : ℕ → ℕ) (n g a : ℕ) :
    (∑ p ∈ bandPositions n g a, F p)=
      ∑ j ∈ range (bandLength n g a), F (BandPartition.start g a+j) := by
  unfold bandPositions
  exact sum_image (fun i _ j _ he => by omega)

theorem sum_ownerProduct (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) (s : ℕ) :
    (∑ t ∈ ownerProduct nA nB nC g rs s, F t)=
      ∑ i ∈ range (row nA g s (rs.getD s default)).length,
        ∑ j ∈ range (bandLength nB g (rs.getD s default).b),
          ∑ k ∈ range (bandLength nC g (rs.getD s default).c),
            F (count nA g rs s+i,
              BandPartition.start g (rs.getD s default).b+j,
              BandPartition.start g (rs.getD s default).c+k) := by
  rw [ownerProduct,sum_product,sum_aIndices]
  apply sum_congr rfl
  intro i hi
  rw [sum_product,sum_bandPositions]
  apply sum_congr rfl
  intro j hj
  exact sum_bandPositions _ _ _ _

theorem sum_allProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ t ∈ allProducts nA nB nC g rs, F t)=
      ∑ s ∈ range rs.length, ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by
  unfold allProducts
  apply sum_biUnion
  intro s hs t ht hst
  exact ownerProduct_disjoint (mem_range.mp hs) (mem_range.mp ht) hst

/-- Every relevant original owner contributes all coordinates of its
actual band product. The returned A index is the physical flattened one. -/
theorem relevant_product_complete {A B C : BandEnumeration.Family}
    {nA nB nC g pA pB pC : ℕ} (t : BandEnumeration.Triple A B C)
    (ht : BandEnumeration.relevant A B C t)
    (ha : BandPartition.start g t.1.val ≤ pA ∧ pA < BandPartition.stop nA g t.1.val)
    (hb : BandPartition.start g t.2.1.val ≤ pB ∧ pB < BandPartition.stop nB g t.2.1.val)
    (hc : BandPartition.start g t.2.2.val ≤ pC ∧ pC < BandPartition.stop nC g t.2.2.val) :
    ∃ k < (items nA g (records A B C)).length,
      labelAt nA g (records A B C) k=⟨slot A B C (BandEnumeration.owner A B C t),pA⟩ ∧
      (k,pB,pC) ∈ ownerProduct nA nB nC g (records A B C)
        (slot A B C (BandEnumeration.owner A B C t)) := by
  have hlabel := owner_covers t ht ha.1 ha.2
  obtain ⟨k,hk,he⟩ := List.mem_iff_getElem.mp hlabel
  have heLabel : labelAt nA g (records A B C) k=
      ⟨slot A B C (BandEnumeration.owner A B C t),pA⟩ := by
    rw [labelAt,List.getD_eq_getElem _ _ hk,he]
  have hs : slot A B C (BandEnumeration.owner A B C t) < (records A B C).length := by
    rw [records_length]
    exact slot_lt A B C _
  have hr := BandCandidateRows.owner_covers A B C t ht
  refine ⟨k,hk,heLabel,(mem_ownerProduct hs).mpr ⟨hk,?_,?_,?_⟩⟩
  · rw [heLabel]
  · apply mem_bandPositions.mpr
    simpa only [hr,fromTriple] using hb
  · apply mem_bandPositions.mpr
    simpa only [hr,fromTriple] using hc

end ThreeSum.BandRawA
