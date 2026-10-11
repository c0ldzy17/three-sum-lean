import Submission.ThreeSum.BlockMaskLayout
import Submission.ThreeSum.QueryCoordinates

/-!
# Exact next-block masks for the reporting host

The machine enumerates subsets directly in the global row-major ground set.
This file identifies those subsets with the balanced next-row children of
the original reporting tree, and proves the arithmetic mask transitions.
-/

namespace ThreeSum.ReportingHostMasks

open Finset BlockRows BlockIndex BlockIndexedQuery BlockMaskLayout
open ThreeSum.SubsetAddress StoredReporting BlockForced

def blockSet {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) : Finset (Fin (J*L)) :=
  indexSet (join {i} (fun _ => S))

@[simp] theorem mem_blockSet {J L : ℕ} (i j : Fin J) (S : Finset (Fin L)) (x : Fin L) :
    coordEquiv J L ⟨j,x⟩ ∈ blockSet i S ↔ j = i ∧ x ∈ S := by
  simp [blockSet]

@[simp] theorem blockSet_card {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    (blockSet i S).card = S.card := by
  simp [blockSet,join_card]

@[simp] theorem blockSet_mask {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    subsetMask (blockSet i S) = 2^(i.val*L)*subsetMask S := by
  simp [blockSet,mask_join,rowMask]

@[simp] theorem blockSet_subset {J L : ℕ} (i : Fin J) (S T : Finset (Fin L)) :
    blockSet i S ⊆ blockSet i T ↔ S ⊆ T := by
  rw [blockSet,blockSet,indexSet_subset]
  constructor
  · intro h x hx
    exact (mem_join.mp (h (x := Sigma.mk i x) (mem_join.mpr ⟨by simp,hx⟩))).2
  · intro h ⟨j,x⟩ hx
    exact mem_join.mpr ⟨(mem_join.mp hx).1,h (mem_join.mp hx).2⟩

def localRow {J L : ℕ} (i : Fin J) (T : Finset (Fin (J*L))) : Finset (Fin L) :=
  row (unindexSet T) i

@[simp] theorem localRow_blockSet {J L : ℕ} (i : Fin J) (S : Finset (Fin L)) :
    localRow i (blockSet i S) = S := by
  simp [localRow,blockSet]

theorem blockSet_localRow {J L : ℕ} (i : Fin J) (Q : Finset (Fin L))
    {T : Finset (Fin (J*L))} (hT : T ⊆ blockSet i Q) : blockSet i (localRow i T) = T := by
  have hu : unindexSet T ⊆ join {i} (fun _ => Q) := by
    apply (indexSet_subset _ _).mp
    simpa only [index_unindex,blockSet] using hT
  have he : join {i} (fun _ => localRow i T) = unindexSet T := by
    ext ⟨j,x⟩
    simp only [mem_join,mem_singleton,localRow,mem_row]
    constructor
    · rintro ⟨rfl,hx⟩
      exact hx
    · intro hx
      have hj := (mem_join.mp (hu hx)).1
      have he : j = i := mem_singleton.mp hj
      exact ⟨he,by simpa only [he] using hx⟩
  exact (congrArg indexSet he).trans (index_unindex T)

def globalChildren {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :=
  QueryCoordinates.missingSets (blockSet i Q) h

def localChildren {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :=
  (globalChildren i Q h).map (localRow i)

@[simp] theorem globalChildren_length {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).length = Q.card.choose h := by
  simp [globalChildren]

theorem globalChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (globalChildren i Q h).Nodup := QueryCoordinates.missingSets_nodup _ _

theorem globalChildren_mem {J L : ℕ} (i : Fin J) (Q S : Finset (Fin L)) (h : ℕ) :
    blockSet i S ∈ globalChildren i Q h ↔ S ⊆ Q ∧ S.card = h := by
  simp [globalChildren,QueryCoordinates.missingSets_mem]

theorem localChildren_mem {J L : ℕ} (i : Fin J) (Q S : Finset (Fin L)) (h : ℕ) :
    S ∈ localChildren i Q h ↔ S ∈ RawReporting.childList Q h := by
  rw [RawReporting.mem_childList,Finset.mem_powersetCard]
  constructor
  · intro hs
    obtain ⟨T,hT,rfl⟩ := List.mem_map.mp hs
    have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
    have he := blockSet_localRow i Q ht.1
    have hc : (localRow i T).card = T.card := by
      simpa only [blockSet_card] using congrArg Finset.card he
    exact ⟨(blockSet_subset i _ _).mp (he.symm ▸ ht.1),hc.trans ht.2⟩
  · intro hs
    exact List.mem_map.mpr ⟨blockSet i S,(globalChildren_mem i Q S h).mpr hs,localRow_blockSet i S⟩

theorem localChildren_nodup {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).Nodup := by
  apply (globalChildren_nodup i Q h).map_on
  intro S hS T hT he
  have hs := (QueryCoordinates.missingSets_mem _ _ _).mp hS
  have ht := (QueryCoordinates.missingSets_mem _ _ _).mp hT
  rw [← blockSet_localRow i Q hs.1,← blockSet_localRow i Q ht.1,he]

@[simp] theorem localChildren_length {J L : ℕ} (i : Fin J) (Q : Finset (Fin L)) (h : ℕ) :
    (localChildren i Q h).length = Q.card.choose h := by
  simp [localChildren]

theorem mask_union {W : ℕ} (S T : Finset (Fin W)) (hd : Disjoint S T) :
    subsetMask (S ∪ T) = subsetMask S+subsetMask T := by
  simp only [MaskDifference.subsetMask_sum,Finset.sum_union hd]

theorem leftPrefix_step {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    leftPrefix (k+1) (Function.update u ⟨k,hk⟩ S) =
      leftPrefix k u ∪ blockSet ⟨k,hk⟩ S := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  simp only [leftPrefix,prefixLeft,mem_indexSet,mem_join,mem_prefixIndices,
    Finset.mem_union,mem_blockSet]
  by_cases he : i = ⟨k,hk⟩
  · subst i
    simp
  · have hv : i.val ≠ k := fun h => he (Fin.ext h)
    have hi : i.val < k+1 ↔ i.val < k := by omega
    simp [he,hi]

theorem prefix_disjoint_block {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) : Disjoint (leftPrefix k u) (blockSet ⟨k,hk⟩ S) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  obtain ⟨rfl,_⟩ := (mem_blockSet _ _ _ _).mp hy
  have hh := (mem_join.mp (mem_indexSet _ _ |>.mp hx)).1
  exact (by simp : (⟨k,hk⟩ : Fin J) ∉ prefixIndices J k) hh

theorem rightPrefix_step {J L k : ℕ} (Q u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    rightPrefix (k+1) Q (Function.update u ⟨k,hk⟩ S) =
      rightPrefix k Q u ∪ blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) := by
  have he : (fun i => Q i \ Function.update u ⟨k,hk⟩ S i) =
      Function.update (fun i => Q i \ u i) ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) := by
    funext i
    by_cases hi : i = ⟨k,hk⟩
    · subst i; simp
    · simp [hi]
  change leftPrefix (k+1) (fun i => Q i \ Function.update u ⟨k,hk⟩ S i) = _
  rw [he,leftPrefix_step]
  rfl

theorem leftMask_step {J L k : ℕ} (u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) :
    (subsetMask (leftPrefix k u) : ℤ)+(subsetMask (blockSet ⟨k,hk⟩ S) : ℤ) =
      (subsetMask (leftPrefix (k+1) (Function.update u ⟨k,hk⟩ S)) : ℤ) := by
  rw [leftPrefix_step,mask_union _ _ (prefix_disjoint_block u hk S)]
  simp

theorem rightMask_step {J L k : ℕ} (Q u : Fin J → Finset (Fin L)) (hk : k < J)
    (S : Finset (Fin L)) (hS : S ⊆ Q ⟨k,hk⟩) :
    (subsetMask (rightPrefix k Q u) : ℤ)+
      ((subsetMask (blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩)) : ℤ)-(subsetMask (blockSet ⟨k,hk⟩ S) : ℤ)) =
      (subsetMask (rightPrefix (k+1) Q (Function.update u ⟨k,hk⟩ S)) : ℤ) := by
  have hd := prefix_disjoint_block (fun i => Q i \ u i) hk (Q ⟨k,hk⟩ \ S)
  change Disjoint (rightPrefix k Q u) (blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S)) at hd
  have he : blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩ \ S) =
      blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩) \ blockSet ⟨k,hk⟩ S := by
    ext x
    obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
    simp only [mem_blockSet,Finset.mem_sdiff]
    tauto
  rw [rightPrefix_step,mask_union _ _ hd,he]
  push_cast
  rw [← MaskDifference.subsetMask_sdiff_int _ _ ((blockSet_subset _ _ _).mpr hS)]

theorem querySet_step {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    querySet (k+1) Q = querySet k Q \ blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩) := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  simp only [querySet,mem_indexSet,remaining,mem_join,Finset.mem_compl,mem_prefixIndices,
    Finset.mem_sdiff,mem_blockSet]
  constructor
  · rintro ⟨hi,ha⟩
    refine ⟨⟨by omega,ha⟩,?_⟩
    rintro ⟨he,_⟩
    have hv : i.val = k := congrArg Fin.val he
    omega
  · rintro ⟨⟨hi,ha⟩,hn⟩
    refine ⟨?_,ha⟩
    intro hh
    have he : i.val = k := by omega
    apply hn
    have he' : i = ⟨k,hk⟩ := Fin.ext he
    exact ⟨he',he' ▸ ha⟩

theorem blockSet_subset_query {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩) ⊆ querySet k Q := by
  intro x hx
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J L).surjective x
  obtain ⟨rfl,ha⟩ := (mem_blockSet _ _ _ _).mp hx
  simp only [querySet,mem_indexSet,remaining,mem_join,Finset.mem_compl,mem_prefixIndices]
  exact ⟨by simp,ha⟩

theorem queryMask_step {J L k : ℕ} (Q : Fin J → Finset (Fin L)) (hk : k < J) :
    (subsetMask (querySet k Q) : ℤ)-(rowMask Q ⟨k,hk⟩ : ℤ) =
      (subsetMask (querySet (k+1) Q) : ℤ) := by
  rw [querySet_step Q hk]
  have he : rowMask Q ⟨k,hk⟩ = subsetMask (blockSet ⟨k,hk⟩ (Q ⟨k,hk⟩)) := by
    simp [rowMask]
  rw [he]
  exact MaskDifference.subsetMask_sdiff_int _ _ (blockSet_subset_query Q hk)

theorem prefixRows_append {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k < J) (S : Finset (Fin L)) :
    prefixRows (J := J) (pre ++ [S]) = Function.update (prefixRows pre) ⟨k,hk⟩ S := by
  funext i
  by_cases hi : i.val < k
  · have hne : i ≠ ⟨k,hk⟩ := by
      intro he
      have hv : i.val = k := congrArg Fin.val he
      omega
    rw [Function.update_of_ne hne]
    simp only [prefixRows]
    rw [List.getElem?_append_left (l₁ := pre) (l₂ := [S]) (i := i.val) (by omega)]
  · by_cases he : i = ⟨k,hk⟩
    · subst i
      simp [prefixRows,hp]
    · have hv : k < i.val := by
        have hn : i.val ≠ k := fun h => he (Fin.ext h)
        omega
      rw [Function.update_of_ne he]
      simp only [prefixRows]
      rw [List.getElem?_append_right (l₁ := pre) (l₂ := [S]) (i := i.val) (by omega),hp]
      rw [List.getElem?_eq_none (by simp; omega),List.getElem?_eq_none (by omega)]

theorem validPrefix_append {h J k : ℕ} (q : GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (S : Finset (Fin (512*h))) (hS : S ⊆ outputRows q ⟨k,hk⟩ ∧ S.card = h) :
    ValidPrefix q (k+1) (pre ++ [S]) := by
  refine ⟨by simp [hp.1],?_⟩
  intro i hi
  rw [prefixRows_append pre hp.1 hk S]
  by_cases he : i = ⟨k,hk⟩
  · subst i
    simpa using hS
  · rw [Function.update_of_ne he]
    apply hp.2 i
    have hn : i.val ≠ k := fun h => he (Fin.ext h)
    omega

theorem localChild_validPrefix {h J k : ℕ} (q : GlobalEncoding.GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (S : Finset (Fin (512*h)))
    (hS : S ∈ localChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h) :
    ValidPrefix q (k+1) (pre ++ [S]) := by
  exact validPrefix_append q pre hp hk S
    (Finset.mem_powersetCard.mp (RawReporting.mem_childList.mp
      ((localChildren_mem _ _ _ _).mp hS)))

end ThreeSum.ReportingHostMasks
