import Submission.ThreeSum.ReportingHostPrefixCatalog
import Submission.ThreeSum.QueryCoordinates

/-!
# A direct ordered enumeration of every local balanced row pair

First enumerate the h-subsets, then enumerate h-subsets of each complement.
The list contains every edge exactly once and has the exact local catalog
size, without scanning the ambient Boolean cube or all pairs of vertices.
-/

namespace ThreeSum.ReportingHostPairEnumeration

open Finset ThreeSum.SubsetAddress LayerCounts LocalGraph

set_option linter.unusedSimpArgs false

def lefts (L h : ℕ) : List (Finset (Fin L)) := (enumerateLayer L h).map (MaskDecode.decode L)

def rights {L : ℕ} (S : Finset (Fin L)) (h : ℕ) : List (Finset (Fin L)) :=
  QueryCoordinates.missingSets (Finset.univ \ S) h

def pairs (L h : ℕ) : List (Finset (Fin L) × Finset (Fin L)) :=
  (lefts L h).flatMap fun S => (rights S h).map fun R => (S,R)

@[simp] theorem lefts_length (L h : ℕ) : (lefts L h).length = L.choose h := by
  simp [lefts,enumerateLayer_length]

theorem lefts_mem {L h : ℕ} (S : Finset (Fin L)) : S ∈ lefts L h ↔ S.card = h := by
  constructor
  · intro hS
    obtain ⟨m,hm,rfl⟩ := List.mem_map.mp hS
    exact MaskDecode.decode_card_layer hm
  · exact MaskDecode.decoded_layer_complete S

theorem lefts_nodup (L h : ℕ) : (lefts L h).Nodup := by
  apply (enumerateLayer_nodup L h).map_on
  intro a ha b hb he
  have hA := (mem_enumerateLayer L h a).mp ha
  have hB := (mem_enumerateLayer L h b).mp hb
  simpa only [MaskDecode.subsetMask_decode hA.1,MaskDecode.subsetMask_decode hB.1] using
    congrArg subsetMask he

theorem lefts_masks (L h : ℕ) : (lefts L h).map subsetMask = enumerateLayer L h := by
  apply List.ext_getElem
  · simp [lefts]
  · intro i hi hi'
    simp only [List.getElem_map,lefts,List.getElem_map]
    exact MaskDecode.subsetMask_decode ((mem_enumerateLayer L h _).mp (List.getElem_mem hi')).1

@[simp] theorem rights_mem {L h : ℕ} (S R : Finset (Fin L)) :
    R ∈ rights S h ↔ R.card = h ∧ Disjoint S R := by
  rw [rights,QueryCoordinates.missingSets_mem]
  constructor
  · intro h
    refine ⟨h.2,Finset.disjoint_left.mpr ?_⟩
    intro a haS haR
    exact (Finset.mem_sdiff.mp (h.1 haR)).2 haS
  · rintro ⟨hc,hd⟩
    refine ⟨?_,hc⟩
    intro a haR
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ a,fun haS => Finset.disjoint_left.mp hd haS haR⟩

theorem rights_length {L h : ℕ} (S : Finset (Fin L)) (hS : S.card = h) :
    (rights S h).length = (L-h).choose h := by
  simp [rights,Finset.card_sdiff_of_subset (Finset.subset_univ S),hS]

theorem rights_nodup {L : ℕ} (S : Finset (Fin L)) (h : ℕ) : (rights S h).Nodup :=
  QueryCoordinates.missingSets_nodup _ _

theorem pairs_mem {L h : ℕ} (p : Finset (Fin L) × Finset (Fin L)) :
    p ∈ pairs L h ↔ p ∈ edgeSet L h := by
  rw [LayerCounts.mem_edgeSet]
  constructor
  · intro hp
    obtain ⟨S,hS,hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨R,hR,rfl⟩ := List.mem_map.mp hp
    exact ⟨(lefts_mem S).mp hS,(rights_mem S R).mp hR⟩
  · rintro ⟨hS,hR,hd⟩
    exact List.mem_flatMap.mpr ⟨p.1,(lefts_mem p.1).mpr hS,
      List.mem_map.mpr ⟨p.2,(rights_mem p.1 p.2).mpr ⟨hR,hd⟩,rfl⟩⟩

theorem pairs_nodup (L h : ℕ) : (pairs L h).Nodup := by
  apply List.nodup_flatMap.mpr
  constructor
  · intro S _
    exact (rights_nodup S h).map (fun a b he => congrArg Prod.snd he)
  · exact (lefts_nodup L h).imp fun {S T} hST p hp hq => by
      obtain ⟨R,_,rfl⟩ := List.mem_map.mp hp
      obtain ⟨U,_,he⟩ := List.mem_map.mp hq
      exact hST (congrArg Prod.fst he).symm

theorem pairs_length (L h : ℕ) :
    (pairs L h).length = L.choose (2*h)*(2*h).choose h := by
  have hm : ((lefts L h).map (fun S => ((rights S h).map (fun R => (S,R))).length)) =
      List.replicate (lefts L h).length ((L-h).choose h) := by
    apply List.ext_getElem
    · simp
    · intro i hi hi'
      simp only [List.getElem_map,List.length_map,List.getElem_replicate]
      exact rights_length _ ((lefts_mem _).mp (List.getElem_mem (by simpa using hi)))
  calc
    (pairs L h).length = (((lefts L h).map fun S => ((rights S h).map fun R => (S,R)).length)).sum := by
      simp [pairs,List.length_flatMap]
    _ = (lefts L h).length*((L-h).choose h) := by rw [hm]; simp
    _ = L.choose h*(L-h).choose h := by rw [lefts_length]
    _ = L.choose (2*h)*(2*h).choose h := LayerCounts.vertex_degree_identity L h

def leftAt (L h i : ℕ) : Finset (Fin L) := ((lefts L h)[i]?).getD ∅

def rightAt (L h i j : ℕ) : Finset (Fin L) := ((rights (leftAt L h i) h)[j]?).getD ∅

theorem leftAt_eq_get {L h i : ℕ} (hi : i < L.choose h) :
    leftAt L h i = (lefts L h)[i]'(by simpa using hi) := by
  simp [leftAt,List.getElem?_eq_getElem,hi]

theorem leftAt_card {L h i : ℕ} (hi : i < L.choose h) : (leftAt L h i).card = h := by
  rw [leftAt_eq_get hi]
  exact (lefts_mem _).mp (List.getElem_mem _)

theorem rightAt_eq_get {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    rightAt L h i j = (rights (leftAt L h i) h)[j]'(by rw [rights_length _ (leftAt_card hi)]; exact hj) := by
  have hlen : j < (rights (leftAt L h i) h).length := by rw [rights_length _ (leftAt_card hi)]; exact hj
  simp [rightAt,List.getElem?_eq_getElem hlen]

theorem pairAt_mem {L h i j : ℕ} (hi : i < L.choose h) (hj : j < (L-h).choose h) :
    (leftAt L h i,rightAt L h i j) ∈ edgeSet L h := by
  rw [LayerCounts.mem_edgeSet]
  refine ⟨leftAt_card hi,?_⟩
  rw [rightAt_eq_get hi hj]
  exact (rights_mem _ _).mp (List.getElem_mem _)

theorem subsetMask_univ_succ (L : ℕ) : subsetMask (Finset.univ : Finset (Fin L))+1 = 2^L := by
  rw [MaskDifference.subsetMask_sum,Fin.sum_univ_eq_sum_range]
  induction L with
  | zero => simp
  | succ L ih =>
      rw [Finset.sum_range_succ,Nat.pow_succ]
      omega

theorem leftAt_mask {L h i : ℕ} (hi : i < L.choose h) :
    subsetMask (leftAt L h i) = (enumerateLayer L h)[i]'(by rw [enumerateLayer_length]; exact hi) := by
  have hiL : i < (lefts L h).length := by rw [lefts_length]; exact hi
  have hiE : i < (enumerateLayer L h).length := by rw [enumerateLayer_length]; exact hi
  have he := congrArg (fun xs : List ℕ => xs[i]?.getD 0) (lefts_masks L h)
  rw [leftAt_eq_get hi]
  simpa only [List.getElem?_map,List.getElem?_eq_getElem hiL,
    List.getElem?_eq_getElem hiE,Option.map_some,Option.getD_some] using he

end ThreeSum.ReportingHostPairEnumeration
