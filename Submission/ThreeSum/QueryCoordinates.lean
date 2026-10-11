import Submission.ThreeSum.LightWeightedEnumeration
import Submission.ThreeSum.MaskDifference
import Submission.ThreeSum.MaskDecode
import Mathlib.Data.List.Sublists
import Mathlib.Algebra.BigOperators.Fin

/-!
# Query-coordinate lists and weighted subset semantics

The coordinate list has one entry per set bit of the query. Its powers
form a compact weight table for the output-sensitive enumeration routine.
-/

namespace ThreeSum.QueryCoordinates

open Finset ThreeSum.SubsetAddress
open scoped BigOperators

/-- The selected coordinates among the first `j` scanned positions. -/
def positions {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) : List ℕ :=
  (List.range j).filter fun i => i ∈ natPositions Q

@[simp] theorem positions_zero {W : ℕ} (Q : Finset (Fin W)) : positions Q 0 = [] := by
  simp [positions]

theorem positions_succ {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    positions Q (j+1) = positions Q j ++ if j ∈ natPositions Q then [j] else [] := by
  by_cases h : j ∈ natPositions Q <;> simp [positions,List.range_succ,List.filter_append,h]

@[simp] theorem mem_positions {W : ℕ} (Q : Finset (Fin W)) (j i : ℕ) :
    i ∈ positions Q j ↔ i < j ∧ i ∈ natPositions Q := by
  simp [positions]

theorem positions_nodup {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (positions Q j).Nodup := List.nodup_range.filter _

theorem positions_length_le {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (positions Q j).length ≤ j := by
  exact (List.length_filter_le _ _).trans_eq List.length_range

@[simp] theorem positions_toFinset {W : ℕ} (Q : Finset (Fin W)) :
    (positions Q W).toFinset = natPositions Q := by
  ext i
  simp only [List.mem_toFinset,mem_positions,and_iff_right_iff_imp]
  exact fun hi => Finset.mem_range.mp (natPositions_subset Q hi)

@[simp] theorem positions_length {W : ℕ} (Q : Finset (Fin W)) :
    (positions Q W).length = Q.card := by
  rw [← List.toFinset_card_of_nodup (positions_nodup Q W),positions_toFinset,natPositions_card]

def selectedPowers {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) : List ℕ :=
  (positions Q j).map fun i => 2^i

@[simp] theorem selectedPowers_length {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    (selectedPowers Q j).length = (positions Q j).length := by simp [selectedPowers]

@[simp] theorem selectedPowers_zero {W : ℕ} (Q : Finset (Fin W)) :
    selectedPowers Q 0 = [] := by simp [selectedPowers]

theorem selectedPowers_succ {W : ℕ} (Q : Finset (Fin W)) (j : ℕ) :
    selectedPowers Q (j+1) =
      selectedPowers Q j ++ if j ∈ natPositions Q then [2^j] else [] := by
  rw [selectedPowers,positions_succ,List.map_append]
  split <;> simp [selectedPowers]

@[simp] theorem selectedPowers_sum {W : ℕ} (Q : Finset (Fin W)) :
    (selectedPowers Q W).sum = subsetMask Q := by
  rw [selectedPowers,← List.sum_toFinset _ (positions_nodup Q W),positions_toFinset]
  rfl

def weights {W : ℕ} (Q : Finset (Fin W)) (i : ℕ) : ℕ :=
  (selectedPowers Q W)[i]?.getD 0

theorem total_getD (xs : List ℕ) :
    LightWeightedEnumeration.total (fun i => xs[i]?.getD 0) xs.length = xs.sum := by
  unfold LightWeightedEnumeration.total
  rw [← Fin.sum_univ_eq_sum_range]
  simpa using Fin.sum_univ_getElem xs

@[simp] theorem total_weights {W : ℕ} (Q : Finset (Fin W)) :
    LightWeightedEnumeration.total (weights Q) Q.card = subsetMask Q := by
  rw [← positions_length Q,← selectedPowers_length Q W]
  exact (total_getD (selectedPowers Q W)).trans (selectedPowers_sum Q)

/-- Fixed-size sublists, interpreted as finite subsets. -/
def setLayer (xs : List ℕ) (k : ℕ) : List (Finset ℕ) :=
  (xs.sublistsLen k).map List.toFinset

@[simp] theorem setLayer_length (xs : List ℕ) (k : ℕ) :
    (setLayer xs k).length = xs.length.choose k := by
  simp [setLayer,List.length_sublistsLen]

theorem setLayer_nodup (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) :
    (setLayer xs k).Nodup := by
  apply (List.nodup_sublistsLen k hn).map_on
  intro a ha b hb he
  have ha' := (List.mem_sublistsLen.mp ha).1
  have hb' := (List.mem_sublistsLen.mp hb).1
  apply (hn.perm_iff_eq_of_sublist ha' hb').mp
  exact List.perm_of_nodup_nodup_toFinset_eq (hn.sublist ha') (hn.sublist hb') he

theorem mem_setLayer (xs : List ℕ) (hn : xs.Nodup) (k : ℕ) (s : Finset ℕ) :
    s ∈ setLayer xs k ↔ s ⊆ xs.toFinset ∧ s.card = k := by
  constructor
  · rintro hs
    obtain ⟨ys,hy,rfl⟩ := List.mem_map.mp hs
    obtain ⟨hys,hyk⟩ := List.mem_sublistsLen.mp hy
    refine ⟨?_,?_⟩
    · intro a ha
      exact List.mem_toFinset.mpr (hys.subset (List.mem_toFinset.mp ha))
    · rw [List.toFinset_card_of_nodup (hn.sublist hys),hyk]
  · rintro ⟨hs,hk⟩
    let ys := xs.filter fun i => i ∈ s
    have he : ys.toFinset = s := by
      ext i
      simp only [ys,List.mem_toFinset,List.mem_filter,decide_eq_true_eq]
      exact ⟨fun h => h.2,fun hi => ⟨List.mem_toFinset.mp (hs hi),hi⟩⟩
    apply List.mem_map.mpr
    refine ⟨ys,List.mem_sublistsLen.mpr ⟨List.filter_sublist,?_⟩,he⟩
    rw [← List.toFinset_card_of_nodup (hn.filter _),he,hk]

theorem output_eq_sublists (weight : ℕ → ℕ) (L k pref : ℕ) :
    LightWeightedEnumeration.output weight L k pref =
      (((List.range L).reverse).sublistsLen k).map
        (fun xs => ((pref+(xs.map weight).sum : ℕ) : ℤ)) := by
  induction L generalizing k pref with
  | zero => cases k <;> simp [LightWeightedEnumeration.output]
  | succ L ih =>
    cases k with
    | zero => simp [LightWeightedEnumeration.output]
    | succ k =>
      by_cases hk : k+1 ≤ L+1
      · rw [LightWeightedEnumeration.output_succ hk,ih,ih]
        simp [List.range_succ,List.reverse_append,List.sublistsLen_succ_cons,
          List.map_append,List.map_map,Function.comp_def,Nat.add_assoc]
      · rw [LightWeightedEnumeration.output_empty (by omega),List.sublistsLen_of_length_lt]
        · rfl
        · simp only [List.length_reverse,List.length_range]; omega

theorem output_congr {w v : ℕ → ℕ} {L : ℕ}
    (h : ∀ i, i < L → w i = v i) (k pref : ℕ) :
    LightWeightedEnumeration.output w L k pref =
      LightWeightedEnumeration.output v L k pref := by
  induction L generalizing k pref with
  | zero => cases k <;> rfl
  | succ L ih =>
    have hl : ∀ i, i < L → w i = v i := fun i hi => h i (by omega)
    have hh := h L (by omega)
    cases k with
    | zero => rfl
    | succ k => simp [LightWeightedEnumeration.output,ih hl,hh]

theorem sublistsLen_map (f : ℕ → ℕ) (xs : List ℕ) (k : ℕ) :
    (xs.map f).sublistsLen k = (xs.sublistsLen k).map (List.map f) := by
  induction xs generalizing k with
  | nil => cases k <;> simp
  | cons x xs ih =>
    cases k with
    | zero => simp
    | succ k =>
      simp [List.sublistsLen_succ_cons,ih,List.map_append,List.map_map,Function.comp_def]

theorem map_range_getD (xs : List ℕ) :
    (List.range xs.length).map (fun i => xs[i]?.getD 0) = xs := by
  apply List.ext_getElem
  · simp
  · intro i hi hi'
    simp [List.getElem?_eq_getElem,hi']

theorem output_coordinates (xs : List ℕ) (k pref : ℕ) :
    LightWeightedEnumeration.output (fun i => (xs.map fun a => 2^a)[i]?.getD 0)
        xs.length k pref =
      ((xs.reverse).sublistsLen k).map
        (fun ys => ((pref+(ys.map fun a => 2^a).sum : ℕ) : ℤ)) := by
  have hw : ∀ i, i < xs.length →
      (xs.map fun a => 2^a)[i]?.getD 0 = 2^(xs[i]?.getD 0) := by
    intro i hi
    simp [List.getElem?_eq_getElem,hi]
  rw [output_congr hw,output_eq_sublists]
  have hr : xs.reverse = ((List.range xs.length).reverse).map (fun i => xs[i]?.getD 0) := by
    rw [List.map_reverse,map_range_getD]
  rw [hr,sublistsLen_map,List.map_map]
  simp only [List.map_map,Function.comp_def]

def missingSets {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) : List (Finset (Fin W)) :=
  (setLayer (positions Q W).reverse k).map fun s => MaskDecode.decode W (maskOf s)

theorem decode_maskOf {W : ℕ} {s : Finset ℕ} (hs : s ⊆ range W) :
    natPositions (MaskDecode.decode W (maskOf s)) = s := by
  apply maskOf_injective
  exact MaskDecode.subsetMask_decode (maskOf_isMask hs).1

theorem missingSets_mem {W : ℕ} (Q U : Finset (Fin W)) (k : ℕ) :
    U ∈ missingSets Q k ↔ U ⊆ Q ∧ U.card = k := by
  have hn := (List.nodup_reverse.mpr (positions_nodup Q W))
  constructor
  · intro hu
    obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hu
    have hset := (mem_setLayer _ hn _ _).mp hs
    rw [List.toFinset_reverse,positions_toFinset] at hset
    have hr : s ⊆ range W := hset.1.trans (natPositions_subset Q)
    have he := decode_maskOf hr
    refine ⟨?_,?_⟩
    · intro a ha
      have hp : a.val ∈ s := by
        rw [← he]
        exact Finset.mem_map.mpr ⟨a,ha,rfl⟩
      obtain ⟨b,hb,hba⟩ := Finset.mem_map.mp (hset.1 hp)
      exact (Fin.ext hba : b = a) ▸ hb
    · rw [← natPositions_card,he,hset.2]
  · rintro ⟨hU,hk⟩
    apply List.mem_map.mpr
    refine ⟨natPositions U,?_,MaskDecode.decode_subsetMask U⟩
    apply (mem_setLayer _ hn _ _).mpr
    rw [List.toFinset_reverse,positions_toFinset,natPositions_card]
    exact ⟨Finset.map_subset_map.mpr hU,hk⟩

theorem missingSets_nodup {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (missingSets Q k).Nodup := by
  unfold missingSets
  apply (setLayer_nodup _ (List.nodup_reverse.mpr (positions_nodup Q W)) k).map_on
  intro a ha b hb he
  have has := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp ha
  have hbs := (mem_setLayer _ (List.nodup_reverse.mpr (positions_nodup Q W)) _ _).mp hb
  rw [List.toFinset_reverse,positions_toFinset] at has hbs
  have h := congrArg natPositions he
  rw [decode_maskOf (has.1.trans (natPositions_subset Q)),
      decode_maskOf (hbs.1.trans (natPositions_subset Q))] at h
  exact h

@[simp] theorem missingSets_length {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    (missingSets Q k).length = Q.card.choose k := by
  simp [missingSets]

theorem output_missingSets {W : ℕ} (Q : Finset (Fin W)) (k : ℕ) :
    LightWeightedEnumeration.output (weights Q) Q.card k 0 =
      ((missingSets Q k).map subsetMask).map Nat.cast := by
  rw [← positions_length Q]
  change LightWeightedEnumeration.output
    (fun i => ((positions Q W).map fun a => 2^a)[i]?.getD 0)
    (positions Q W).length k 0 = _
  rw [output_coordinates]
  simp only [missingSets,setLayer,List.map_map,Function.comp_def]
  apply List.map_congr_left
  intro ys hy
  have hs := (List.mem_sublistsLen.mp hy).1
  have hn := (List.nodup_reverse.mpr (positions_nodup Q W)).sublist hs
  have hb : ys.toFinset ⊆ range W := by
    intro a ha
    have hm := hs.subset (List.mem_toFinset.mp ha)
    have hq : a ∈ natPositions Q := (mem_positions Q W a).mp (List.mem_reverse.mp hm) |>.2
    exact natPositions_subset Q hq
  rw [MaskDecode.subsetMask_decode (maskOf_isMask hb).1]
  simp only [Nat.zero_add]
  congr 1
  exact (List.sum_toFinset (fun a => 2^a) hn).symm

end ThreeSum.QueryCoordinates
