import Submission.ThreeSum.SubsetStages
import Submission.ThreeSum.SparseBoxes

/-!
# Canonical sparse boxes as stored prefix-zeta stages

A global coordinate prefix intersects each flagged set in an initial
segment. Storing those initialCoords stages uses only a polynomial factor more
than the compact downset. The resulting entries are exactly the signed
box sums used by the sparse-query partition.
-/

namespace ThreeSum.BoxStages

open Finset

def initialCoords (L j : ℕ) : Finset (Fin L) := univ.filter fun a => a.val < j

@[simp] theorem mem_prefix {L j : ℕ} (a : Fin L) : a ∈ initialCoords L j ↔ a.val < j := by
  simp [initialCoords]

@[simp] theorem prefix_zero (L : ℕ) : initialCoords L 0 = ∅ := by
  ext a
  simp

@[simp] theorem prefix_all (L : ℕ) : initialCoords L L = univ := by
  ext a
  simp only [mem_prefix,mem_univ,iff_true]
  exact a.isLt

def nextCoord {L : ℕ} (j : ℕ) (hj : j < L) : Fin L := ⟨j,hj⟩

theorem nextCoord_not_mem {L j : ℕ} (hj : j < L) : nextCoord j hj ∉ initialCoords L j := by
  simp [nextCoord]

theorem prefix_succ {L j : ℕ} (hj : j < L) :
    initialCoords L (j+1) = insert (nextCoord j hj) (initialCoords L j) := by
  ext a
  simp only [mem_prefix,Finset.mem_insert,Fin.ext_iff,nextCoord]
  omega

def stageValue {L : ℕ} (f : Finset (Fin L) → ℤ) (j : ℕ) : Finset (Fin L) → ℤ :=
  Subset.partialZeta (initialCoords L j) f

@[simp] theorem stageValue_zero {L : ℕ} (f : Finset (Fin L) → ℤ) : stageValue f 0 = f := by
  funext S
  simp [stageValue,Subset.partialZeta_empty]

theorem stageValue_succ {L j : ℕ} (f : Finset (Fin L) → ℤ) (hj : j < L) :
    stageValue f (j+1) = Subset.zetaStep (nextCoord j hj) (stageValue f j) := by
  funext S
  rw [stageValue,prefix_succ hj]
  exact Subset.partialZeta_insert f S (initialCoords L j) (nextCoord j hj) (nextCoord_not_mem hj)

@[simp] theorem stageValue_all {L : ℕ} (f : Finset (Fin L) → ℤ) :
    stageValue f L = Subset.zeta f := by
  funext S
  have he : S \ univ = (∅ : Finset (Fin L)) := by ext a; simp
  simp [stageValue,Subset.partialZeta,Subset.zeta,he]

theorem stageValue_abs_le {L cut U : ℕ} (f : Finset (Fin L) → ℤ)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ U) :
    ∀ j ≤ L, ∀ S, S.card ≤ cut → |stageValue f j S| ≤ ((2^j*U : ℕ) : ℤ) := by
  intro j
  induction j with
  | zero =>
    intro hj S hS
    simpa only [stageValue_zero,pow_zero,one_mul] using hf S hS
  | succ j ih =>
    intro hj S hS
    have hjL : j < L := by omega
    have h₁ := ih (by omega) S hS
    have h₂ := ih (by omega) (S.erase (nextCoord j hjL))
      (Subset.zetaStep_stays_in_downset S (nextCoord j hjL) cut hS)
    have hdouble : ((2^(j+1)*U : ℕ) : ℤ) =
        ((2^j*U : ℕ) : ℤ)+((2^j*U : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ]
      ring
    rw [stageValue_succ f hjL,Subset.zetaStep,hdouble]
    split
    · exact (abs_add_le _ _).trans (add_le_add h₁ h₂)
    · exact h₁.trans (by have hn : (0 : ℤ) ≤ ((2^j*U : ℕ) : ℤ) := Int.natCast_nonneg _; omega)

theorem partialZeta_eq_boxSum {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (flags processed : Finset (Fin L)) :
    Subset.partialZeta processed weight flags =
      SparseBoxes.boxSum flags (flags ∩ processed) weight := by
  have hrequired : flags \ (flags ∩ processed) = flags \ processed := by
    ext a
    simp only [mem_sdiff,mem_inter]
    tauto
  unfold Subset.partialZeta SparseBoxes.boxSum
  rw [hrequired,← Finset.sum_filter]
  apply Finset.sum_bij (fun x _ => (flags \ processed) ∪ x)
  · intro x hx
    have hsub := Finset.mem_powerset.mp hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_powerset.mpr ?_,Finset.subset_union_left⟩
    exact Finset.union_subset Finset.sdiff_subset (hsub.trans Finset.inter_subset_left)
  · intro x hx y hy he
    have hxp := (Finset.mem_powerset.mp hx).trans Finset.inter_subset_right
    have hyp := (Finset.mem_powerset.mp hy).trans Finset.inter_subset_right
    ext a
    constructor
    · intro ha
      have he' : a ∈ (flags \ processed) ∪ y := he ▸ Finset.mem_union_right _ ha
      rcases Finset.mem_union.mp he' with hh | hh
      · exact False.elim ((Finset.mem_sdiff.mp hh).2 (hxp ha))
      · exact hh
    · intro ha
      have he' : a ∈ (flags \ processed) ∪ x := he.symm ▸ Finset.mem_union_right _ ha
      rcases Finset.mem_union.mp he' with hh | hh
      · exact False.elim ((Finset.mem_sdiff.mp hh).2 (hyp ha))
      · exact hh
  · intro leaf hl
    obtain ⟨hleaf,hrequired⟩ := Finset.mem_filter.mp hl
    have hlf := Finset.mem_powerset.mp hleaf
    refine ⟨leaf ∩ processed,Finset.mem_powerset.mpr ?_,?_⟩
    · intro a ha
      exact Finset.mem_inter.mpr ⟨hlf (Finset.mem_inter.mp ha).1,(Finset.mem_inter.mp ha).2⟩
    · ext a
      simp only [mem_union,mem_sdiff,mem_inter]
      constructor
      · rintro (⟨haf,hap⟩ | ⟨hal,hap⟩)
        · exact hrequired (Finset.mem_sdiff.mpr ⟨haf,hap⟩)
        · exact hal
      · intro hal
        by_cases hap : a ∈ processed
        · exact Or.inr ⟨hal,hap⟩
        · exact Or.inl ⟨hlf hal,hap⟩
  · intro x hx
    rfl

theorem stageValue_eq_boxSum {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (j : ℕ) (flags : Finset (Fin L)) :
    stageValue weight j flags = SparseBoxes.boxSum flags (flags ∩ initialCoords L j) weight :=
  partialZeta_eq_boxSum weight flags (initialCoords L j)

theorem queryFree_prefix {L : ℕ} (q u : Finset (Fin L)) (hu : u.Nonempty) :
    SparseBoxes.queryFree q u = (q \ u) ∩ initialCoords L (u.min' hu).val := by
  rw [SparseBoxes.queryFree_eq_filter_min q u hu]
  ext a
  simp only [mem_filter,mem_inter,mem_prefix]
  rfl

theorem query_box_stage {L : ℕ} (weight : Finset (Fin L) → ℤ)
    (q u : Finset (Fin L)) (hu : u.Nonempty) :
    SparseBoxes.boxSum (q \ u) (SparseBoxes.queryFree q u) weight =
      stageValue weight (u.min' hu).val (q \ u) := by
  rw [queryFree_prefix q u hu,stageValue_eq_boxSum]

end ThreeSum.BoxStages
