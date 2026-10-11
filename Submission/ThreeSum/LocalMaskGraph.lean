import Submission.ThreeSum.LightMaskBits
import Submission.ThreeSum.LightBooleanDot
import Submission.ThreeSum.LocalGraph
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Concrete integer indices for the local disjoint-subset graph

The finite list is the already checked layer-mask enumeration. Its Boolean
coordinate rows make disjointness an ordinary zero Boolean inner product.
-/

namespace ThreeSum.LocalMaskGraph

open Finset SubsetAddress MaskDecode
open scoped BigOperators

def maskAt (L h i : ℕ) : ℕ := (enumerateLayer L h).getD i 0
def setAt (L h i : ℕ) : Finset (Fin L) := decode L (maskAt L h i)
def vertexCount (L h : ℕ) : ℕ := L.choose h

theorem maskAt_mem {L h i : ℕ} (hi : i < vertexCount L h) :
    maskAt L h i ∈ enumerateLayer L h := by
  have hi' : i < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hi
  unfold maskAt
  rw [List.getD_eq_getElem _ _ hi']
  exact List.getElem_mem hi'

theorem maskAt_spec {L h i : ℕ} (hi : i < vertexCount L h) :
    IsMask L h (maskAt L h i) := (mem_enumerateLayer L h _).mp (maskAt_mem hi)

theorem setAt_card {L h i : ℕ} (hi : i < vertexCount L h) : (setAt L h i).card = h :=
  decode_card_layer (maskAt_mem hi)

theorem subsetMask_setAt {L h i : ℕ} (hi : i < vertexCount L h) :
    subsetMask (setAt L h i) = maskAt L h i := subsetMask_decode (maskAt_spec hi).1

theorem maskAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : maskAt L h i = maskAt L h j) : i=j := by
  have hi' : i < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hi
  have hj' : j < (enumerateLayer L h).length := by simpa [vertexCount,enumerateLayer_length] using hj
  exact (List.getD_inj hi' hj' (enumerateLayer_nodup L h)).mp he

theorem setAt_injective {L h i j : ℕ} (hi : i < vertexCount L h) (hj : j < vertexCount L h)
    (he : setAt L h i = setAt L h j) : i=j := by
  apply maskAt_injective hi hj
  rw [← subsetMask_setAt hi,← subsetMask_setAt hj,he]

theorem setAt_complete {L h : ℕ} (s : Finset (Fin L)) (hs : s.card=h) :
    ∃ i < vertexCount L h, setAt L h i=s := by
  have hm : subsetMask s ∈ enumerateLayer L h := (mem_enumerateLayer L h _).mpr (by
    simpa only [hs] using subsetMask_isMask s)
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hm
  refine ⟨i,by simpa [vertexCount,enumerateLayer_length] using hi,?_⟩
  unfold setAt maskAt
  rw [List.getD_eq_getElem _ _ hi,he,decode_subsetMask]

theorem dot_bits {L : ℕ} (s t : Finset (Fin L)) :
    LightBooleanDot.dot (LightMaskBits.bit L (subsetMask s))
      (LightMaskBits.bit L (subsetMask t)) L = (s ∩ t).card := by
  unfold LightBooleanDot.dot
  rw [← Fin.sum_univ_eq_sum_range]
  have he : (s ∩ t) = (univ : Finset (Fin L)).filter (fun i => i ∈ s ∧ i ∈ t) := by
    ext i
    simp
  rw [he,Finset.card_filter]
  apply sum_congr rfl
  intro i hi
  rw [LightMaskBits.bit_subsetMask s i,LightMaskBits.bit_subsetMask t i]
  by_cases hs : i ∈ s <;> by_cases ht : i ∈ t <;> simp [hs,ht]

theorem dot_zero_iff {L : ℕ} (s t : Finset (Fin L)) :
    LightBooleanDot.dot (LightMaskBits.bit L (subsetMask s))
      (LightMaskBits.bit L (subsetMask t)) L = 0 ↔ Disjoint s t := by
  rw [dot_bits,Finset.card_eq_zero]
  exact Finset.disjoint_iff_inter_eq_empty.symm

theorem indexed_dot_zero_iff {L h i j : ℕ}
    (hi : i < vertexCount L h) (hj : j < vertexCount L h) :
    LightBooleanDot.dot (LightMaskBits.bit L (maskAt L h i))
      (LightMaskBits.bit L (maskAt L h j)) L = 0 ↔ Disjoint (setAt L h i) (setAt L h j) := by
  rw [← subsetMask_setAt hi,← subsetMask_setAt hj]
  exact dot_zero_iff _ _

theorem indexed_edge_iff {L h i j : ℕ}
    (hi : i < vertexCount L h) (hj : j < vertexCount L h) :
    LightBooleanDot.dot (LightMaskBits.bit L (maskAt L h i))
      (LightMaskBits.bit L (maskAt L h j)) L = 0 ↔
      (setAt L h i,setAt L h j) ∈ LayerCounts.edgeSet L h := by
  rw [LayerCounts.mem_edgeSet,indexed_dot_zero_iff hi hj]
  simp only [setAt_card hi,setAt_card hj,true_and]

end ThreeSum.LocalMaskGraph
