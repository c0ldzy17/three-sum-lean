import Submission.ThreeSum.Subset

/-! # Transporting compact subset transforms across an explicit equivalence -/

namespace ThreeSum.SubsetTransport

open Finset
open scoped BigOperators

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def reindex (e : α ≃ β) (f : Finset α → ℤ) (S : Finset β) : ℤ :=
  f (S.map e.symm.toEmbedding)

@[simp] theorem reindex_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    reindex e f (S.map e.toEmbedding) = f S := by
  unfold reindex
  congr 1
  ext a
  simp

theorem sum_powerset_map (e : α ≃ β) (S : Finset α) (f : Finset β → ℤ) :
    (∑ T ∈ (S.map e.toEmbedding).powerset, f T) =
      ∑ T ∈ S.powerset, f (T.map e.toEmbedding) := by
  simp only [Finset.map_eq_image]
  rw [Finset.powerset_image,Finset.sum_image]
  intro A hA B hB he
  exact (Finset.image_inj e.injective).mp he

theorem zeta_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    Subset.zeta (reindex e f) (S.map e.toEmbedding) = Subset.zeta f S := by
  unfold Subset.zeta
  rw [sum_powerset_map]
  simp only [reindex_map]

theorem mobius_map (e : α ≃ β) (f : Finset α → ℤ) (S : Finset α) :
    Subset.mobius (reindex e f) (S.map e.toEmbedding) = Subset.mobius f S := by
  unfold Subset.mobius
  rw [sum_powerset_map]
  simp only [Finset.card_map,reindex_map]

theorem partialZeta_map (e : α ≃ β) (f : Finset α → ℤ) (processed S : Finset α) :
    Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (S.map e.toEmbedding) =
      Subset.partialZeta processed f S := by
  unfold Subset.partialZeta
  rw [← Finset.map_inter,sum_powerset_map]
  apply Finset.sum_congr rfl
  intro T hT
  rw [← Finset.map_sdiff,← Finset.map_union,reindex_map]

theorem mobius_partial_product_map (e : α ≃ β) (f g : Finset α → ℤ)
    (processed preL preR Q : Finset α) :
    Subset.mobius (fun S =>
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e f) (preL.map e.toEmbedding ∪ S) *
      Subset.partialZeta (processed.map e.toEmbedding) (reindex e g) (preR.map e.toEmbedding ∪ S))
      (Q.map e.toEmbedding) =
      Subset.mobius (fun S => Subset.partialZeta processed f (preL ∪ S) *
        Subset.partialZeta processed g (preR ∪ S)) Q := by
  unfold Subset.mobius
  rw [sum_powerset_map]
  simp only [← Finset.map_union,partialZeta_map,Finset.card_map]

end ThreeSum.SubsetTransport
