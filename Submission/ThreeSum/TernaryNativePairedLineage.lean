import Submission.ThreeSum.TernaryPairedContraction
import Submission.ThreeSum.TernaryNativePairMoments
import Submission.ThreeSum.TernaryRepeatedWords
import Submission.ThreeSum.TernaryGoodOutputCatalog

noncomputable section
namespace ThreeSum.TernaryNativePairedLineage
open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
set_option maxHeartbeats 3000000

/-- Every retained physical child record has one original parent record and
one shared map/output/ordered-partition child. Deleting dictionary entries
or wanted records only restricts this injection; equal-valued records are
kept distinct by their physical occurrence IDs. -/
theorem retained_potential_le {p : ℕ} [Fact p.Prime]
    {E P Q : Type*} [Field E] [Algebra (ZMod p) E] [Fintype E]
    [DecidableEq E] [Fintype P] [Fintype Q]
    {Λ L K F : ℕ} {α π : DigitType}
    (ℓ : E→ₗ[ZMod p] ZMod p) (A : P→Matrix (Fin (K+K)) (Fin Λ) ℤ)
    (B : Q→Matrix (Fin (K+K)) (Fin Λ) ℤ)
    (maps : Fin F→TernaryCoverHashes.Coordinate (Fin L)→ZMod p)
    (seed : E×E) (lineage : Q→P×Child L K F α π)
    (hinj : Function.Injective lineage)
    (hMatrix : ∀ q, B q=A (lineage q).1)
    (hEvent : ∀ q, seed∈menuEvent ℓ (fun i j => (A (lineage q).1 i j : ZMod p))
      (childTarget maps (lineage q).2)) :
    potential B≤nextPotential (α := α) (π := π) ℓ A maps seed := by
  classical
  let weight : P×Child L K F α π→ℕ := fun x =>
    if seed∈menuEvent ℓ (fun i j => (A x.1 i j : ZMod p)) (childTarget maps x.2)
      then minorWeight (A x.1) else 0
  have heach (q : Q) : minorWeight (B q)=weight (lineage q) := by
    simp only [weight,if_pos (hEvent q),hMatrix q]
  unfold potential
  simp_rw [heach]
  calc
    _ = ∑ x∈(univ : Finset Q).image lineage, weight x := by
      rw [sum_image]
      exact fun a ha b hb h => hinj h
    _ ≤ ∑ x : P×Child L K F α π, weight x := sum_le_sum_of_subset (subset_univ _)
    _ = _ := by rw [Fintype.sum_prod_type]; rfl

/-- A literal filter of a finite tuple index never increases its nonnegative
integer paired score. This is the trimming case of the injection theorem. -/
theorem filter_potential_le {P : Type*} [Fintype P] {d Λ : ℕ}
    (A : P→Matrix (Fin d) (Fin Λ) ℤ) (keep : P→Prop) [DecidablePred keep] :
    (∑ q : {q : P // keep q}, minorWeight (A q.val))≤potential A := by
  classical
  unfold potential
  calc
    _ = ∑ q∈(univ : Finset {q : P // keep q}).image Subtype.val, minorWeight (A q) := by
      rw [sum_image]
      exact fun a ha b hb h => Subtype.ext h
    _ ≤ _ := sum_le_sum_of_subset (subset_univ _)

end ThreeSum.TernaryNativePairedLineage
