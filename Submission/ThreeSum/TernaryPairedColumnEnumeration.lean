import Submission.ThreeSum.LightTernaryPairedPolynomial
import Submission.ThreeSum.WeightEnumeration

/-! Exact radix enumeration of all ordered column selections. The actual
digit procedure visits each selection once; no ambient input-pair list is
enumerated by the potential evaluator. -/

noncomputable section
namespace ThreeSum.TernaryPairedColumnEnumeration

open TernaryPairedTensor
open scoped BigOperators

abbrev width (m : ℕ) : ℕ := Fintype.card (PairedIndex m)

def equiv (m Λ : ℕ) : (PairedIndex m → Fin Λ) ≃ Fin (Λ^width m) :=
  ((Equiv.arrowCongr (Fintype.equivFin (PairedIndex m)) (Equiv.refl (Fin Λ))).trans
    (Equiv.arrowCongr (Fin.revPerm) (Equiv.refl (Fin Λ)))).trans finFunctionFinEquiv

theorem equiv_symm_digit (m Λ : ℕ) (i : Fin (Λ^width m)) (r : PairedIndex m) :
    ((equiv m Λ).symm i r).val =
      WeightEnumeration.digit Λ (width m) i.val (Fintype.equivFin (PairedIndex m) r).val := by
  change (finFunctionFinEquiv.symm i ((Fintype.equivFin (PairedIndex m) r).rev)).val = _
  rw [finFunctionFinEquiv_symm_apply_val]
  have he : ((Fintype.equivFin (PairedIndex m) r).rev).val =
      width m-1-(Fintype.equivFin (PairedIndex m) r).val := by
    simp only [Fin.val_rev,width]
    omega
  rw [he]
  rfl

theorem sum_digits_eq_sum_columns {R : Type*} [AddCommMonoid R] (m Λ : ℕ)
    (f : (PairedIndex m → ℕ) → R) :
    (∑ i ∈ Finset.range (Λ^width m), f (fun r =>
      WeightEnumeration.digit Λ (width m) i (Fintype.equivFin (PairedIndex m) r).val)) =
      ∑ cols : PairedIndex m → Fin Λ, f (fun r => (cols r).val) := by
  rw [Finset.sum_range]
  have hh := (equiv m Λ).symm.sum_comp (fun cols : PairedIndex m → Fin Λ => f (fun r => (cols r).val))
  rw [←hh]
  apply Finset.sum_congr rfl
  intro i hi
  congr 1
  funext r
  exact (equiv_symm_digit m Λ i r).symm

end ThreeSum.TernaryPairedColumnEnumeration
