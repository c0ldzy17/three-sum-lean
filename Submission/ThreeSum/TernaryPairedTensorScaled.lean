import Submission.ThreeSum.LightTernaryPairedPotentialBatch

noncomputable section
namespace ThreeSum.TernaryPairedTensorScaled
open LightTernaryPairedPolynomial LightTernaryPairedPotential
open TernaryPairedTensor TernaryPairedColumnEnumeration
open scoped BigOperators

theorem scaled_potential {P : Type*} [Fintype P]
    (K base Λ : ℕ) (μ : ℕ→ℤ) (L R : P→Fin Λ→ℤ) (s : ℤ)
    (hTensor : ∀ a b c d : Fin Λ,
      μ (base+tensorIndex Λ a.val b.val c.val d.val)=s*tensor L R a b c d) :
    prefixSum K base Λ μ (Λ^width K)=s^K*
      ((∑ e : Fin K→P, TernaryPairedPotential.rowWeight
        (Sum.elim (fun i => L (e i)) (fun i => R (e i)))) : ℤ) := by
  unfold prefixSum term
  change (∑ i∈Finset.range (Λ^width K),
    (fun cols : PairedIndex K→ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
      (fun r => WeightEnumeration.digit Λ (width K) i (Fintype.equivFin (PairedIndex K) r).val)) = _
  have he := sum_digits_eq_sum_columns K Λ
    (fun cols : PairedIndex K→ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
  refine he.trans ?_
  calc
    _ = ∑ cols : PairedIndex K→Fin Λ, s^K*value (fun q => tensor L R (cols q.1)
        (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := by
      apply Finset.sum_congr rfl
      intro cols hcols
      have he : (fun q : Quad K => μ (base+tensorIndex Λ (cols q.1).val
          (cols q.2.1).val (cols q.2.2.1).val (cols q.2.2.2).val))=
          (fun q => s*tensor L R (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := by
        funext q
        exact hTensor _ _ _ _
      rw [he,value_scaled]
    _ = s^K*∑ cols : PairedIndex K→Fin Λ, value (fun q => tensor L R (cols q.1)
        (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2)) := (Finset.mul_sum _ _ _).symm
    _ = _ := by
      congr 1
      simpa [value,channel] using (full_potential_tensor_expansion (m := K) L R).symm

theorem scaled_total {H : ℕ} {P : Fin H→Type*} [∀ i, Fintype (P i)]
    (K base Λ : ℕ) (μ : ℕ→ℤ) (L R : ∀ i, P i→Fin Λ→ℤ) (s : ℤ)
    (hTensor : ∀ (i : Fin H) (a b c d : Fin Λ),
      μ (base+i.val*Λ^4+tensorIndex Λ a.val b.val c.val d.val)=s*tensor (L i) (R i) a b c d) :
    LightTernaryPairedPotentialBatch.total K base Λ μ H=s^K*
      ((∑ i : Fin H, ∑ e : Fin K→P i, TernaryPairedPotential.rowWeight
        (Sum.elim (fun j => L i (e j)) (fun j => R i (e j)))) : ℤ) := by
  have heach (i : Fin H) : LightTernaryPairedPotentialBatch.term K base Λ μ i.val=s^K*
      ((∑ e : Fin K→P i, TernaryPairedPotential.rowWeight
        (Sum.elim (fun j => L i (e j)) (fun j => R i (e j)))) : ℤ) :=
    scaled_potential K (base+i.val*Λ^4) Λ μ (L i) (R i) s (hTensor i)
  unfold LightTernaryPairedPotentialBatch.total
  rw [←Fin.sum_univ_eq_sum_range]
  simp_rw [heach]
  rw [←Finset.mul_sum]

end ThreeSum.TernaryPairedTensorScaled
