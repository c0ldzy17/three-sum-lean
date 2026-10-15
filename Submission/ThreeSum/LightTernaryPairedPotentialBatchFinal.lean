import Submission.ThreeSum.LightTernaryPairedPotentialBatch

namespace ThreeSum.LightTernaryPairedPotentialBatch
open Light
open scoped BigOperators

theorem total_eq_of_reads (K base Λ H : ℕ) (μ ν : ℕ→ℤ) (hΛ : 1≤Λ)
    (hread : ∀ i<H, ∀ q<Λ^4, μ (base+i*Λ^4+q)=ν (base+i*Λ^4+q)) :
    total K base Λ μ H=total K base Λ ν H := by
  unfold total
  apply Finset.sum_congr rfl
  intro i hi
  unfold term LightTernaryPairedPotential.prefixSum
  apply Finset.sum_congr rfl
  intro j hj
  unfold LightTernaryPairedPotential.term
  congr 1
  funext q
  exact hread i (Finset.mem_range.mp hi) _ (LightTernaryPairedPolynomial.tensorIndex_lt
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)))

theorem receipt_final {lim : Limits} {P : Program} {p d t K base Λ H cutoff : ℕ}
    {argv : List ℤ} {μ : ℕ→ℤ} (hΛ : 1≤Λ) (hend : base+H*Λ^4≤cutoff)
    (h : Meets lim P p d argv μ t
      (fun r ν => r=total K base Λ μ H ∧ Kept μ ν cutoff)) :
    Meets lim P p d argv μ t (fun r ν => r=total K base Λ ν H ∧ Kept μ ν cutoff) := by
  apply h.mono le_rfl
  rintro r ν ⟨hr,hkeep⟩
  refine ⟨hr.trans (total_eq_of_reads K base Λ H μ ν hΛ ?_),hkeep⟩
  intro i hi q hq
  apply Eq.symm
  apply hkeep
  have hh := Nat.mul_le_mul_right (Λ^4) (by omega : i+1≤H)
  nlinarith

end ThreeSum.LightTernaryPairedPotentialBatch
