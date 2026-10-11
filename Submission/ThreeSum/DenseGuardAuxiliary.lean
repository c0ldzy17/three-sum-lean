import Submission.ThreeSum.DenseGuard
import Submission.ThreeSum.LightPrimePool

/-! # The actually generated auxiliary prime pool separates all bounded differences -/

namespace ThreeSum.DenseGuard

open Filter Scales RawIncidences
open scoped Topology

def actualAux (n : ℕ) : Finset ℤ :=
  Auxiliary.moduli (WeightedScore.auxiliarySet (LightPrimePool.prime (primeWindow n))
    (LightPrimePool.size (primeWindow n)))

theorem actualAux_eq (n : ℕ) :
    actualAux n=Auxiliary.moduli (PrimeDensity.candidates (primeWindow n)) := by
  rw [actualAux,LightPrimePool.auxiliarySet_eq_candidates]

theorem actual_aux_separates (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ z : ℤ, z ≠ 0 → z.natAbs ≤ 3*n^k →
      ∃ l ∈ actualAux n, ¬ l ∣ z := by
  filter_upwards [actual_auxiliary_cardinality k] with n hn
  intro z hz hb
  rw [actualAux_eq]
  exact Auxiliary.candidate_pool_separates (primeWindow n) (3*n^k)
    (by simpa only [Nat.log2_eq_log_two,candidateCount] using hn) hz hb

theorem difference_natAbs_le {α β γ : Type*} {U : ℕ}
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (ha : ∀ i, (a i).natAbs ≤ U) (hb : ∀ i, (b i).natAbs ≤ U)
    (hc : ∀ i, (c i).natAbs ≤ U) (t : Original α β γ) :
    (difference a b c t).natAbs ≤ 3*U := by
  have hca := Int.natAbs_add_le (c t.2.2) (-b t.2.1)
  have hfinal := Int.natAbs_add_le (c t.2.2+-b t.2.1) (-a t.1)
  have ha' := ha t.1
  have hb' := hb t.2.1
  have hc' := hc t.2.2
  simp only [Int.natAbs_neg] at hca hfinal
  unfold difference
  simp only [sub_eq_add_neg]
  omega

theorem actual_differences_separate {α β γ : Type*} (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ),
      (∀ i, (a i).natAbs ≤ n^k) → (∀ i, (b i).natAbs ≤ n^k) →
      (∀ i, (c i).natAbs ≤ n^k) →
      ∀ t : Original α β γ, difference a b c t ≠ 0 →
        ∃ l ∈ actualAux n, ¬ l ∣ difference a b c t := by
  filter_upwards [actual_aux_separates k] with n hn
  intro a b c ha hb hc t hnonzero
  exact hn _ hnonzero (difference_natAbs_le a b c ha hb hc t)

end ThreeSum.DenseGuard
