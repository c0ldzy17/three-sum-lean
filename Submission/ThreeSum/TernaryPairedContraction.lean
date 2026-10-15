import Submission.ThreeSum.TernaryPairedPotential

/-! Literal local-map/output/partition children and their paired potential.
Local map occurrences and ordered endpoint partitions are never deduplicated.
The row event is imposed on original integer coefficient vectors, rather
than on local encoded words. -/

noncomputable section
namespace ThreeSum.TernaryPairedContraction

open Finset TernaryJointType TernaryCoverLocal TernaryCoverOutputCap
open TernaryOriginalRowMenu TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable

abbrev Child (L m F : ℕ) (α π : DigitType) :=
  Fin F × (Σ q : vertices L π, Fin m → outputFiber α π q.val)

theorem child_card_le (L m F : ℕ) (α π : DigitType) :
    Fintype.card (Child L m F α π) ≤ F*(vertices L π).card*(2^(π 1)*3^(π 2))^m := by
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_sigma]
  have hh : (∑ q : vertices L π, Fintype.card (Fin m → outputFiber α π q.val)) ≤
      (vertices L π).card*(2^(π 1)*3^(π 2))^m := by
    calc
      _ ≤ ∑ _q : vertices L π, (2^(π 1)*3^(π 2))^m := by
        apply sum_le_sum
        intro q hq
        rw [Fintype.card_fun,Fintype.card_fin]
        exact Nat.pow_le_pow_left (outputFiber_card_le α π q.val (mem_filter.mp q.property).2) m
      _ = _ := by simp
  exact (Nat.mul_le_mul_left F hh).trans_eq (by ring)

variable {p : ℕ} [Fact p.Prime]

def childTarget {L m F : ℕ} {α π : DigitType}
    (maps : Fin F → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (c : Child L m F α π) : Fin (m+m) → ZMod p :=
  fun i => Sum.elim
    (fun j => leftHash (maps c.1) (c.2.2 j).val)
    (fun j => rightHash (maps c.1) (c.2.2 j).val) (finSumFinEquiv.symm i)

variable {E P : Type*} [Field E] [Algebra (ZMod p) E]
  [Fintype E] [DecidableEq E] [Fintype P]

def potential {d Λ : ℕ} (A : P → Matrix (Fin d) (Fin Λ) ℤ) : ℕ :=
  ∑ a, minorWeight (A a)

def nextPotential {Λ L m F : ℕ} {α π : DigitType} (ℓ : E →ₗ[ZMod p] ZMod p)
    (A : P → Matrix (Fin (m+m)) (Fin Λ) ℤ)
    (maps : Fin F → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (seed : E × E) : ℕ :=
  ∑ a : P, ∑ c : Child L m F α π,
    if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
    then minorWeight (A a) else 0

theorem sum_nextPotential_bound {Λ L m F : ℕ} {α π : DigitType}
    (ℓ : E →ₗ[ZMod p] ZMod p) (hℓ : ℓ ≠ 0)
    (V : Submodule (ZMod p) (Fin Λ → ZMod p)) (hV : V ≠ ⊤) (hp : 3 ≤ p)
    (A : P → Matrix (Fin (m+m)) (Fin Λ) ℤ)
    (hsmall : ∀ a f, ((A a).submatrix id f).det.natAbs < p)
    (maps : Fin F → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (hsize1 : 8*Λ*p^2 ≤ Fintype.card E)
    (hsize : 8*Λ*p^(2*(m+m)) ≤ Fintype.card E) :
    p^(m+m) * (∑ seed ∈ admissible Λ ℓ V,
      nextPotential (α := α) (π := π) ℓ A maps seed) ≤
      3*(admissible Λ ℓ V).card*F*(vertices L π).card*
        (2^(π 1)*3^(π 2))^m*potential A := by
  let S := admissible Λ ℓ V
  have ht (a : P) (c : Child L m F α π) :
      p^(m+m) * (∑ seed ∈ S,
        if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
        then minorWeight (A a) else 0) ≤ 3*S.card*minorWeight (A a) := by
    by_cases hz : minorWeight (A a) = 0
    · simp [hz]
    · have hind := mod_independent_of_minorWeight_pos (A a) (Nat.pos_of_ne_zero hz) (hsmall a)
      have hc := admissible_event_bound ℓ hℓ V hV (by simpa using hp)
        (fun i j => (A a i j : ZMod p)) hind (childTarget maps c)
        (by simpa using hsize1) (by simpa using hsize)
      have he : (∑ seed ∈ S,
          if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
          then minorWeight (A a) else 0) =
          (S ∩ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)).card *
            minorWeight (A a) := by
        rw [← sum_filter]
        simp only [sum_const, smul_eq_mul]
        congr 1
      rw [he]
      have hh := Nat.mul_le_mul_right (minorWeight (A a)) hc
      simpa [S,Nat.mul_assoc] using hh
  have he : (∑ seed ∈ S, nextPotential (α := α) (π := π) ℓ A maps seed) =
      ∑ a : P, ∑ c : Child L m F α π, ∑ seed ∈ S,
        if seed ∈ menuEvent ℓ (fun i j => (A a i j : ZMod p)) (childTarget maps c)
        then minorWeight (A a) else 0 := by
    unfold nextPotential
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
  rw [he,mul_sum]
  calc
    _ ≤ ∑ a : P, ∑ _c : Child L m F α π, 3*S.card*minorWeight (A a) := by
      apply sum_le_sum
      intro a ha
      rw [mul_sum]
      exact sum_le_sum fun c hc => ht a c
    _ = 3*S.card*Fintype.card (Child L m F α π)*potential A := by
      simp only [sum_const,card_univ,smul_eq_mul,potential]
      rw [mul_sum]
      apply sum_congr rfl
      intro a ha
      ring
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_right (potential A)
        (Nat.mul_le_mul_left (3*S.card) (child_card_le L m F α π))
      simpa only [Nat.mul_assoc] using hh

end ThreeSum.TernaryPairedContraction
