import Submission.ThreeSum.PrimeChain

/-!
# Positive represented FALSE scores for a scalar modulus

Original records remain the summation indices.  A nonnegative multiplicity
records the number of representations of each original modular triple.
Auxiliary residue failures remove all genuine zero differences before any
prime averaging.  The representation factor is retained explicitly.
-/

namespace ThreeSum.TernaryResidueScore

open Finset
open scoped BigOperators

variable {ι : Type*}

def score (T : Finset ι) (difference : ι → ℤ) (L : Finset ℤ)
    (repr : ℕ → ι → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ T, if m ∣ (difference i).natAbs then
    repr m i * Arithmetic.missWeight L (difference i) else 0

def residueScore (T : Finset ι) (difference : ι → ℤ)
    (repr : ℕ → ι → ℕ) (m : ℕ) (l : ℤ) : ℕ :=
  ∑ i ∈ T, if m ∣ (difference i).natAbs ∧ ¬ l ∣ difference i then repr m i else 0

def mass (T : Finset ι) (difference : ι → ℤ)
    (repr : ℕ → ι → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ T, if m ∣ (difference i).natAbs then repr m i else 0

def falseMass (T : Finset ι) (difference : ι → ℤ)
    (repr : ℕ → ι → ℕ) (m : ℕ) : ℕ :=
  ∑ i ∈ T, if m ∣ (difference i).natAbs ∧ difference i ≠ 0 then repr m i else 0

/-- The backend can sum residue-filtered positive query counts.  No
subtraction of nearly equal counts and no unknown zero predicate occurs. -/
theorem score_eq_sum_residueScore (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (m : ℕ) :
    score T difference L repr m = ∑ l ∈ L, residueScore T difference repr m l := by
  classical
  unfold score residueScore
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hm : m ∣ (difference i).natAbs
  · simp only [if_pos hm, Arithmetic.missWeight, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro l hl
    by_cases hd : l ∣ difference i <;> simp [hm, hd]
  · simp [hm]

/-- Source residue classes determine the failed auxiliary test exactly,
including negative original values and nonprime auxiliary moduli. -/
theorem difference_dvd_iff_residues (l a b c : ℤ) :
    l ∣ c-b-a ↔ l ∣ c%l-b%l-a%l := by
  exact ((Int.mod_modEq c l).sub (Int.mod_modEq b l) |>.sub (Int.mod_modEq a l)).dvd_iff.symm

@[simp] theorem zero_contributes_zero (L : Finset ℤ) (R : ℕ) :
    R * Arithmetic.missWeight L 0 = 0 := by simp

/-- Coverage, on the actual modular triples only, gives the lower sandwich. -/
theorem physicalScore_le_score (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (m : ℕ)
    (hcover : ∀ i ∈ T, m ∣ (difference i).natAbs → 1 ≤ repr m i) :
    PrimeChain.score T difference (Arithmetic.missWeight L) m ≤
      score T difference L repr m := by
  unfold PrimeChain.score score
  apply Finset.sum_le_sum
  intro i hi
  by_cases hm : m ∣ (difference i).natAbs
  · simp only [if_pos hm]
    simpa only [one_mul] using
      Nat.mul_le_mul_right (Arithmetic.missWeight L (difference i)) (hcover i hi hm)
  · simp [hm]

/-- A raw representation cap supplies the upper sandwich.  This cap is
independent of the candidate scalar modulus and original triple. -/
theorem score_le_cap_physicalScore (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (m S : ℕ)
    (hcap : ∀ i ∈ T, m ∣ (difference i).natAbs → repr m i ≤ S) :
    score T difference L repr m ≤
      S * PrimeChain.score T difference (Arithmetic.missWeight L) m := by
  unfold PrimeChain.score score
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  by_cases hm : m ∣ (difference i).natAbs
  · simp only [if_pos hm]
    exact Nat.mul_le_mul_right _ (hcap i hi hm)
  · simp [hm]

/-- The measured represented score bounds all represented false triples,
not just their distinct values or one selected witness per triple. -/
theorem falseMass_le_score (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (m : ℕ)
    (hsep : ∀ i ∈ T, difference i ≠ 0 → ∃ l ∈ L, ¬ l ∣ difference i) :
    falseMass T difference repr m ≤ score T difference L repr m := by
  unfold falseMass score
  apply Finset.sum_le_sum
  intro i hi
  by_cases h : m ∣ (difference i).natAbs ∧ difference i ≠ 0
  · obtain ⟨l, hl, hnot⟩ := hsep i hi h.2
    have hw := Arithmetic.missWeight_pos_of_witness hl hnot
    simp only [if_pos h, if_pos h.1]
    simpa only [mul_one] using Nat.mul_le_mul_left (repr m i) hw
  · simp only [if_neg h]
    exact Nat.zero_le _

/-- An excess of total represented mass over the measured false score
certifies an original zero difference.  It is valid on arbitrary inputs. -/
theorem dense_early_yes (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (m : ℕ)
    (hsep : ∀ i ∈ T, difference i ≠ 0 → ∃ l ∈ L, ¬ l ∣ difference i)
    (hlarge : score T difference L repr m < mass T difference repr m) :
    ∃ i ∈ T, difference i = 0 := by
  classical
  by_contra hnone
  push_neg at hnone
  have heq : mass T difference repr m = falseMass T difference repr m := by
    unfold mass falseMass
    apply Finset.sum_congr rfl
    intro i hi
    by_cases hm : m ∣ (difference i).natAbs
    · rw [if_pos hm, if_pos ⟨hm, hnone i hi⟩]
    · rw [if_neg hm, if_neg (fun h => hm h.1)]
  have hh := falseMass_le_score T difference L repr m hsep
  rw [← heq] at hh
  exact Nat.not_lt_of_ge hh hlarge

/-- Prime averaging uses the original weighted score.  The representation
loss S occurs at each step and is never omitted from the recurrence. -/
theorem sum_candidate_scores_le (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (C : Finset ℕ) (q K S : ℕ)
    (hcurrent : PrimeChain.score T difference (Arithmetic.missWeight L) q ≤
      score T difference L repr q)
    (hcandidates : ∀ p ∈ C, score T difference L repr (q*p) ≤
      S * PrimeChain.score T difference (Arithmetic.missWeight L) (q*p))
    (havg : (∑ p ∈ C, PrimeChain.score T difference (Arithmetic.missWeight L) (q*p)) ≤
      K * PrimeChain.score T difference (Arithmetic.missWeight L) q) :
    (∑ p ∈ C, score T difference L repr (q*p)) ≤
      (S*K) * score T difference L repr q := by
  calc
    _ ≤ ∑ p ∈ C, S * PrimeChain.score T difference (Arithmetic.missWeight L) (q*p) :=
      Finset.sum_le_sum hcandidates
    _ = S * ∑ p ∈ C, PrimeChain.score T difference (Arithmetic.missWeight L) (q*p) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ S * (K * PrimeChain.score T difference (Arithmetic.missWeight L) q) :=
      Nat.mul_le_mul_left _ havg
    _ ≤ S * (K * score T difference L repr q) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hcurrent)
    _ = _ := by ring

/-- Existing nonzero-difference prime-divisor averaging remains applicable
because the miss weight of zero is exactly zero. -/
theorem sum_candidate_scores_le_log (T : Finset ι) (difference : ι → ℤ)
    (L : Finset ℤ) (repr : ℕ → ι → ℕ) (C : Finset ℕ) (q y M S : ℕ)
    (hy : 1 < y) (hprime : ∀ p ∈ C, Nat.Prime p) (hmin : ∀ p ∈ C, y ≤ p)
    (hbound : ∀ i ∈ T, (difference i).natAbs ≤ M)
    (hcover : ∀ i ∈ T, q ∣ (difference i).natAbs → 1 ≤ repr q i)
    (hcap : ∀ p ∈ C, ∀ i ∈ T, q*p ∣ (difference i).natAbs → repr (q*p) i ≤ S) :
    (∑ p ∈ C, score T difference L repr (q*p)) ≤
      (S * Nat.log y M) * score T difference L repr q := by
  apply sum_candidate_scores_le T difference L repr C q (Nat.log y M) S
    (physicalScore_le_score T difference L repr q hcover)
  · intro p hp
    exact score_le_cap_physicalScore T difference L repr (q*p) S (hcap p hp)
  · exact PrimeChain.sum_scores_le_log T difference (Arithmetic.missWeight L)
      (by simp) C q y M hy hprime hmin hbound

end ThreeSum.TernaryResidueScore
