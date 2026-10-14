import Submission.ThreeSum.TernaryJointType
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Compressed ternary rank banks

The addresses in this module are words in `Fin 3`, rather than subsets of two
independently addressed copies of each coordinate.  In particular the finite
bank contains at most `3 ^ N` addresses.  The weighted bounds count these
compressed addresses directly.
-/

noncomputable section
namespace ThreeSum.TernaryBank

open Finset
open ThreeSum.TernaryJointType

def rank {N : ℕ} (R : TritWord N) : ℕ := ∑ i, (R i).val

def Below {N : ℕ} (R Q : TritWord N) : Prop := ∀ i, R i ≤ Q i

instance {N : ℕ} (R Q : TritWord N) : Decidable (Below R Q) :=
  inferInstanceAs (Decidable (∀ i, R i ≤ Q i))

def bank (N T : ℕ) : Finset (TritWord N) := univ.filter (fun R => rank R ≤ T)

def deficit {N : ℕ} (Q R : TritWord N) : ℕ := ∑ i, ((Q i).val - (R i).val)

def lowerWords {N : ℕ} (Q : TritWord N) : Finset (TritWord N) :=
  univ.filter (fun R => Below R Q)

def nearWords {N : ℕ} (Q : TritWord N) (D : ℕ) : Finset (TritWord N) :=
  (lowerWords Q).filter (fun R => deficit Q R ≤ D)

@[simp] theorem mem_bank {N T : ℕ} {R : TritWord N} :
    R ∈ bank N T ↔ rank R ≤ T := by simp [bank]

@[simp] theorem mem_lowerWords {N : ℕ} {R Q : TritWord N} :
    R ∈ lowerWords Q ↔ Below R Q := by simp [lowerWords]

@[simp] theorem mem_nearWords {N D : ℕ} {R Q : TritWord N} :
    R ∈ nearWords Q D ↔ Below R Q ∧ deficit Q R ≤ D := by simp [nearWords]

theorem rank_mono {N : ℕ} {R Q : TritWord N} (h : Below R Q) : rank R ≤ rank Q :=
  Finset.sum_le_sum fun i _ => h i

theorem bank_downward_closed {N T : ℕ} {R Q : TritWord N}
    (hRQ : Below R Q) (hQ : Q ∈ bank N T) : R ∈ bank N T :=
  mem_bank.mpr ((rank_mono hRQ).trans (mem_bank.mp hQ))

theorem rank_add_deficit {N : ℕ} {R Q : TritWord N} (h : Below R Q) :
    rank R + deficit Q R = rank Q := by
  unfold rank deficit
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact Nat.add_sub_of_le (h i)

/-- Rank arithmetic used by the physical frozen-coordinate query. -/
theorem rank_update_add {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3) :
    rank (Function.update R i d) + (R i).val = rank R + d.val := by
  unfold rank
  rw [← Finset.add_sum_erase univ (fun j => (R j).val) (mem_univ i),
    ← Finset.add_sum_erase univ (fun j => (Function.update R i d j).val) (mem_univ i)]
  have hrest :
      (∑ j ∈ (univ : Finset (Fin N)).erase i, (Function.update R i d j).val) =
      ∑ j ∈ (univ : Finset (Fin N)).erase i, (R j).val := by
    apply Finset.sum_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  rw [hrest]
  simp only [Function.update_self]
  omega

theorem rank_update_drop {N : ℕ} (R : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d ≤ R i) :
    rank (Function.update R i d) = rank R - ((R i).val - d.val) := by
  have h := rank_update_add R i d
  have hv : d.val ≤ (R i).val := hd
  omega

theorem below_bank_or_near {N T : ℕ} {R Q : TritWord N} (hRQ : Below R Q) :
    R ∈ bank N T ∨ R ∈ nearWords Q (rank Q-(T+1)) := by
  by_cases hlow : rank R ≤ T
  · exact Or.inl (mem_bank.mpr hlow)
  · apply Or.inr
    apply mem_nearWords.mpr
    refine ⟨hRQ, ?_⟩
    have hsum := rank_add_deficit hRQ
    omega

theorem bank_card_le (N T : ℕ) : (bank N T).card ≤ 3 ^ N := by
  calc
    (bank N T).card ≤ (univ : Finset (TritWord N)).card := card_le_card (filter_subset _ _)
    _ = 3 ^ N := by simp [TritWord]

theorem rank_generating_sum (N : ℕ) (y : ℝ) :
    (∑ R : TritWord N, y ^ rank R) = (1 + y + y ^ 2) ^ N := by
  have h := Fintype.sum_pow (fun d : Fin 3 => y ^ d.val) N
  have hlocal : (∑ d : Fin 3, y ^ d.val) = 1 + y + y ^ 2 := by
    simp [Fin.sum_univ_succ]
    ring
  rw [hlocal] at h
  rw [h]
  apply Finset.sum_congr rfl
  intro R hR
  exact (Finset.prod_pow_eq_pow_sum univ (fun i => (R i).val) y).symm

private theorem pow_antitone (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1)
    {a b : ℕ} (hab : a ≤ b) : y ^ b ≤ y ^ a := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hab
  rw [pow_add]
  exact mul_le_of_le_one_right (pow_nonneg hy _) (pow_le_one₀ hy hy1)

theorem bank_card_gibbs (N T : ℕ) (y : ℝ) (hy : 0 ≤ y) (hy1 : y ≤ 1) :
    (bank N T).card * y ^ T ≤ (1 + y + y ^ 2) ^ N := by
  calc
    (bank N T).card * y ^ T = ∑ R ∈ bank N T, y ^ T := by simp
    _ ≤ ∑ R ∈ bank N T, y ^ rank R := by
      apply Finset.sum_le_sum
      intro R hR
      exact pow_antitone y hy hy1 (mem_bank.mp hR)
    _ ≤ ∑ R : TritWord N, y ^ rank R := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro R hR hnot
      exact pow_nonneg hy _
    _ = (1 + y + y ^ 2) ^ N := rank_generating_sum N y

def digitDeficitWeight (z : ℝ) (q r : Fin 3) : ℝ :=
  if r ≤ q then z ^ (q.val - r.val) else 0

theorem digit_deficit_sum (z : ℝ) (q : Fin 3) :
    (∑ r : Fin 3, digitDeficitWeight z q r) =
      if q = 0 then 1 else if q = 1 then 1 + z else 1 + z + z ^ 2 := by
  fin_cases q <;> norm_num [digitDeficitWeight, Fin.sum_univ_succ, Fin.le_def] <;> ring

theorem deficit_generating_sum {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
      ∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
        else 1 + z + z ^ 2) := by
  have hpoint (R : TritWord N) :
      (∏ i, digitDeficitWeight z (Q i) (R i)) =
        if Below R Q then z ^ deficit Q R else 0 := by
    by_cases h : Below R Q
    · simp only [h, ↓reduceIte]
      have heq : (∏ i : Fin N, digitDeficitWeight z (Q i) (R i)) =
          ∏ i : Fin N, z ^ ((Q i).val - (R i).val) := by
        apply Finset.prod_congr rfl
        intro i hi
        simp [digitDeficitWeight, h i]
      rw [heq]
      exact Finset.prod_pow_eq_pow_sum (univ : Finset (Fin N)) _ _
    · simp only [h, ↓reduceIte]
      obtain ⟨i, hi⟩ := not_forall.mp h
      apply Finset.prod_eq_zero (mem_univ i)
      simp [digitDeficitWeight, hi]
  calc
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
        ∑ R : TritWord N, if Below R Q then z ^ deficit Q R else 0 := by
      simp [lowerWords, Finset.sum_filter]
    _ = ∑ R : TritWord N, ∏ i, digitDeficitWeight z (Q i) (R i) := by
      apply Finset.sum_congr rfl
      intro R hR
      exact (hpoint R).symm
    _ = ∏ i : Fin N, ∑ r : Fin 3, digitDeficitWeight z (Q i) r :=
      (Fintype.prod_sum _).symm
    _ = _ := by simp only [digit_deficit_sum]

theorem deficit_product_eq_counts {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
      else 1 + z + z ^ 2)) =
    (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by
  have hlocal (q : Fin 3) :
      (if q = 0 then 1 else if q = 1 then 1 + z else 1 + z + z ^ 2) =
        (1 + z) ^ (if q = 1 then 1 else 0 : ℕ) *
          (1 + z + z ^ 2) ^ (if q = 2 then 1 else 0 : ℕ) := by
    fin_cases q <;> norm_num [Fin.ext_iff]
  simp_rw [hlocal]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum,
    Finset.prod_pow_eq_pow_sum]
  rfl

theorem deficit_generating_sum_counts {N : ℕ} (Q : TritWord N) (z : ℝ) :
    (∑ R ∈ lowerWords Q, z ^ deficit Q R) =
    (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by
  rw [deficit_generating_sum, deficit_product_eq_counts]

theorem nearWords_card_gibbs {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (nearWords Q D).card * z ^ D ≤
      ∏ i : Fin N, (if Q i = 0 then 1 else if Q i = 1 then 1 + z
        else 1 + z + z ^ 2) := by
  calc
    (nearWords Q D).card * z ^ D = ∑ R ∈ nearWords Q D, z ^ D := by simp
    _ ≤ ∑ R ∈ nearWords Q D, z ^ deficit Q R := by
      apply Finset.sum_le_sum
      intro R hR
      exact pow_antitone z hz hz1 (mem_nearWords.mp hR).2
    _ ≤ ∑ R ∈ lowerWords Q, z ^ deficit Q R := by
      apply Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      intro R hR hnot
      exact pow_nonneg hz _
    _ = _ := deficit_generating_sum Q z

theorem nearWords_card_gibbs_counts {N : ℕ} (Q : TritWord N) (D : ℕ)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (nearWords Q D).card * z ^ D ≤
      (1 + z) ^ digitCount Q 1 * (1 + z + z ^ 2) ^ digitCount Q 2 := by
  rw [← deficit_product_eq_counts]
  exact nearWords_card_gibbs Q D z hz hz1

end ThreeSum.TernaryBank
