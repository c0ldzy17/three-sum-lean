import Submission.ThreeSum.WeightedModuli
import Submission.ThreeSum.ModuloCounts

/-!
# Array-order identities for the weighted modular score

The auxiliary primes are read in a fixed array order.  Every partial
correction is at most the initial `s * N_q`, so the corresponding machine
subtractions stay nonnegative.  Shared factors with `q` use `joint`.
-/

namespace ThreeSum.WeightedScore

open Finset Arithmetic ModuloCounts WeightedModuli
open scoped BigOperators

def auxiliarySet (primes : ℕ → ℕ) (s : ℕ) : Finset ℕ :=
  (range s).image primes

def corrections (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) : ℕ :=
  ∑ j ∈ range i, count (joint q (primes j)) nA nB nC a b c

def remaining (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) : ℕ :=
  s * count q nA nB nC a b c - corrections primes q nA nB nC a b c i

def score (primes : ℕ → ℕ) (s q nA nB nC : ℕ) (a b c : ℕ → ℤ) : ℕ :=
  weightedFalseCount (triples nA nB nC) (difference a b c)
    (Auxiliary.moduli (auxiliarySet primes s)) q

theorem count_mono_dvd {q r : ℕ} (h : q ∣ r) (nA nB nC : ℕ)
    (a b c : ℕ → ℤ) : count r nA nB nC a b c ≤ count q nA nB nC a b c := by
  unfold count modCount
  apply sum_le_sum
  intro t ht
  have hdiv : (q : ℤ) ∣ (r : ℤ) := Int.natCast_dvd_natCast.mpr h
  unfold dividesIndicator
  by_cases hr : (r : ℤ) ∣ difference a b c t
  · simp [hr, hdiv.trans hr]
  · simp [hr]

theorem base_dvd_joint (q p : ℕ) : q ∣ joint q p := by
  unfold joint
  split
  · exact dvd_refl q
  · exact dvd_mul_right q p

theorem joint_count_le (q p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count (joint q p) nA nB nC a b c ≤ count q nA nB nC a b c :=
  count_mono_dvd (base_dvd_joint q p) nA nB nC a b c

@[simp] theorem corrections_zero (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) : corrections primes q nA nB nC a b c 0 = 0 := by
  simp [corrections]

theorem corrections_succ (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    corrections primes q nA nB nC a b c (i+1) =
      corrections primes q nA nB nC a b c i +
        count (joint q (primes i)) nA nB nC a b c := by
  exact sum_range_succ _ _

theorem corrections_le (primes : ℕ → ℕ) (q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    corrections primes q nA nB nC a b c i ≤ i * count q nA nB nC a b c := by
  unfold corrections
  calc
    _ ≤ ∑ _j ∈ range i, count q nA nB nC a b c :=
      sum_le_sum fun j _ => joint_count_le q (primes j) nA nB nC a b c
    _ = _ := by simp

@[simp] theorem remaining_zero (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) :
    remaining primes s q nA nB nC a b c 0 = s * count q nA nB nC a b c := by
  simp [remaining]

theorem remaining_le (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c i ≤ s * (nA*nB*nC) :=
  (Nat.sub_le _ _).trans (Nat.mul_le_mul_left s (count_le q nA nB nC a b c))

theorem next_count_le_remaining (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    count (joint q (primes i)) nA nB nC a b c ≤
      remaining primes s q nA nB nC a b c i := by
  have h := (corrections_le primes q nA nB nC a b c (i+1)).trans
    (Nat.mul_le_mul_right (count q nA nB nC a b c) (by omega : i+1 ≤ s))
  rw [corrections_succ] at h
  unfold remaining
  omega

theorem remaining_succ (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ) (i : ℕ) :
    remaining primes s q nA nB nC a b c (i+1) =
      remaining primes s q nA nB nC a b c i -
        count (joint q (primes i)) nA nB nC a b c := by
  unfold remaining
  rw [corrections_succ, Nat.sub_add_eq]

theorem remaining_succ_cast (primes : ℕ → ℕ) {s q nA nB nC i : ℕ}
    (a b c : ℕ → ℤ) (hi : i < s) :
    (remaining primes s q nA nB nC a b c (i+1) : ℤ) =
      (remaining primes s q nA nB nC a b c i : ℤ) -
        (count (joint q (primes i)) nA nB nC a b c : ℤ) := by
  rw [remaining_succ, Nat.cast_sub (next_count_le_remaining primes a b c hi)]

theorem score_eq_remaining (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (a b c : ℕ → ℤ)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j) :
    score primes s q nA nB nC a b c = remaining primes s q nA nB nC a b c s := by
  have hcard : (auxiliarySet primes s).card = s := by
    unfold auxiliarySet
    rw [Finset.card_image_of_injOn]
    · exact card_range s
    · intro i hi j hj heq
      exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  have hpr : ∀ p ∈ auxiliarySet primes s, Nat.Prime p := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hp
    exact hprime i (mem_range.mp hi)
  have hsum : (∑ p ∈ auxiliarySet primes s,
      modCount (triples nA nB nC) (difference a b c) (joint q p)) =
      corrections primes q nA nB nC a b c s := by
    unfold auxiliarySet corrections count
    rw [sum_image]
    intro i hi j hj heq
    exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  unfold score
  rw [weighted_count_eq _ _ _ hpr q, hcard, hsum]
  rfl

theorem count_congr {q nA nB nC : ℕ} {a a' b b' c c' : ℕ → ℤ}
    (ha : ∀ i < nA, a i = a' i) (hb : ∀ i < nB, b i = b' i)
    (hc : ∀ i < nC, c i = c' i) :
    count q nA nB nC a b c = count q nA nB nC a' b' c' := by
  unfold count modCount
  apply sum_congr rfl
  intro t ht
  simp only [triples, mem_product, mem_range] at ht
  simp only [difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]

end ThreeSum.WeightedScore
