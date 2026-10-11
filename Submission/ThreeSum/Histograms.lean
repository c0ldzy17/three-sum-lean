import Submission.ThreeSum.Balancing
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Abel

/-!
# Exact histogram and correlation counts

All weights are natural multiplicities.  In particular, raw A incidences and
repeated selected-map occurrences need not be deduplicated to use these
identities. The common offset is chosen from the actual key histograms.
-/

namespace ThreeSum.Histograms

open Finset
open scoped BigOperators

variable {ι τ ν G : Type*} [AddCommGroup G] [Fintype G] [DecidableEq G]

def histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) (k : G) : ℕ :=
  ∑ i ∈ I, if key i = k then weight i else 0

theorem sum_histogram (I : Finset ι) (key : ι → G) (weight : ι → ℕ) :
    (∑ k, histogram I key weight k) = ∑ i ∈ I, weight i := by
  unfold histogram
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp

def pairMass (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) : ℕ :=
  ∑ i ∈ I, ∑ j ∈ J, if right j - left i = d then weightL i * weightR j else 0

theorem correlation_histograms (I : Finset ι) (J : Finset τ)
    (left : ι → G) (right : τ → G) (weightL : ι → ℕ) (weightR : τ → ℕ) (d : G) :
    Balancing.correlation (histogram J right weightR) (histogram I left weightL) d =
      pairMass I J left right weightL weightR d := by
  unfold Balancing.correlation histogram pairMass
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  conv_rhs => rw [sum_comm]
  apply sum_congr rfl
  intro j hj
  rw [sum_comm]
  have hinner (i : ι) :
      (∑ k : G, (if right j = k then weightR j else 0) *
        (if left i = k - d then weightL i else 0)) =
      if right j - left i = d then weightL i * weightR j else 0 := by
    simp only [ite_mul, zero_mul, sum_ite_eq', mem_univ, ite_true]
    by_cases h : right j - left i = d
    · have h' : left i = right j - d := by exact eq_sub_iff_add_eq.mpr (by simpa only [add_comm] using (sub_eq_iff_eq_add.mp h).symm)
      simp [h, h', Nat.mul_comm]
    · have h' : left i ≠ right j - d := by
        intro h'
        apply h
        rw [h']
        abel
      simp [h, h']
  simp_rw [hinner]

theorem pairMass_one_eq_card [DecidableEq ι] [DecidableEq τ]
    (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G) (d : G) :
    pairMass I J left right (fun _ => 1) (fun _ => 1) d =
      ((I ×ˢ J).filter fun p => right p.2 - left p.1 = d).card := by
  rw [Finset.card_eq_sum_ones, sum_filter, sum_product]
  simp [pairMass]

/-- The actual raw-incidence/output-key join obeys the exact balancing bound
for the selected offset, without an independent hash-uniformity premise. -/
theorem selected_pairMass_bound [Inhabited G]
    (keys : List G) (hkeys : ∀ d, d ∈ keys)
    (I : Finset ι) (J : Finset τ) (left : ι → G) (right : τ → G)
    (weightL : ι → ℕ) (weightR : τ → ℕ) :
    Fintype.card G * pairMass I J left right weightL weightR
      (Balancing.chooseOffset keys (histogram J right weightR) (histogram I left weightL)) ≤
        (∑ i ∈ I, weightL i) * (∑ j ∈ J, weightR j) := by
  have h := Balancing.chooseOffset_balanced keys hkeys
    (histogram J right weightR) (histogram I left weightL)
  rw [correlation_histograms, sum_histogram, sum_histogram] at h
  simpa only [Nat.mul_comm] using h

def tripleMass (A : Finset ι) (B : Finset τ) (C : Finset ν)
    (a : ι → G) (b : τ → G) (c : ν → G)
    (wa : ι → ℕ) (wb : τ → ℕ) (wc : ν → ℕ) : ℕ :=
  ∑ i ∈ A, ∑ j ∈ B, ∑ k ∈ C,
    if a i + b j = c k then wa i * wb j * wc k else 0

/-- One B/C correlation is shared by every A value in the band. -/
theorem tripleMass_eq_histogram (A : Finset ι) (B : Finset τ) (C : Finset ν)
    (a : ι → G) (b : τ → G) (c : ν → G)
    (wa : ι → ℕ) (wb : τ → ℕ) (wc : ν → ℕ) :
    tripleMass A B C a b c wa wb wc =
      ∑ i ∈ A, wa i *
        Balancing.correlation (histogram C c wc) (histogram B b wb) (a i) := by
  unfold tripleMass
  apply sum_congr rfl
  intro i hi
  rw [correlation_histograms]
  unfold pairMass
  rw [mul_sum]
  apply sum_congr rfl
  intro j hj
  rw [mul_sum]
  apply sum_congr rfl
  intro k hk
  have heq : a i + b j = c k ↔ c k - b j = a i := by
    rw [sub_eq_iff_eq_add]
    exact eq_comm
  simp only [heq]
  split <;> simp_all [Nat.mul_assoc]

end ThreeSum.Histograms
