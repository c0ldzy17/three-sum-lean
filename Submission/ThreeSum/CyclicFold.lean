import Submission.ThreeSum.KaratsubaBounds
import Submission.ThreeSum.Histograms
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fintype.EquivFin

/-!
# Folding a dense polynomial product into a cyclic convolution

The product of two vectors of length at most `p` has only two possible
contributions to an output residue `r < p`: coefficients `r` and `r+p`.
The double sum below specifies the answer; the implementation obtains it
by one fast product and a linear pass over the output coefficients.
-/

namespace ThreeSum.CyclicFold

open Finset Polynomial Karatsuba
open scoped BigOperators

theorem asPolynomial_sum (as : List ℤ) (p : ℕ) (ha : as.length ≤ p) :
    asPolynomial as = ∑ i ∈ Finset.range p, monomial i (as.getD i 0) := by
  apply Polynomial.ext
  intro k
  simp only [asPolynomial_coeff, finsetSum_coeff, coeff_monomial]
  by_cases hk : k < p
  · simp [hk, eq_comm]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [hk, eq_comm]

theorem product_coeff_double (as bs : List ℤ) (p : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (r : ℕ) :
    (asPolynomial as * asPolynomial bs).coeff r =
      ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
        if i + j = r then as.getD i 0 * bs.getD j 0 else 0 := by
  rw [asPolynomial_sum as p ha, asPolynomial_sum bs p hb]
  simp only [sum_mul_sum, finsetSum_coeff, monomial_mul_monomial, coeff_monomial]

theorem mod_indicator {p i j r : ℕ} (hi : i < p) (hj : j < p) (hr : r < p)
    (w : ℤ) :
    (if i + j = r then w else 0) + (if i + j = r + p then w else 0) =
      if (i + j) % p = r then w else 0 := by
  by_cases hsum : i + j < p
  · rw [Nat.mod_eq_of_lt hsum]
    split_ifs <;> omega
  · rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    split_ifs <;> omega

def cyclic (p : ℕ) (as bs : List ℤ) (r : ℕ) : ℤ :=
  ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
    if (i + j) % p = r then as.getD i 0 * bs.getD j 0 else 0

theorem fold_product (as bs : List ℤ) (p r : ℕ)
    (ha : as.length ≤ p) (hb : bs.length ≤ p) (hr : r < p) :
    (asPolynomial as * asPolynomial bs).coeff r +
      (asPolynomial as * asPolynomial bs).coeff (r + p) = cyclic p as bs r := by
  rw [product_coeff_double as bs p ha hb, product_coeff_double as bs p ha hb]
  rw [← sum_add_distrib]
  unfold cyclic
  apply sum_congr rfl
  intro i hi
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro j hj
  exact mod_indicator (mem_range.mp hi) (mem_range.mp hj) hr _

def vector (p : ℕ) (f : ZMod p → ℕ) : List ℤ :=
  (List.range p).map fun (i : ℕ) => (f (i : ZMod p) : ℤ)

theorem vector_length (p : ℕ) (f : ZMod p → ℕ) : (vector p f).length = p := by
  simp [vector]

theorem vector_getD (p : ℕ) (f : ZMod p → ℕ) (i : ℕ) (hi : i < p) :
    (vector p f).getD i 0 = (f (i : ZMod p) : ℤ) := by
  rw [List.getD_eq_getElem (vector p f) 0 (by rw [vector_length]; exact hi)]
  simp only [vector, List.getElem_map, List.getElem_range]

theorem sum_range_zmod {p : ℕ} [NeZero p] (f : ZMod p → ℤ) :
    (∑ i ∈ Finset.range p, f (i : ZMod p)) = ∑ i : ZMod p, f i := by
  apply Finset.sum_bij (fun (i : ℕ) (_ : i ∈ Finset.range p) => (i : ZMod p))
  · intro i hi
    exact mem_univ _
  · intro i hi j hj heq
    have h := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (mem_range.mp hi),
      ZMod.val_natCast_of_lt (mem_range.mp hj)] using h
  · intro z hz
    exact ⟨z.val, mem_range.mpr (ZMod.val_lt z), ZMod.natCast_zmod_val z⟩
  · intro i hi
    rfl

theorem cyclic_correlation {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (r : ℕ) (hr : r < p) :
    cyclic p (vector p F) (vector p (fun z => H (-z))) r =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by
  have heq (i j : ℕ) : (i + j) % p = r ↔
      (i : ZMod p) + (j : ZMod p) = (r : ZMod p) := by
    rw [← Nat.cast_add, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hr]
  calc
    _ = ∑ i ∈ Finset.range p, ∑ j ∈ Finset.range p,
        if (i : ZMod p) + (j : ZMod p) = (r : ZMod p)
        then (F (i : ZMod p) : ℤ) * (H (-(j : ZMod p)) : ℤ) else 0 := by
      unfold cyclic
      apply sum_congr rfl
      intro i hi
      apply sum_congr rfl
      intro j hj
      simp only [vector_getD p F i (mem_range.mp hi),
        vector_getD p (fun z => H (-z)) j (mem_range.mp hj), heq]
    _ = ∑ i : ZMod p, ∑ j : ZMod p,
        if i + j = (r : ZMod p) then (F i : ℤ) * (H (-j) : ℤ) else 0 := by
      have hinner (i : ℕ) :
          (∑ j ∈ Finset.range p, if (i : ZMod p) + (j : ZMod p) = (r : ZMod p)
            then (F (i : ZMod p) : ℤ) * (H (-(j : ZMod p)) : ℤ) else 0) =
          ∑ j : ZMod p, if (i : ZMod p) + j = (r : ZMod p)
            then (F (i : ZMod p) : ℤ) * (H (-j) : ℤ) else 0 :=
        sum_range_zmod (fun j => if (i : ZMod p) + j = (r : ZMod p)
          then (F (i : ZMod p) : ℤ) * (H (-j) : ℤ) else 0)
      simp_rw [hinner]
      exact sum_range_zmod (fun i => ∑ j : ZMod p,
        if i + j = (r : ZMod p) then (F i : ℤ) * (H (-j) : ℤ) else 0)
    _ = ∑ i : ZMod p, (F i : ℤ) * (H (i - (r : ZMod p)) : ℤ) := by
      apply sum_congr rfl
      intro i hi
      have hj (j : ZMod p) : i + j = (r : ZMod p) ↔ j = (r : ZMod p) - i := by
        rw [eq_sub_iff_add_eq, add_comm]
      simp_rw [hj]
      simp
    _ = _ := by simp [Balancing.correlation]

theorem folded_correlation {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (r : ℕ) (hr : r < p) :
    (asPolynomial (vector p F) * asPolynomial (vector p (fun z => H (-z)))).coeff r +
      (asPolynomial (vector p F) * asPolynomial (vector p (fun z => H (-z)))).coeff (r+p) =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by
  rw [fold_product _ _ p r (le_of_eq (vector_length _ _))
    (le_of_eq (vector_length _ _)) hr]
  exact cyclic_correlation F H r hr

def padTo (n : ℕ) (as : List ℤ) : List ℤ :=
  as ++ List.replicate (n - as.length) 0

theorem padTo_length (n : ℕ) (as : List ℤ) (ha : as.length ≤ n) :
    (padTo n as).length = n := by
  simp [padTo, Nat.add_sub_of_le ha]

@[simp] theorem asPolynomial_replicate_zero (n : ℕ) :
    asPolynomial (List.replicate n 0) = 0 := by
  induction n with
  | zero => simp [asPolynomial]
  | succ n ih => simp [List.replicate_succ, asPolynomial, ih]

theorem asPolynomial_padTo (n : ℕ) (as : List ℤ) :
    asPolynomial (padTo n as) = asPolynomial as := by
  rw [asPolynomial_split as.length]
  simp [padTo]

theorem coeffBound_padTo {as : List ℤ} {U : ℤ} (h : CoeffBound as U) (n : ℕ) :
    CoeffBound (padTo n as) U := by
  intro j
  rw [← asPolynomial_coeff, asPolynomial_padTo, asPolynomial_coeff]
  exact h j

theorem padded_folded_correlation {p : ℕ} [NeZero p]
    (F H : ZMod p → ℕ) (n r : ℕ) (hr : r < p) :
    (asPolynomial (padTo n (vector p F)) *
      asPolynomial (padTo n (vector p (fun z => H (-z))))).coeff r +
    (asPolynomial (padTo n (vector p F)) *
      asPolynomial (padTo n (vector p (fun z => H (-z))))).coeff (r+p) =
      (Balancing.correlation F H (r : ZMod p) : ℤ) := by
  simp only [asPolynomial_padTo]
  exact folded_correlation F H r hr

end ThreeSum.CyclicFold
