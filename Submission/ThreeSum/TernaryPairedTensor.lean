import Submission.ThreeSum.TernaryPairedSupportConcrete

/-! Exact fourth mixed tensor expansion of the paired determinant potential.
The source channels may be signed; no positivity is asserted for those
channels. Positivity belongs to the final sum of squared determinants. -/

noncomputable section
namespace ThreeSum.TernaryPairedTensor

open Finset Matrix TernaryPairedPotential
open scoped BigOperators

variable {P I R : Type*} [Fintype P] [CommRing R]

abbrev PairedIndex (m : ℕ) := Fin m ⊕ Fin m

def pairedMinor {m : ℕ} (L R' : P → I → R) (e : Fin m → P) (cols : PairedIndex m → I) :
    Matrix (PairedIndex m) (PairedIndex m) R :=
  fun i j => Sum.elim (fun k => L (e k)) (fun k => R' (e k)) i (cols j)

def tensor (L R' : P → I → R) (a b c d : I) : R :=
  ∑ x : P, L x a * L x b * R' x c * R' x d

theorem det_row_expansion {m : ℕ} (L R' : P → I → R)
    (e : Fin m → P) (cols : PairedIndex m → I) :
    (pairedMinor L R' e cols).det =
      ∑ σ : Equiv.Perm (PairedIndex m), ((Equiv.Perm.sign σ : ℤ) : R) *
        (∏ i : Fin m, L (e i) (cols (σ (.inl i)))) *
        (∏ i : Fin m, R' (e i) (cols (σ (.inr i)))) := by
  rw [← Matrix.det_transpose,Matrix.det_apply']
  apply sum_congr rfl
  intro σ hσ
  rw [Fintype.prod_sum_type]
  simp [pairedMinor,mul_assoc]

theorem det_square_expansion {m : ℕ} (L R' : P → I → R)
    (e : Fin m → P) (cols : PairedIndex m → I) :
    (pairedMinor L R' e cols).det^2 =
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R)) *
        ∏ i : Fin m, L (e i) (cols (σ (.inl i))) * L (e i) (cols (τ (.inl i))) *
          R' (e i) (cols (σ (.inr i))) * R' (e i) (cols (τ (.inr i))) := by
  rw [pow_two,det_row_expansion,sum_mul_sum]
  apply sum_congr rfl
  intro σ hσ
  apply sum_congr rfl
  intro τ hτ
  simp only [prod_mul_distrib]
  ring

/-- The tuple sum is a product of fourth mixed tensor entries. Thus no
enumeration of all ordered `m`-tuples is required to compute this score. -/
theorem tuple_sum_tensor_expansion {m : ℕ} (L R' : P → I → R)
    (cols : PairedIndex m → I) :
    (∑ e : Fin m → P, (pairedMinor L R' e cols).det^2) =
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R)) *
        ∏ i : Fin m, tensor L R' (cols (σ (.inl i))) (cols (τ (.inl i)))
          (cols (σ (.inr i))) (cols (τ (.inr i))) := by
  simp_rw [det_square_expansion]
  rw [sum_comm]
  apply sum_congr rfl
  intro σ hσ
  rw [sum_comm]
  apply sum_congr rfl
  intro τ hτ
  rw [← mul_sum]
  congr 1
  exact (Fintype.prod_sum (fun i (x : P) =>
    L x (cols (σ (.inl i))) * L x (cols (τ (.inl i))) *
      R' x (cols (σ (.inr i))) * R' x (cols (τ (.inr i))))).symm

theorem minorWeight_intCast {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) :
    (minorWeight A : ℤ) = ∑ f : Fin d → Fin Λ, (A.submatrix id f).det^2 := by
  simp [minorWeight,Int.natCast_natAbs,sq_abs]

theorem rowWeight_intCast {ι : Type*} [Fintype ι] [DecidableEq ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) :
    (rowWeight A : ℤ) = ∑ cols : ι → Fin Λ, (Matrix.det (fun i j => A i (cols j)))^2 := by
  let e := (Fintype.equivFin ι).symm
  let Φ := Equiv.arrowCongr e (Equiv.refl (Fin Λ))
  let M : Matrix (Fin (Fintype.card ι)) (Fin Λ) ℤ := fun i j => A (e i) j
  change (minorWeight M : ℤ) = _
  rw [minorWeight_intCast]
  calc
    _ = ∑ cols : Fin (Fintype.card ι) → Fin Λ,
        (Matrix.det (fun i j => A i (Φ cols j)))^2 := by
      apply sum_congr rfl
      intro cols hcols
      have hh := Matrix.det_submatrix_equiv_self e
        (fun i j => A i (Φ cols j))
      congr 1
      calc
        _ = (Matrix.submatrix (fun i j => A i (Φ cols j)) e e).det := by
          congr 1
          ext i j
          change A (e i) (cols j) = A (e i) (Φ cols (e j))
          simp [Φ,Equiv.arrowCongr]
        _ = _ := hh
    _ = _ := Φ.sum_comp (fun cols : ι → Fin Λ =>
      (Matrix.det (fun i j => A i (cols j)))^2)

/-- The exact natural potential cast to integers is computed by fourth mixed
channels followed by a fixed-degree polynomial in those channel values. -/
theorem full_potential_tensor_expansion {m Λ : ℕ} (L R' : P → Fin Λ → ℤ) :
    ((∑ e : Fin m → P, rowWeight (Sum.elim (fun i => L (e i)) (fun i => R' (e i)))) : ℤ) =
      ∑ cols : PairedIndex m → Fin Λ,
      ∑ σ : Equiv.Perm (PairedIndex m), ∑ τ : Equiv.Perm (PairedIndex m),
        (((Equiv.Perm.sign σ : ℤ) : ℤ) * ((Equiv.Perm.sign τ : ℤ) : ℤ)) *
        ∏ i : Fin m, tensor L R' (cols (σ (.inl i))) (cols (τ (.inl i)))
          (cols (σ (.inr i))) (cols (τ (.inr i))) := by
  simp only [Nat.cast_sum,rowWeight_intCast]
  rw [sum_comm]
  apply sum_congr rfl
  intro cols hcols
  exact tuple_sum_tensor_expansion L R' cols

end ThreeSum.TernaryPairedTensor
