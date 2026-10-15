import Submission.ThreeSum.TernaryPairedSupport
import Submission.ThreeSum.TernaryOriginalRowMenu
import Submission.ThreeSum.TernaryCoverUniformRank
import Mathlib.LinearAlgebra.Matrix.Nonsingular
import Mathlib.Data.ZMod.Basic
import Submission.ThreeSum.TernaryCoverOutputCap
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! The actual nonnegative integer sum of squared paired minors.
All ordered column selections are retained. Repeated columns contribute zero,
and using ordered selections only changes a fixed factor in the potential. -/

noncomputable section
namespace ThreeSum.TernaryPairedPotential

open Finset Matrix
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K : Type*} [Field K] [DecidableEq K]

theorem exists_nonsingular_column_selection {d Λ : ℕ}
    (A : Matrix (Fin d) (Fin Λ) K) (hA : LinearIndependent K A) :
    ∃ f : Fin d → Fin Λ, (A.submatrix id f).det ≠ 0 := by
  have hdim : Module.finrank K (Submodule.span K (Set.range fun j => fun i => A i j)) = d := by
    have he := TernaryCoverUniformRank.row_rank_eq_column_rank (fun i j => A i j)
    have hr : Module.finrank K (Submodule.span K (Set.range fun i => fun j => A i j)) = d := by
      simpa using finrank_span_eq_card hA
    exact he.symm.trans hr
  have hex : ∃ f : Fin d → Fin d → K,
      (∀ i, f i ∈ Set.range (fun j => fun i => A i j)) ∧
      Submodule.span K (Set.range f) =
        Submodule.span K (Set.range (fun j => fun i => A i j)) ∧ LinearIndependent K f := by
    have hh := Submodule.exists_fun_fin_finrank_span_eq K
      (Set.range (fun j => fun i => A i j))
    rw [hdim] at hh
    exact hh
  obtain ⟨f,hf,hspan,hind⟩ := hex
  let pick : Fin d → Fin Λ := fun i => Classical.choose (hf i)
  have hpick (i : Fin d) : (fun j => A j (pick i)) = f i := Classical.choose_spec (hf i)
  refine ⟨pick, Matrix.nonsingular_iff_det_ne_zero.mp
    (Matrix.linearIndependent_col_iff.mp ?_)⟩
  have he : (A.submatrix id pick).col = f := by
    funext i j
    exact congrFun (hpick i) j
  rw [he]
  exact hind

def minorWeight {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) : ℕ :=
  ∑ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs ^ 2

theorem minorWeight_pos_of_mod_independent {d Λ : ℕ}
    (A : Matrix (Fin d) (Fin Λ) ℤ) (ρ : ℤ →+* K)
    (hA : LinearIndependent K (fun i j => ρ (A i j))) :
    0 < minorWeight A := by
  obtain ⟨f,hf⟩ := exists_nonsingular_column_selection (fun i j => ρ (A i j)) hA
  have hd : (A.submatrix id f).det ≠ 0 := by
    intro hz
    apply hf
    have he := ρ.map_det (A.submatrix id f)
    change (ρ.mapMatrix (A.submatrix id f)).det = 0
    rw [← he,hz,map_zero]
  unfold minorWeight
  exact sum_pos_iff.mpr ⟨f,mem_univ _,pow_pos (Int.natAbs_pos.mpr hd) 2⟩

def pairedMatrix {m Λ : ℕ} (L R : Fin m → Fin Λ → ℤ) :
    Matrix (Fin m ⊕ Fin m) (Fin Λ) ℤ := Sum.elim L R

theorem mod_independent_of_minorWeight_pos {d Λ p : ℕ} [Fact p.Prime]
    (A : Matrix (Fin d) (Fin Λ) ℤ) (hw : 0 < minorWeight A)
    (hsmall : ∀ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs < p) :
    LinearIndependent (ZMod p) (fun i j => (A i j : ZMod p)) := by
  obtain ⟨f,hf,hpos⟩ := sum_pos_iff.mp hw
  have hd : (A.submatrix id f).det ≠ 0 := by
    intro hz
    simp [hz] at hpos
  have hm : (((Int.castRingHom (ZMod p)).mapMatrix (A.submatrix id f)).det) ≠ 0 := by
    intro hz
    have he := (Int.castRingHom (ZMod p)).map_det (A.submatrix id f)
    rw [hz] at he
    have hdvd : (p : ℤ) ∣ (A.submatrix id f).det :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp he
    exact hd (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdvd (by simpa using hsmall f))
  have hi := Matrix.linearIndependent_row_iff.mpr (Matrix.nonsingular_iff_det_ne_zero.mpr hm)
  let restrict : (Fin Λ → ZMod p) →ₗ[ZMod p] (Fin d → ZMod p) :=
    LinearMap.pi fun i => LinearMap.proj (f i)
  exact LinearIndependent.of_comp restrict hi

def rowWeight {ι : Type*} [Fintype ι] {Λ : ℕ} (A : ι → Fin Λ → ℤ) : ℕ :=
  minorWeight (fun i => A ((Fintype.equivFin ι).symm i))

theorem rowWeight_pos_of_mod_independent {ι : Type*} [Fintype ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) (ρ : ℤ →+* K)
    (hA : LinearIndependent K (fun i j => ρ (A i j))) : 0 < rowWeight A := by
  exact minorWeight_pos_of_mod_independent _ ρ
    (hA.comp (Fintype.equivFin ι).symm (Fintype.equivFin ι).symm.injective)

theorem mod_independent_of_rowWeight_pos {ι : Type*} [Fintype ι] {Λ p : ℕ} [Fact p.Prime]
    (A : ι → Fin Λ → ℤ) (hw : 0 < rowWeight A)
    (hsmall : ∀ f : Fin (Fintype.card ι) → Fin Λ,
      (Matrix.submatrix (fun i => A ((Fintype.equivFin ι).symm i)) id f).det.natAbs < p) :
    LinearIndependent (ZMod p) (fun i j => (A i j : ZMod p)) := by
  have hh := mod_independent_of_minorWeight_pos
    (fun i => A ((Fintype.equivFin ι).symm i)) hw hsmall
  have hc := hh.comp (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  simpa only [Function.comp_def,Equiv.symm_apply_apply] using hc

theorem minor_natAbs_le {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ b) (f : Fin d → Fin Λ) :
    (A.submatrix id f).det.natAbs ≤ d.factorial*b^d := by
  have he : ∀ i j, |(A.submatrix id f) i j| ≤ (b : ℤ) := by
    intro i j
    change |A i (f j)| ≤ (b : ℤ)
    rw [← Int.natCast_natAbs]
    exact_mod_cast hA i (f j)
  have hh := Matrix.det_le (abv := AbsoluteValue.abs) he
  simp only [AbsoluteValue.abs_apply,Fintype.card_fin,nsmul_eq_mul,
    ← Int.natCast_natAbs] at hh
  exact_mod_cast hh

theorem minor_small_of_entry_bound {d Λ p : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ)
    (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ b) (hp : d.factorial*b^d < p) :
    ∀ f : Fin d → Fin Λ, (A.submatrix id f).det.natAbs < p := by
  intro f
  exact (minor_natAbs_le A b hA f).trans_lt hp

theorem minorWeight_le {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) (b : ℕ)
    (hA : ∀ i j, (A i j).natAbs ≤ b) :
    minorWeight A ≤ Λ^d*(d.factorial*b^d)^2 := by
  unfold minorWeight
  calc
    _ ≤ ∑ _f : Fin d → Fin Λ, (d.factorial*b^d)^2 :=
      sum_le_sum fun f hf => Nat.pow_le_pow_left (minor_natAbs_le A b hA f) 2
    _ = _ := by simp

theorem rowWeight_le {ι : Type*} [Fintype ι] {Λ : ℕ}
    (A : ι → Fin Λ → ℤ) (b : ℕ) (hA : ∀ i j, (A i j).natAbs ≤ b) :
    rowWeight A ≤ Λ^(Fintype.card ι)*((Fintype.card ι).factorial*b^(Fintype.card ι))^2 :=
  minorWeight_le _ b (fun i j => hA _ _)

end ThreeSum.TernaryPairedPotential
