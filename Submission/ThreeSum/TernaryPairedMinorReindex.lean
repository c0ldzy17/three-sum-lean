import Submission.ThreeSum.TernaryPairedPotential

noncomputable section
namespace ThreeSum.TernaryPairedMinorReindex
open Matrix Finset TernaryPairedPotential
open scoped BigOperators

theorem minorWeight_rows {d Λ : ℕ} (A : Matrix (Fin d) (Fin Λ) ℤ) (e : Equiv.Perm (Fin d)) :
    minorWeight (fun i => A (e i))=minorWeight A := by
  unfold minorWeight
  apply sum_congr rfl
  intro f hf
  congr 1
  have hh := Matrix.abs_det_submatrix_equiv_equiv e (Equiv.refl (Fin d)) (A.submatrix id f)
  have he : (fun i j => A (e i) (f j))=(A.submatrix id f).submatrix e (Equiv.refl _) := rfl
  change (Matrix.submatrix (fun i => A (e i)) id f).det.natAbs=(A.submatrix id f).det.natAbs
  change |(Matrix.submatrix (fun i => A (e i)) id f).det|=|(A.submatrix id f).det| at hh
  rw [←Int.natCast_natAbs,←Int.natCast_natAbs] at hh
  exact Int.ofNat_inj.mp hh

theorem rowWeight_equiv {ι : Type*} [Fintype ι] {Λ d : ℕ}
    (A : ι→Fin Λ→ℤ) (e : Fin d≃ι) :
    rowWeight A=minorWeight (fun i => A (e i)) := by
  have hd : Fintype.card ι=d := (Fintype.card_congr e).symm.trans (Fintype.card_fin d)
  subst d
  let t : Equiv.Perm (Fin (Fintype.card ι)) := e.trans (Fintype.equivFin ι)
  have he : (fun i => A (e i))=(fun i => A ((Fintype.equivFin ι).symm (t i))) := by
    funext i
    simp [t]
  rw [he]
  exact (minorWeight_rows (fun i j => A ((Fintype.equivFin ι).symm i) j) t).symm

theorem paired_rowWeight {K Λ : ℕ} (L R : Fin K→Fin Λ→ℤ) :
    rowWeight (Sum.elim L R)=
      minorWeight (fun i => Sum.elim L R (finSumFinEquiv.symm i)) :=
  rowWeight_equiv _ finSumFinEquiv.symm

end ThreeSum.TernaryPairedMinorReindex
