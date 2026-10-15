import Submission.ThreeSum.TernaryArenaPrefixPairs
import Submission.ThreeSum.TernaryPairedMinorReindex
import Submission.ThreeSum.TernaryNativeTensorScore

noncomputable section
namespace ThreeSum.TernaryArenaPrefixPotential
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryArenaPrefixGroups TernaryArenaPrefixPairs
open TernaryNativePrefixLineage TernaryPairedPotential TernaryPairedContraction
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : TernaryGoodOutputCatalog.Output m)

abbrev Index (r K : ℕ) := Σ j : Fin (S (r := r) maps τ cap I L R row root Q).front.count,
  Fin K→TernaryNativePairMoments.Pair (S (r := r) maps τ cap I L R row root Q) j.val

def equiv (r K : ℕ) : Index maps τ cap I L R row root Q r K≃
    (M maps τ cap I L R row root).Index r K :=
  Equiv.sigmaCongr (groupEquiv maps τ cap I L R row root r)
    (fun j => Equiv.piCongrRight (fun _ : Fin K => pairEquiv (maps := maps) (τ := τ) (cap := cap)
      (I := I) (L := L) (R := R) (row := row) (root := root) (Q := Q) j))

def matrix {r K : ℕ} (x : Index maps τ cap I L R row root Q r K) :
    Matrix (Fin (K+K)) (Fin Λ) ℤ := fun i =>
  Sum.elim (fun k => L (x.2 k).val.1.1) (fun k => R (x.2 k).val.2.1) (finSumFinEquiv.symm i)

theorem matrix_equiv {r K : ℕ} (x : Index maps τ cap I L R row root Q r K) :
    (M maps τ cap I L R row root).matrix (equiv maps τ cap I L R row root Q r K x)=
      matrix maps τ cap I L R row root Q x := rfl

def value (r K : ℕ) : ℕ := potential (matrix maps τ cap I L R row root Q (r := r) (K := K))

/-- Literal physical positions, local dictionary tuple indices, actual wanted
ordinals and every K-tuple are in bijection with the retained prefix model. -/
theorem value_eq_model (r K : ℕ) : value maps τ cap I L R row root Q r K=
    potential ((M maps τ cap I L R row root).matrix (r := r) (K := K)) := by
  unfold value potential
  have hh := (equiv maps τ cap I L R row root Q r K).sum_comp
    (fun x => minorWeight ((M maps τ cap I L R row root).matrix x))
  simpa only [matrix_equiv] using hh

theorem value_eq_native {J : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input)
    (A B : ℕ→ℕ→ℤ) (row : ℕ→(Fin (J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (root : ℕ→ℕ→ZMod p) (Q : TernaryGoodOutputCatalog.Output m) (r K : ℕ) :
    value maps τ cap I (fun i t => A i t.val) (fun i t => B i t.val) row root Q r K=
      TernaryNativeTensorScore.pairedPotential
        (S (r := r) maps τ cap I (fun i t => A i t.val) (fun i t => B i t.val) row root Q) K J A B := by
  unfold value potential TernaryNativeTensorScore.pairedPotential
  rw [Fintype.sum_sigma]
  apply sum_congr rfl
  intro j hj
  apply sum_congr rfl
  intro e he
  rw [TernaryPairedMinorReindex.paired_rowWeight]
  rfl

end ThreeSum.TernaryArenaPrefixPotential
