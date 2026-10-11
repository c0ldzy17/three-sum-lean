import Submission.ThreeSum.Coloring
import Submission.ThreeSumApsp.Programs.Tasks

/-! # Exact original-position semantics at the benchmark task boundary -/

namespace ThreeSum.OriginalThreeSum

open Light ThreeSumApsp.Spec

theorem distinct_iff_end {n : ℕ} (x : Fin n → ℤ) :
    Coloring.DistinctZeroSum x ↔ EndStatement.ThreeSum.yes x := by
  constructor
  · rintro ⟨i,j,k,hij,hik,hjk,hzero⟩
    exact ⟨i,j,k,hij,hjk,hik,hzero⟩
  · rintro ⟨i,j,k,hij,hjk,hik,hzero⟩
    exact ⟨i,j,k,hij,hik,hjk,hzero⟩

theorem flag_of_decision {n : ℕ} (x : Fin n → ℤ) {r : ℤ}
    (hbool : r=0 ∨ r=1) (hcorrect : r=1 ↔ Coloring.DistinctZeroSum x) :
    r=ThreeSumApsp.flag (ThreeSumApsp.ThreeSum x) := by
  by_cases hx : Coloring.DistinctZeroSum x
  · rw [ThreeSumApsp.flag_of ((distinct_iff_end x).mp hx)]
    exact hcorrect.mpr hx
  · rw [ThreeSumApsp.flag_of_not (fun h => hx ((distinct_iff_end x).mpr h))]
    rcases hbool with h | h
    · exact h
    · exact False.elim (hx (hcorrect.mp h))

theorem task_read {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (H : x.Pre μ fr) :
    ∀ i : Fin x.N, μ (x.a+i.val)=vecOf x.N x.X i := by
  intro i
  exact H.seg.getD (by rw [H.len]; exact i.isLt) 0

theorem task_bound {x : VecInst} {μ : ℕ → ℤ} {fr : ℕ} (H : x.Pre μ fr) :
    ∀ i : Fin x.N, |vecOf x.N x.X i| ≤ (x.U : ℤ) := by
  intro i
  exact ThreeSumApsp.AbsLe.abs_getD_le (Int.natCast_nonneg _) H.le i.val

theorem task_post {x : VecInst} {μ ν : ℕ → ℤ} {fr : ℕ} {r : ℤ}
    (hbool : r=0 ∨ r=1) (hcorrect : r=1 ↔ Coloring.DistinctZeroSum (vecOf x.N x.X))
    (hkeep : Kept μ ν fr) : s3Task.Post x μ fr r ν :=
  ⟨flag_of_decision _ hbool hcorrect,hkeep⟩

end ThreeSum.OriginalThreeSum
