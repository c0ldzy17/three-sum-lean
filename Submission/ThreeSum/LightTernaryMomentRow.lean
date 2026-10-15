import Submission.ThreeSum.LightTernaryMomentGather
import Submission.ThreeSum.LightMomentZeroDetector

/-! One literal wanted record: original-A lookup, moment gather, exact detector. -/
noncomputable section
namespace ThreeSum.LightTernaryMomentRow
open Light FiniteMomentZeroDetector

def body (H pGather pDetector : ℕ) : Stmt :=
  .set 7 (M (v 0)) ;;
  .set 8 (M (v 1 +' v 7)) ;;
  .call pGather [v 3,v 4,v 5,v 6,k (2*H+1)] 9 ;;
  .call pDetector [v 6,v 8] 0

def time (H : ℕ) : ℕ := LightTernaryMomentGather.time (2*H+1)+
  LightMomentDeterminant.time (LightMomentZeroDetector.atoms H) H+100

structure Procs (H : ℕ) (P : Program) (pMain : ℕ) where
  pGather : ℕ
  pDetector : ℕ
  gather : P[pGather]?=some LightTernaryMomentGather.body
  detector : P[pDetector]?=some (LightMomentDeterminant.body (LightMomentZeroDetector.atoms H) H)
  main : P[pMain]?=some (body H pGather pDetector)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {H pMain : ℕ} (S : Procs H P pMain)
    {μ : ℕ→ℤ} {record originalA originalCount matrix count row scratch position U t : ℕ}
    (a : ℤ) (v w : Fin t→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hr : row<count) (hpos : position<originalCount)
    (hrecord : record+3≤scratch) (hAarray : originalA+originalCount≤scratch)
    (hmatrix : matrix+(2*H+1)*count≤scratch) (hspace : scratch+(2*H+1)≤lim.space)
    (hposition : μ record=(position : ℤ)) (hAread : μ (originalA+position)=a)
    (ha : |a|≤(U : ℤ))
    (hword : max (U : ℤ) (LightMomentDeterminant.wordBound U H)≤lim.word)
    (hv : Function.Injective v) (hweights : ∀ s, w s≠0) (ht : t≤H)
    (hmabs : ∀ k≤2*H, |moment v w k|≤(U : ℤ))
    (hm : ∀ k≤2*H, μ (matrix+k*count+row)=moment v w k) :
    Meets lim P pMain d [record,originalA,originalCount,matrix,count,row,scratch] μ (time H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ Kept μ ν scratch) := by
  classical
  have hU : (U : ℤ)≤lim.word := (le_max_left _ _).trans hword
  have hdet : LightMomentDeterminant.wordBound (U : ℤ) H≤lim.word := (le_max_right _ _).trans hword
  have hb := abs_le.mp ha
  have hpword : (position : ℤ)≤lim.word := by
    have hh : position≤lim.space := by omega
    exact (Int.ofNat_le.mpr hh).trans hw
  apply Meets.of_body S.main
  unfold body time
  light_set (position : ℕ) using hposition,LightTernaryMomentGather.time,LightMomentDeterminant.time
  light_set a using hAread,LightTernaryMomentGather.time,LightMomentDeterminant.time
  light_call (LightTernaryMomentGather.meets (d := d+1) (μ := μ)
    (matrix := matrix) (count := count) (row := row) (scratch := scratch)
    (terms := 2*H+1) (U := U) S.gather (fun k => moment v w k) hw hr hmatrix hspace
    (fun k hk => hm k (by omega)) (fun k hk => hmabs k (by omega)) hU)
    using LightTernaryMomentGather.time,LightMomentDeterminant.time
      with r ν ⟨hgather,hkeep⟩
  have hread : ∀ k≤2*H, ν (scratch+k)=moment v w k := fun k hk => hgather k (by omega)
  have hbound : ∀ k≤2*H, |ν (scratch+k)|≤(U : ℤ) := by
    intro k hk
    rw [hread k hk]
    exact hmabs k hk
  light_call (LightMomentZeroDetector.meets H scratch a ν v w hv hweights ht S.detector
    hspace hw (U : ℤ) (Int.natCast_nonneg U) ha hdet hbound hread)
    using LightTernaryMomentGather.time,LightMomentDeterminant.time
      with flag ξ ⟨hflag,hmem⟩
  subst ξ
  refine ⟨?_,?_⟩
  · exact hflag
  · intro i hi
    exact hkeep i (Or.inl hi)

def program (H : ℕ) : Program :=
  [body H 1 2,LightTernaryMomentGather.body,
    LightMomentDeterminant.body (LightMomentZeroDetector.atoms H) H]

def procs (H : ℕ) : Procs H (program H) 0 := ⟨1,2,rfl,rfl,rfl⟩

end ThreeSum.LightTernaryMomentRow
