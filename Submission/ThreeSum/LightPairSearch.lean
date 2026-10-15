import Submission.ThreeSum.LightArray
import Submission.ThreeSum.PairFirst

namespace ThreeSum.LightPairSearch
open Light
set_option maxHeartbeats 300000
set_option maxRecDepth 18000

def rowBody (pPred : ℕ) : Stmt :=
  .for 4 (v 0)
    (.ite (v 3 =' k 0)
      (.call pPred [v 1,v 4,v 2] 5 ;;
        .ite (k 0 <' v 5) (.set 3 (k 1 +' v 1 *' v 0 +' v 4)) .skip)
      .skip) ;;
  .set 0 (v 3)

def rowTime (q T : ℕ) : ℕ := q*(T+100)+20

def RowInv (I : (ℕ → ℤ) → Prop) (q u ctx : ℕ)
    (good : ℕ → ℕ → Prop) [DecidableRel good] (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [q,u,ctx,first (goodCode q good) (u*q+j),j,r],ν⟩ ∧ I ν

variable {lim : Limits} {P : Program}

theorem row_meets {pRow pPred q u ctx T d : ℕ}
    (hrow : P[pRow]?=some (rowBody pPred))
    (good : ℕ → ℕ → Prop) [DecidableRel good] (I : (ℕ → ℤ) → Prop)
    (hq : 0<q) (hu : u<q) (μ : ℕ → ℤ) (hI : I μ)
    (hword : ((q*q+q+ctx+20 : ℕ) : ℤ) ≤ lim.word)
    (hd : d<lim.depth)
    (hpred : ∀ v<q, ∀ ν, I ν → Meets lim P pPred (d+1) [u,v,ctx] ν T
      (fun r ξ => r=(if good u v then 1 else 0) ∧ I ξ)) :
    Meets lim P pRow d [q,u,ctx,first (goodCode q good) (u*q)] μ (rowTime q T)
      (fun r ν => r=(first (goodCode q good) ((u+1)*q) : ℤ) ∧ I ν) := by
  have hqW : (q : ℤ) ≤ lim.word := by omega
  have huW : (u : ℤ) ≤ lim.word := by omega
  have hctxW : (ctx : ℤ) ≤ lim.word := by omega
  have hcode (j : ℕ) (hj : j≤q) : u*q+j≤q*q := by
    have hh := Nat.mul_le_mul_right q (show u+1≤q by omega)
    nlinarith
  apply Meets.of_body hrow
  unfold rowBody rowTime
  refine Ends.pieceThen (Ends.for (T := q*(T+100)+10)
    (Q := RowInv I q u ctx good q) (RowInv I q u ctx good) q (T+80)
    ?_ ?_ ?_ ?_ (hT := by light_time)) ?_ (hT := by light_time)
  · refine ⟨0,μ,?_,hI⟩
    simp only [Nat.add_zero,update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc,μ⟩ : State)) (frame_append_zeros _ 1).symm
  · rintro j _ hj _ ⟨rval,ν,rfl,hν⟩
    have hprefix := first_le (goodCode q good) (u*q+j)
    have hprefixNext := first_le (goodCode q good) (u*q+(j+1))
    have hjW : (j : ℤ) ≤ lim.word := by omega
    have hsmall := hcode j (by omega)
    have hsmallNext := hcode (j+1) (by omega)
    have hprod : ((u*q : ℕ) : ℤ) ≤ lim.word := by omega
    have hcodeW : ((u*q+j+1 : ℕ) : ℤ) ≤ lim.word := by omega
    have hprefW : ((first (goodCode q good) (u*q+j) : ℕ) : ℤ) ≤ lim.word := by omega
    have hgood := goodCode_pair q u j hq hj good
    light_if hz hnz : first (goodCode q good) (u*q+j)=0
    · light_call (hpred j hj ν hν) with result ξ ⟨hr,hξ⟩
      by_cases hg : good u j
      · have hr' : result=1 := by simpa only [hg,ite_true] using hr
        light_if hpos hnonpos : (0 : ℤ)<result using hr'
        · light_set (u*q+j+1 : ℕ) using Nat.add_assoc
          refine ⟨by simp,1,ξ,?_,hξ⟩
          have hgc := hgood.mpr hg
          simp [first,hz,hgc,update_frame_setLocal,Nat.add_assoc,hr']
        · omega
      · have hr' : result=0 := by simpa only [hg,ite_false] using hr
        light_if hpos hnonpos : (0 : ℤ)<result using hr'
        · omega
        · apply Ends.skip
          refine ⟨by simp,0,ξ,?_,hξ⟩
          have hgc : ¬goodCode q good (u*q+j) := by simpa only [hgood] using hg
          simp [first,hz,hgc,update_frame_setLocal,Nat.add_assoc,hr']
    · apply Ends.skip
      refine ⟨by simp,rval,ν,?_,hν⟩
      simp [first,hnz,update_frame_setLocal,Nat.add_assoc]
  · intro σ _ hshape; exact hshape
  · rintro j _ hj _ ⟨rval,ν,rfl,hν⟩; simp
  · rintro σ ⟨rval,ν,rfl,hν⟩
    have hb := first_le (goodCode q good) (u*q+q)
    have hsmall := hcode q le_rfl
    light_set (first (goodCode q good) ((u+1)*q) : ℕ) using Nat.add_mul,Nat.one_mul
    exact ⟨rfl,hν⟩

end ThreeSum.LightPairSearch
