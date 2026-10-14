import Submission.ThreeSum.LightTernaryEulerScan

/-!
# Actual ascending-rank outside-bank memoization

The outer machine visits each rank layer once and scans the exact nearword
rows. Strictly lower predecessor ranks ensure all reads come from the fixed
bank or previously filled memo cells. Neither recursion nor a full bank copy
is charged as one operation.
-/

namespace ThreeSum.LightTernaryEulerMemo

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 12000

def Ready (μ ν : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (vals rows T stage : ℕ) : Prop :=
  Kept μ ν vals ∧ ∀ j < rows, rank j ≤ T+stage → ν (vals+j)=f j

theorem Ready.next {μ ν ξ : ℕ → ℤ} {f : ℕ → ℤ} {rank : ℕ → ℕ}
    {vals rows T fr stage : ℕ} (H : Ready μ ν f rank vals rows T stage)
    (hvals : vals+rows ≤ fr)
    (hs : LightTernaryEulerScan.Stored ν ξ f rank vals (T+stage+1) fr rows) :
    Ready μ ξ f rank vals rows T (stage+1) := by
  constructor
  · intro a ha
    rw [hs a (by omega),LightTernaryEulerScan.stageValue_below ν f rank ha]
    exact H.1 a ha
  · intro j hj hr
    rw [hs (vals+j) (by omega)]
    by_cases hc : rank j=T+stage+1
    · simp [LightTernaryEulerScan.stageValue,hc,hj]
    · have hp : rank j≤T+stage := by omega
      simpa [LightTernaryEulerScan.stageValue,hc] using H.2 j hj hp

def loopBody (pScan : ℕ) : Stmt :=
  .call pScan [v 0,v 1,v 2,v 3,v 4,v 5,v 6 +' v 11 +' k 1,v 7,v 9,v 10] 12

def body (pScan : ℕ) : Stmt :=
  .for 11 (v 8 -' v 6) (loopBody pScan) ;;
  .set 0 (k 0)

def time (N rows stages V : ℕ) : ℕ :=
  stages*(LightTernaryEulerScan.time N rows V+150)+100

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (rank : ℕ → ℕ)
    (N rows ws ks ranks vals T h maxRank pcount fr stage : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [N,rows,ws,ks,ranks,vals,T,h,maxRank,pcount,fr,stage,rval],ν⟩ ∧
      Ready μ ν f rank vals rows T stage

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pScan pFill pRow pSum pDivide pNaturalDivide N rows ws ks ranks vals T h maxRank pcount fr U V : ℕ}
    (hmain : P[pMain]?=some (body pScan))
    (hscan : P[pScan]?=some (LightTernaryEulerScan.body pFill))
    (hfill : P[pFill]?=some (LightTernaryEulerRow.fillBody pRow))
    (hrow : P[pRow]?=some (LightTernaryEulerRow.body pSum pDivide))
    (hsum : P[pSum]?=some LightTernaryWeightedSum.body)
    (hdivide : P[pDivide]?=some (LightTernaryDivide.body pNaturalDivide))
    (hnatural : P[pNaturalDivide]?=some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (weights keys : ℕ → ℕ → ℕ) (g f : ℕ → ℤ) (rank : ℕ → ℕ)
    (F : ∀ current, T<current → current≤maxRank → Light.Emod.Pre lim (current-h) V fr)
    (hT : T≤maxRank) (hh : h≤T)
    (hws : ws+N*rows ≤ vals) (hks : ks+N*rows ≤ vals) (hranks : ranks+rows ≤ vals)
    (hvals : vals+rows ≤ fr) (hspace : pcount ≤ lim.space)
    (hrankRead : ∀ j < rows, μ (ranks+j)=(rank j : ℤ))
    (hrankRange : ∀ j < rows, T<rank j ∧ rank j≤maxRank)
    (hweights : ∀ j < rows, ∀ i < N, μ (ws+N*j+i)=(weights j i : ℤ))
    (hkeys : ∀ j < rows, ∀ i < N, μ (ks+N*j+i)=(keys j i : ℤ))
    (hrange : ∀ j < rows, ∀ i < N, keys j i < pcount ∧ keys j i < fr)
    (hbank : ∀ j < rows, ∀ i < N, keys j i<vals → μ (keys j i)=g (keys j i))
    (hmemo : ∀ j < rows, g (vals+j)=f j)
    (hweight : ∀ j < rows, ∀ i < N, weights j i ≤ 2)
    (hvalue : ∀ j < rows, ∀ i < N, |g (keys j i)| ≤ U)
    (hpre : ∀ j < rows, ∀ i < N,
      keys j i<vals ∨ ∃ k<rows, keys j i=vals+k ∧ rank k<rank j)
    (hEuler : ∀ j < rows,
      LightTernaryWeightedSum.sum (weights j) (keys j) g N=(rank j-h : ℕ)*f j)
    (hV : 2*(N+1)*U ≤ V) (hd : d+5 ≤ lim.depth)
    (hword : ((N+rows+maxRank+h+pcount+fr+20 : ℕ) : ℤ) ≤ lim.word)
    (hw : (lim.space : ℤ) ≤ lim.word) (hfr : fr≤lim.space) :
    Meets lim P pMain d [N,rows,ws,ks,ranks,vals,T,h,maxRank,pcount,fr] μ
      (time N rows (maxRank-T) V)
      (fun r ν => r=0 ∧ Kept μ ν vals ∧ ∀ j<rows, ν (vals+j)=f j) := by
  have hcall {stage : ℕ} (hstage : stage<maxRank-T) (ν : ℕ → ℤ)
      (H : Ready μ ν f rank vals rows T stage) :
      Meets lim P pScan (d+1)
        [N,rows,ws,ks,ranks,vals,(T+stage+1 : ℕ),h,pcount,fr] ν
        (LightTernaryEulerScan.time N rows V)
        (fun r ξ => r=0 ∧ LightTernaryEulerScan.Stored ν ξ f rank vals (T+stage+1) fr rows) := by
    have hc : T+stage+1≤maxRank := by omega
    have hmeta {a : ℕ} (ha : a<vals) : ν a=μ a := H.1 a ha
    apply LightTernaryEulerScan.meets hscan hfill hrow hsum hdivide hnatural ν
      weights keys g f rank (F (T+stage+1) (by omega) hc)
    · omega
    · exact hws
    · exact hks
    · exact hranks
    · exact hvals
    · exact hspace
    · intro j hj
      rw [hmeta (by omega)]
      exact hrankRead j hj
    · intro j hj i hi
      have ha : ws+N*j+i<vals := by nlinarith
      rw [hmeta ha]
      exact hweights j hj i hi
    · intro j hj i hi
      have ha : ks+N*j+i<vals := by nlinarith
      rw [hmeta ha]
      exact hkeys j hj i hi
    · exact hrange
    · intro j hj hjrank i hi
      rcases hpre j hj i hi with hb | ⟨k,hk,he,hr⟩
      · rw [hmeta hb]
        exact hbank j hj i hi hb
      · rw [he,H.2 k hk (by omega),hmemo k hk]
    · exact hweight
    · intro j hj _
      exact hvalue j hj
    · intro j hj hjrank i hi k hk hkr he
      rcases hpre j hj i hi with hb | ⟨l,hl,hel,hr⟩
      · omega
      · have heq : k=l := by omega
        subst l
        omega
    · intro j hj hjrank
      simpa only [hjrank] using hEuler j hj
    · exact hV
    · omega
    · have hb : N+rows+(T+stage+1)+h+pcount+fr+20 ≤ N+rows+maxRank+h+pcount+fr+20 := by omega
      exact (Int.ofNat_le.mpr hb).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.pieceThen (Ends.for (T := (maxRank-T)*(LightTernaryEulerScan.time N rows V+150)+20)
    (Q := Inv μ f rank N rows ws ks ranks vals T h maxRank pcount fr (maxRank-T))
    (Inv μ f rank N rows ws ks ranks vals T h maxRank pcount fr)
    (maxRank-T) (LightTernaryEulerScan.time N rows V+100)
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_⟩
    · simpa [update_frame_setLocal,setLocal] using
        congrArg (fun loc => (⟨loc,μ⟩ : State))
          (frame_append_zeros ([N,rows,ws,ks,ranks,vals,T,h,maxRank,pcount,fr,0] : List ℤ) 1).symm
    · refine ⟨SameOn.refl,?_⟩
      intro j hj hr
      have hmin := (hrankRange j hj).1
      omega
  case round =>
    rintro stage _ hstage _ ⟨rval,ν,rfl,H⟩
    have hcurrent : T+stage+1≤maxRank := by omega
    have hcurrentWord : ((T+stage+1 : ℕ) : ℤ) ≤ lim.word := by omega
    have hdiff : ((maxRank-T : ℕ) : ℤ)=(maxRank : ℤ)-(T : ℤ) := Nat.cast_sub hT
    unfold loopBody
    have hc := hcall hstage ν H
    light_call hc using hdiff,LightTernaryEulerScan.time
      with result ξ ⟨hresult,hs⟩
    refine ⟨by simp,result,ξ,?_,H.next hvals hs⟩
    simp [update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound =>
    rintro stage _ hstage _ ⟨rval,ν,rfl,H⟩
    have hdiff : ((maxRank-T : ℕ) : ℤ)=(maxRank : ℤ)-(T : ℤ) := Nat.cast_sub hT
    light_side
  case after =>
    rintro _ ⟨rval,ν,rfl,H⟩
    light_set 0
    refine ⟨rfl,H.1,?_⟩
    intro j hj
    exact H.2 j hj (by have hmax := (hrankRange j hj).2; omega)

/-- The complete seven-procedure outside-bank memo arithmetic library. -/
def program : Program := [body 1,LightTernaryEulerScan.body 2,
  LightTernaryEulerRow.fillBody 3,LightTernaryEulerRow.body 4 5,
  LightTernaryWeightedSum.body,LightTernaryDivide.body 6,LightOutputDecodeDivide.body]

theorem time_bound (N rows stages V : ℕ) :
    time N rows stages V ≤
      (stages+1)*(rows+1)*(400*(N+Nat.log 2 (V+1)+3)+500) := by
  have hrow := LightTernaryEulerRow.time_bound N V
  let K := N+Nat.log 2 (V+1)+3
  have hbound : LightTernaryEulerRow.time N V ≤ 400*K := hrow
  unfold time LightTernaryEulerScan.time LightTernaryEulerRow.fillTime
  calc
    _ ≤ stages*(rows*(400*K+250)+250)+100 := by
      have hb : LightTernaryEulerRow.time N V+100+150 ≤ 400*K+250 := by omega
      have hm := Nat.mul_le_mul_left rows hb
      have hs : rows*(LightTernaryEulerRow.time N V+100+150)+100+150 ≤
          rows*(400*K+250)+250 := by omega
      exact Nat.add_le_add_right (Nat.mul_le_mul_left stages hs) 100
    _ ≤ (stages+1)*(rows+1)*(400*K+500) := by
      nlinarith
    _ = _ := rfl

end ThreeSum.LightTernaryEulerMemo
