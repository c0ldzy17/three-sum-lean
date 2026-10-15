import Submission.ThreeSum.LightTernaryMomentChannels
import Submission.ThreeSum.LightTernaryMomentAccumulate

/-! One actual signed moment channel: original-source weight passes, the
registered source-count procedure, and in-place matrix-row accumulation.
The count procedure's execution theorem is passed compositionally; this
module does not postulate a count operation or a primitive query oracle. -/
namespace ThreeSum.LightTernaryMomentChannelStep
open Light TernaryWeightChannels
set_option maxHeartbeats 1500000

def callArgs (positions : List ℕ) : List Expr := positions.map v
def values (positions : List ℕ) (vals : List ℤ) : List ℤ := positions.map (frame vals)

theorem callArgs_spec {lim : Limits} {loc μ : ℕ→ℤ} (positions : List ℕ) (vals : List ℤ)
    (hloc : ∀ i∈positions, loc i=frame vals i)
    (hword : ∀ i∈positions, |frame vals i|≤lim.word) :
    (∀ e∈callArgs positions, e.Safe lim ⟨loc,μ⟩) ∧
      (callArgs positions).map (·.val ⟨loc,μ⟩)=values positions vals := by
  constructor
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    simp only [v,Expr.Safe]
  · simp only [callArgs,values,List.map_map,Function.comp_def,v,Expr.val]
    exact List.map_congr_left hloc

@[simp] theorem callArgs_cost (positions : List ℕ) :
    ((callArgs positions).map Expr.cost).sum=positions.length := by
  induction positions with
  | nil => rfl
  | cons i is ih =>
    simp only [callArgs,List.map_cons,List.sum_cons,List.length_cons,Expr.cost] at *
    omega

/-- Arguments are original B/count, original C/count, left/right reusable
weight bases, moment matrix, wanted count, channel output, then backend
arguments. Backend positions refer to this unchanged argument frame. -/
def args (originalB nB originalC nC leftWeight rightWeight matrix count out : ℕ)
    (backend : List ℤ) : List ℤ :=
  [(originalB : ℤ),nB,originalC,nC,leftWeight,rightWeight,matrix,count,out]++backend

def body (k j pLeft pRight pHost pAdd : ℕ) (positions : List ℕ) (arity : ℕ) : Stmt :=
  .call pLeft [v 0,v 1,v 4] 0 ;;
  .call pRight [v 2,v 3,v 5] 0 ;;
  .call pHost (callArgs positions) 0 ;;
  .call pAdd [v 6 +' Light.k k *' v 7,v 8,v 7] 0 ;;
  .set 0 (Light.k 0)

def time (k j nB nC count hostTime hostArity : ℕ) : ℕ :=
  LightTernaryScalarChannel.time (leftMoment k j) nB+
  LightTernaryScalarChannel.time (rightMoment k j) nC+
  hostTime+LightTernaryMomentAccumulate.time count+hostArity+300

structure Procs (k j : ℕ) (positions : List ℕ) (arity : ℕ) (P : Program) (pMain : ℕ) where
  pLeft : ℕ
  pRight : ℕ
  pHost : ℕ
  pAdd : ℕ
  left : P[pLeft]?=some (LightTernaryScalarChannel.body (leftMoment k j))
  right : P[pRight]?=some (LightTernaryScalarChannel.body (rightMoment k j))
  add : P[pAdd]?=some LightTernaryMomentAccumulate.body
  main : P[pMain]?=some (body k j pLeft pRight pHost pAdd positions arity)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {k j pMain originalB nB originalC nC leftWeight rightWeight
      matrix count out U V hostTime : ℕ} {backend : List ℤ} {positions : List ℕ}
    (S : Procs k j positions (9+backend.length) P pMain)
    (μ : ℕ→ℤ) (B C accum score : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+1<lim.depth)
    (hBspace : originalB+nB≤leftWeight) (hCspace : originalC+nC≤leftWeight)
    (hmatrix : matrix+k*count+count≤leftWeight)
    (hleft : leftWeight+nB≤rightWeight) (hright : rightWeight+nC≤lim.space)
    (houtBefore : leftWeight≤out) (hout : out+count≤lim.space)
    (hleftSpace : leftWeight≤lim.space)
    (hB : ∀ i<nB, μ (originalB+i)=B i) (hC : ∀ i<nC, μ (originalC+i)=C i)
    (hBabs : ∀ i<nB, |B i|≤(U : ℤ)) (hCabs : ∀ i<nC, |C i|≤(U : ℤ))
    (haccum : ∀ i<count, μ (matrix+k*count+i)=accum i)
    (hbounded : ∀ i<count, |accum i|≤(V : ℤ) ∧ |score i|≤(V : ℤ))
    (hleftWord : max (U : ℤ) (2*((k.choose j : ℤ)+1)*((U : ℤ)+2)^j)≤lim.word)
    (hrightWord : max (U : ℤ) (2*((U : ℤ)+1)^(k-j))≤lim.word)
    (haddWord : 2*(V : ℤ)≤lim.word) (hkWord : (k : ℤ)≤lim.word)
    (hpositions : ∀ a∈positions, 9≤a ∧ a<9+backend.length)
    (hargsWord : ∀ z∈args originalB nB originalC nC leftWeight rightWeight matrix count out backend,
      |z|≤lim.word)
    (hhost : ∀ ν, Kept μ ν leftWeight →
      (∀ i<nB, ν (leftWeight+i)=(k.choose j : ℤ)*(-(B i))^j) →
      (∀ i<nC, ν (rightWeight+i)=(C i)^(k-j)) →
      Meets lim P S.pHost (d+1)
        (values positions (args originalB nB originalC nC leftWeight rightWeight matrix count out backend))
        ν hostTime (fun _ ξ => Kept ν ξ leftWeight ∧ ∀ i<count, ξ (out+i)=score i)) :
    Meets lim P pMain d
      (args originalB nB originalC nC leftWeight rightWeight matrix count out backend) μ
      (time k j nB nC count hostTime positions.length)
      (fun r ν => r=0 ∧ (∀ i<count, ν (matrix+k*count+i)=accum i+score i) ∧
        ∀ a<leftWeight, (a<matrix+k*count ∨ matrix+k*count+count≤a) → ν a=μ a) := by
  let vals := args originalB nB originalC nC leftWeight rightWeight matrix count out backend
  have hleftEnd : leftWeight+nB≤lim.space := by omega
  have hrowEnd : matrix+k*count+count≤lim.space := by omega
  have hBsafe : LightArray.SourceSafe originalB leftWeight nB :=
    Or.inr (Or.inl hBspace)
  have hCsafe : LightArray.SourceSafe originalC rightWeight nC :=
    Or.inr (Or.inl (by omega))
  have hwordFrame (a : ℕ) (ha : a<9+backend.length) : |frame vals a|≤lim.word := by
    apply hargsWord
    have hlen : vals.length=9+backend.length := by simp [vals,args]; omega
    change vals.getD a 0∈vals
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  apply Meets.of_body S.main
  unfold body time args
  light_call (LightTernaryMomentChannels.left_meets S.left μ B hw (by omega) hleftEnd
    hBsafe hB hBabs hleftWord) using LightTernaryMomentAccumulate.time,frame_setLocal
    with rL μL ⟨hL,hkeepL⟩
  have hprefixL : Kept μ μL leftWeight := fun a ha => hkeepL a (Or.inl ha)
  have hCreadL : ∀ i<nC, μL (originalC+i)=C i := by
    intro i hi
    exact (hprefixL _ (by omega)).trans (hC i hi)
  light_call (LightTernaryMomentChannels.right_meets S.right μL C hw (by omega) hright
    hCsafe hCreadL hCabs hrightWord) using LightTernaryMomentAccumulate.time,frame_setLocal
    with rR μR ⟨hR,hkeepR⟩
  have hprefixR : Kept μ μR leftWeight := by
    intro a ha
    exact (hkeepR a (Or.inl (by omega))).trans (hprefixL a ha)
  have hLreadR : ∀ i<nB, μR (leftWeight+i)=(k.choose j : ℤ)*(-(B i))^j := by
    intro i hi
    exact (hkeepR _ (Or.inl (by omega))).trans (hL i hi)
  have hhostArgs :
      (∀ e∈callArgs positions, e.Safe lim ⟨frame
        (setLocal (setLocal vals 0 rL) 0 rR),μR⟩) ∧
      (callArgs positions).map (·.val ⟨frame
        (setLocal (setLocal vals 0 rL) 0 rR),μR⟩)=
        values positions vals := by
    apply callArgs_spec
    · intro a ha
      have hp := hpositions a ha
      simp only [frame_setLocal,show a≠0 by omega,ite_false]
    · intro a ha
      exact hwordFrame a (hpositions a ha).2
  light_head
  refine Ends.callToThen (hhost μR hprefixR hLreadR hR) ?_ (ha := hhostArgs)
    (hT := by light_time [LightTernaryMomentAccumulate.time])
  intro rH μH ⟨hkeepH,hscore⟩
  have hprefixH : Kept μ μH leftWeight := fun a ha => (hkeepH a ha).trans (hprefixR a ha)
  have haccumH : ∀ i<count, μH (matrix+k*count+i)=accum i := by
    intro i hi
    exact (hprefixH _ (by omega)).trans (haccum i hi)
  have hsep : LightArray.SourceSafe out (matrix+k*count) count := Or.inr (Or.inr (by omega))
  have hmulWord : (k : ℤ)*(count : ℤ)≤lim.word := by
    have hh : k*count≤lim.space := by omega
    have hh' : (k : ℤ)*(count : ℤ)≤(lim.space : ℤ) := by exact_mod_cast hh
    exact hh'.trans hw
  have haddr : ((matrix : ℤ)+(k : ℤ)*(count : ℤ)).toNat=matrix+k*count := by norm_cast
  light_call (LightTernaryMomentAccumulate.meets S.add μH accum score hw hrowEnd hout hsep
    haccumH hscore hbounded haddWord) using haddr,LightTernaryMomentAccumulate.time,frame_setLocal
    with rA ν ⟨hrow,hkeepA⟩
  light_set (0 : ℤ) using LightTernaryMomentAccumulate.time,frame_setLocal
  refine ⟨rfl,hrow,?_⟩
  intro a ha haway
  exact (hkeepA a haway).trans (hprefixH a ha)

end ThreeSum.LightTernaryMomentChannelStep
