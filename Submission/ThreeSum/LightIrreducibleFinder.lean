import Submission.ThreeSum.LightExtensionFactorSearch
import Submission.ThreeSum.LightArgumentTable
import Submission.ThreeSum.TernaryExtensionSearchCorrect
import Submission.ThreeSum.TernaryCoefficientCodes
import Submission.ThreeSum.LightTernaryRowSelector

/-! Exhaustive irreducible polynomial construction using the actual bounded
monic factor search, with runtime candidate decoding and degree headers. -/
noncomputable section
namespace ThreeSum.LightIrreducibleFinder
open Light ThreeSum.LightExtensionFactorPredicate
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

def atDegree (C : Layout) (e : ℕ) : Layout := {C with degree := e}
def factorFirst (C : Layout) (q : ℕ) (f : ℕ → ℕ) (e : ℕ) : ℕ :=
  LightPairSearch.first (LightPairSearch.goodCode q (LightExtensionFactorSearch.good (atDegree C e) f)) (q*q)

def factorTime (C : Layout) (q e : ℕ) : ℕ := q*q*(LightExtensionFactorPredicate.time (atDegree C e) q q+200)+100

def degreeFlag (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) : ℕ :=
  if ∀ t<j, factorFirst C q f (t+1)=0 then 1 else 0

def degreeRound : Stmt :=
  .call 11 [v 3,v 0,v 1,v 9 +' k 1,v 4,v 5,v 6,v 7] 10 ;;
  .call 9 [v 2,v 3] 11 ;;
  .ite (k 0 <' v 11) (.set 8 (k 0)) .skip

def degreeBody : Stmt := .set 8 (k 1) ;; .for 9 (v 1 -' k 1) degreeRound ;; .set 0 (v 8)
def degreeTime (dim T : ℕ) : ℕ := (dim-1)*(T+200)+100

def candidateBody : Stmt :=
  .call 2 [k 2 *' v 2,v 1,v 0 +' v 3,v 4,k 0,k 1,v 5,k 2 *' v 2] 9 ;;
  .call 10 [v 1,v 2,v 3,v 6,v 4,v 5,v 7,v 8] 0

def searchRound : Stmt :=
  .call 12 [v 10,v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 11 ;;
  .ite (v 11 =' k 1) (.set 9 (v 10 +' k 1)) .skip

def searchBody : Stmt := .set 9 (k 0) ;; .for 10 (v 2) searchRound ;; .set 0 (v 9)
def setupBody : Stmt :=
  .call 14 [v 3,k 2 *' v 1 +' k 1,v 0] 8 ;;
  .call 13 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7] 9 ;;
  .call 2 [k 2 *' v 1,v 0,v 9 -' k 1 +' v 2,v 3,k 0,k 1,v 4,k 2 *' v 1] 10 ;;
  .set 0 (v 9)

def tail : Program := [degreeBody,LightArgumentTable.stores 0 7,candidateBody,searchBody,powTableBody,setupBody]
def program : Program := LightExtensionFactorSearch.program++tail
@[simp] theorem program_length : program.length=16 := rfl

def DegreeInv (μ : ℕ → ℤ) (C : Layout) (q ctx : ℕ) (f : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ headerResult result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [C.p,C.dim,q,ctx,C.powers,C.target,C.left,C.right,degreeFlag C q f j,j,headerResult,result],ν⟩ ∧
      Kept μ ν ctx

theorem degreeFlag_le_one (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) : degreeFlag C q f j≤1 := by
  unfold degreeFlag; split <;> omega

theorem degreePrefix_succ (C : Layout) (q : ℕ) (f : ℕ → ℕ) (j : ℕ) :
    (∀ t<j+1, factorFirst C q f (t+1)=0) ↔
      (∀ t<j, factorFirst C q f (t+1)=0) ∧ factorFirst C q f (j+1)=0 := by
  constructor
  · intro h; exact ⟨fun t ht => h t (by omega),h j (by omega)⟩
  · rintro ⟨h,he⟩ t ht
    rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | rfl
    · exact h t ht
    · exact he

variable {lim : Limits}

theorem degree_meets (C : Layout) {q ctx T depth : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+8<lim.depth)
    (hq : 0<q) (hp : 1<C.p) (hdim : 0<C.dim)
    (hctx : ctx+7≤C.left) (hpowCtx : C.powers+(2*C.dim+1)≤ctx)
    (htargetCtx : C.target+2*C.dim≤ctx)
    (hleft : C.left+2*C.dim≤C.right) (hspace : C.right+2*C.dim≤lim.space)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ))
    (hfRead : ∀ i<2*C.dim, μ (C.target+i)=(f i : ℤ))
    (hword : ∀ e, 0<e → e<C.dim → (LightExtensionFactorPredicate.word (atDegree C e) q q : ℤ)≤lim.word)
    (hsearchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word)
    (hcontrols : ((C.p+C.dim+q+ctx+32 : ℕ) : ℤ)≤lim.word)
    (htime : ∀ e, 0<e → e<C.dim → factorTime C q e≤T) :
    Meets lim program 10 depth [C.p,C.dim,q,ctx,C.powers,C.target,C.left,C.right] μ (degreeTime C.dim T)
      (fun r ν => r=(degreeFlag C q f (C.dim-1) : ℤ) ∧ Kept μ ν ctx) := by
  apply Meets.of_body (by rfl : program[10]?=some degreeBody)
  unfold degreeBody degreeTime
  light_set 1
  refine Ends.pieceThen (Ends.for (T := (C.dim-1)*(T+200)+30)
    (Q := DegreeInv μ C q ctx f (C.dim-1)) (DegreeInv μ C q ctx f) (C.dim-1) (T+150)
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,0,μ,?_,SameOn.refl⟩
    simp [update_frame_setLocal,degreeFlag]
    change frame [(C.p : ℤ),C.dim,q,ctx,C.powers,C.target,C.left,C.right,1,0]=
      frame ([(C.p : ℤ),C.dim,q,ctx,C.powers,C.target,C.left,C.right,1,0]++[0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨headerResult,result,ν,rfl,H⟩
    have he : 0<j+1 := by omega
    have hed : j+1<C.dim := by omega
    have hdimCast : ((C.dim-1 : ℕ) : ℤ)=(C.dim : ℤ)-1 := by omega
    have hpow : ∀ i≤2*C.dim, ν (C.powers+i)=((C.p^i : ℕ) : ℤ) := by
      intro i hi; rw [H _ (by omega),hpowRead i hi]
    have hf : ∀ i<2*C.dim, ν (C.target+i)=(f i : ℤ) := by
      intro i hi; rw [H _ (by omega),hfRead i hi]
    have hh := LightArgumentTable.meets (depth := depth+1) (proc := 11) (N := 7)
      (P := program) rfl (header (atDegree C (j+1))) (by rfl) ctx ν hw (by omega)
    have hFlag := degreeFlag_le_one C q f j
    unfold degreeRound
    light_call hh using header,atDegree,hdimCast
      with rh ξ ⟨hrh,hHeader,hHeaderOutside⟩
    have hpow' : ∀ i≤2*C.dim, ξ (C.powers+i)=((C.p^i : ℕ) : ℤ) := by
      intro i hi; rw [hHeaderOutside _ (Or.inl (by omega)),hpow i hi]
    have hf' : ∀ i<2*C.dim, ξ (C.target+i)=(f i : ℤ) := by
      intro i hi; rw [hHeaderOutside _ (Or.inl (by omega)),hf i hi]
    have hc := (LightExtensionFactorSearch.program_meets (atDegree C (j+1)) (depth := depth+1) ξ f hw (by omega)
      hq hp he hed hHeader hctx (by dsimp [atDegree]; omega) (by dsimp [atDegree]; omega)
      hleft hspace hpow' hf' (hword (j+1) he hed) hsearchWord).append tail
    have hc' := hc.mono_time (htime (j+1) he hed)
    light_call hc' using factorTime
      with out η ⟨hout,hKeep⟩
    have hKept : Kept μ η ctx := by
      intro x hx
      rw [hKeep x (by dsimp [atDegree]; omega),hHeaderOutside x (Or.inl hx),H x hx]
    have hfirstWord : ((factorFirst C q f (j+1) : ℕ) : ℤ)≤lim.word := by
      have hh := LightPairSearch.first_le (LightPairSearch.goodCode q (LightExtensionFactorSearch.good (atDegree C (j+1)) f)) (q*q)
      change factorFirst C q f (j+1) ≤ q*q at hh
      omega
    light_if hpos hnonpos : (0 : ℤ)<(factorFirst C q f (j+1) : ℤ) using hout,factorFirst
    · have hne : factorFirst C q f (j+1)≠0 := by omega
      have hNext : degreeFlag C q f (j+1)=0 := by
        unfold degreeFlag
        rw [if_neg (fun h => hne (h j (by omega)))]
      light_set 0
      refine ⟨by simp,rh,out,η,?_,hKept⟩
      simp [update_frame_setLocal,hNext]
    · have hz : factorFirst C q f (j+1)=0 := by omega
      have hNext : degreeFlag C q f (j+1)=degreeFlag C q f j := by
        unfold degreeFlag
        simp only [degreePrefix_succ,hz,and_true]
      refine Ends.skip ⟨by simp,rh,out,η,?_,hKept⟩
      simp [update_frame_setLocal,hNext]
  case done => intro σ _ H; exact H
  case bound =>
    rintro j _ hj _ ⟨rh,result,ν,rfl,H⟩
    have hdimCast : ((C.dim-1 : ℕ) : ℤ)=(C.dim : ℤ)-1 := by omega
    light_side [hdimCast]
  case after =>
    rintro _ ⟨rh,result,ν,rfl,H⟩
    have hf := degreeFlag_le_one C q f (C.dim-1)
    light_set (degreeFlag C q f (C.dim-1) : ℕ)
    exact ⟨by simp,H⟩


open TernaryExtensionEncoding

theorem degreeFlag_irreducible (C : Layout) [Fact C.p.Prime] {c : ℕ}
    (hd : 0<C.dim) (hc : c<C.p^C.dim) :
    degreeFlag C (C.p^C.dim) (codeDigits (p := C.p) (c+C.p^C.dim)) (C.dim-1)=1 ↔
      Irreducible (monicOfCode (p := C.p) C.dim c) := by
  have hp := (Fact.out : C.p.Prime).one_lt
  have hq : 0<C.p^C.dim := pow_pos (by omega) _
  have step (e : ℕ) (he : 0<e) (hed : e<C.dim) :
      factorFirst C (C.p^C.dim) (codeDigits (p := C.p) (c+C.p^C.dim)) e=0 ↔
        ∀ u<C.p^e, ∀ v<C.p^(C.dim-e),
          monicOfCode (p := C.p) e u*monicOfCode (C.dim-e) v≠monicOfCode C.dim c := by
    rw [factorFirst,LightExtensionFactorSearch.nohit_all _ _ _ hq (by simpa [atDegree] using Nat.le_of_lt hp)
      (by simpa [atDegree] using Nat.le_of_lt hed) (by simp [atDegree])]
    constructor
    · intro h u hu v hv hm
      apply h u v
      refine ⟨hu,hv,?_⟩
      exact (factor_check_iff hd hed hc hu hv).mpr hm
    · intro h u v hg
      exact h u hg.1 v hg.2.1 ((factor_check_iff hd hed hc hg.1 hg.2.1).mp hg.2.2)
  rw [irreducible_code_iff hd]
  constructor
  · intro h e he hed
    have hh : ∀t<C.dim-1, factorFirst C (C.p^C.dim) (codeDigits (p := C.p) (c+C.p^C.dim)) (t+1)=0 := by
      unfold degreeFlag at h
      split_ifs at h with hh
      · exact hh
    exact (step e he hed).mp (by simpa only [Nat.sub_add_cancel he] using hh (e-1) (by omega))
  · intro h
    unfold degreeFlag
    apply if_pos
    intro t ht
    exact (step (t+1) (by omega) (by omega)).mpr (h (t+1) (by omega) (by omega))

structure Budget (lim : Limits) (C : Layout) (q ctx T : ℕ) : Prop where
  qpos : 0<q
  primeBase : 1<C.p
  dimpos : 0<C.dim
  ctxLeft : ctx+7≤C.left
  powersTarget : C.powers+(2*C.dim+1)≤C.target
  targetCtx : C.target+2*C.dim≤ctx
  leftRight : C.left+2*C.dim≤C.right
  space : C.right+2*C.dim≤lim.space
  factorWord : ∀ e, 0<e → e<C.dim → (LightExtensionFactorPredicate.word (atDegree C e) q q : ℤ)≤lim.word
  searchWord : ((q*q+q+ctx+20 : ℕ) : ℤ)≤lim.word
  controls : ((C.p+C.dim+q+ctx+32 : ℕ) : ℤ)≤lim.word
  decodeWord : (LightCoefficientDecode.word (2*C.dim) C.p (2*q) 0 1 : ℤ)≤lim.word
  factorTime : ∀ e, 0<e → e<C.dim → LightIrreducibleFinder.factorTime C q e≤T

def candidateTime (C : Layout) (q T : ℕ) : ℕ :=
  LightCoefficientDecode.time (2*C.dim) (2*q)+degreeTime C.dim T+200

theorem candidate_meets (C : Layout) {c q ctx T depth : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+10<lim.depth)
    (B : Budget lim C q ctx T) (hc : c<q)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ)) :
    Meets lim program 12 depth [c,C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right] μ
      (candidateTime C q T)
      (fun r ν => r=(degreeFlag C q (LightCoefficientDecode.digit C.p (c+q)) (C.dim-1) : ℤ) ∧
        Kept μ ν C.target) := by
  have hdecodeword : (LightCoefficientDecode.word (2*C.dim) C.p (c+q) 0 1 : ℤ)≤lim.word := by
    apply le_trans _ B.decodeWord
    exact_mod_cast (show LightCoefficientDecode.word (2*C.dim) C.p (c+q) 0 1≤
        LightCoefficientDecode.word (2*C.dim) C.p (2*q) 0 1 by unfold LightCoefficientDecode.word; omega)
  have hh := LightCoefficientDecode.meets (d := depth+1) (P := program) (pMain := 2) (pDigit := 3) (pDivide := 4)
    (W := 2*C.dim) (p := C.p) (k := c+q) (powers := C.powers) (start := 0) (stride := 1)
    (dst := C.target) (n := 2*C.dim) rfl rfl rfl hw (by omega) (by have := B.primeBase; omega)
    (by have := B.targetCtx; have := B.ctxLeft; have := B.leftRight; have := B.space; omega)
    (by have := B.powersTarget; have := B.targetCtx; have := B.ctxLeft; have := B.leftRight; have := B.space; omega)
    (Or.inl B.powersTarget) hdecodeword (by intro i hi; omega) hpowRead
  have hht := hh.mono_time (show LightCoefficientDecode.time (2*C.dim) (c+q)≤
      LightCoefficientDecode.time (2*C.dim) (2*q) by unfold LightCoefficientDecode.time LightRadixDigit.time; gcongr <;> omega)
  have hcontrols := B.controls
  have hdecodeBig := B.decodeWord
  unfold LightCoefficientDecode.word at hdecodeBig
  have hs := B.space
  have hl := B.leftRight
  have hct := B.ctxLeft
  have htc := B.targetCtx
  have hpt := B.powersTarget
  apply Meets.of_body (by rfl : program[12]?=some candidateBody)
  unfold candidateBody candidateTime
  light_call hht with r ν ⟨hread,hOutside⟩
  have hpows : ∀ i≤2*C.dim, ν (C.powers+i)=((C.p^i : ℕ) : ℤ) := by
    intro i hi
    rw [hOutside _ (Or.inl (by have := B.powersTarget; omega)),hpowRead i hi]
  have hdeg := degree_meets C (depth := depth+1) ν (LightCoefficientDecode.digit C.p (c+q)) hw
    (by omega) B.qpos B.primeBase B.dimpos B.ctxLeft (by have := B.powersTarget; have := B.targetCtx; omega)
    B.targetCtx B.leftRight B.space hpows (by simpa using hread) B.factorWord B.searchWord B.controls B.factorTime
  light_call hdeg with out η ⟨hout,hKept⟩
  exact ⟨by simpa using hout,fun x hx => (hKept x (by have := B.targetCtx; omega)).trans (hOutside x (Or.inl hx))⟩


def accepted (C : Layout) (q c : ℕ) : Prop :=
  degreeFlag C q (LightCoefficientDecode.digit C.p (c+q)) (C.dim-1)=1

def chosen (C : Layout) (q n : ℕ) : ℕ := LightTernaryRowSelector.pick (accepted C q) n

def searchTime (C : Layout) (q T : ℕ) : ℕ := q*(candidateTime C q T+200)+100

def SearchInv (μ : ℕ → ℤ) (C : Layout) (q ctx : ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right,0,chosen C q j,j,result],ν⟩ ∧
      Kept μ ν C.target

theorem search_meets (C : Layout) {q ctx T depth : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+11<lim.depth)
    (B : Budget lim C q ctx T)
    (hpowRead : ∀ i≤2*C.dim, μ (C.powers+i)=((C.p^i : ℕ) : ℤ)) :
    Meets lim program 13 depth [C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right] μ
      (searchTime C q T)
      (fun r ν => r=(chosen C q q : ℤ) ∧ Kept μ ν C.target) := by
  have hcontrols := B.controls
  have hs := B.space
  have hl := B.leftRight
  have hct := B.ctxLeft
  have htc := B.targetCtx
  have hpt := B.powersTarget
  apply Meets.of_body (by rfl : program[13]?=some searchBody)
  unfold searchBody searchTime
  light_set 0
  refine Ends.pieceThen (Ends.for (T := q*(candidateTime C q T+200)+30)
    (Q := SearchInv μ C q ctx q) (SearchInv μ C q ctx) q (candidateTime C q T+150)
    ?start ?round ?done ?bound (hT := by light_time)) ?after (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,SameOn.refl⟩
    simp [update_frame_setLocal,chosen,LightTernaryRowSelector.pick]
    change frame [(C.p : ℤ),C.dim,q,C.powers,C.target,ctx,C.left,C.right,0,0,0]=
      frame ([(C.p : ℤ),C.dim,q,C.powers,C.target,ctx,C.left,C.right,0,0,0]++[0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨result,ν,rfl,H⟩
    have hpows : ∀i≤2*C.dim, ν (C.powers+i)=((C.p^i : ℕ) : ℤ) := by
      intro i hi; rw [H _ (by omega),hpowRead i hi]
    have hcall := candidate_meets C (depth := depth+1) ν hw (by omega) B hj hpows
    have hchosen : chosen C q j≤j := LightTernaryRowSelector.pick_le _ _
    unfold searchRound
    light_call hcall with out η ⟨hout,hKeep⟩
    have hKept : Kept μ η C.target := fun x hx => (hKeep x hx).trans (H x hx)
    have hFlag := degreeFlag_le_one C q (LightCoefficientDecode.digit C.p (j+q)) (C.dim-1)
    light_if hyes hno : (degreeFlag C q (LightCoefficientDecode.digit C.p (j+q)) (C.dim-1) : ℤ)=1 using hout
    · have ha : accepted C q j := by unfold accepted; omega
      have hNext : chosen C q (j+1)=j+1 := by simp [chosen,LightTernaryRowSelector.pick,ha]
      light_set (j+1 : ℕ)
      refine ⟨by simp,out,η,?_,hKept⟩
      simp [update_frame_setLocal,hNext]
    · have ha : ¬accepted C q j := by unfold accepted; omega
      have hNext : chosen C q (j+1)=chosen C q j := by simp [chosen,LightTernaryRowSelector.pick,ha]
      exact Ends.skip ⟨by simp,out,η,by simp [update_frame_setLocal,hNext],hKept⟩
  case done => intro σ _ H; exact H
  case bound => rintro j _ hj _ ⟨r,ν,rfl,H⟩; light_side
  case after =>
    rintro _ ⟨r,ν,rfl,H⟩
    have hh : chosen C q q≤q := LightTernaryRowSelector.pick_le _ _
    light_set (chosen C q q : ℕ)
    exact ⟨by simp,H⟩


theorem chosen_irreducible (C : Layout) [Fact C.p.Prime] (hd : 0<C.dim) :
    0<chosen C (C.p^C.dim) (C.p^C.dim) ∧
    chosen C (C.p^C.dim) (C.p^C.dim)≤C.p^C.dim ∧
    Irreducible (monicOfCode (p := C.p) C.dim (chosen C (C.p^C.dim) (C.p^C.dim)-1)) := by
  have equiv (c : ℕ) (hc : c<C.p^C.dim) :
      accepted C (C.p^C.dim) c ↔ Irreducible (monicOfCode (p := C.p) C.dim c) := by
    exact degreeFlag_irreducible C hd hc
  obtain ⟨c,hc,hi⟩ := exists_irreducible_code (p := C.p) C.dim hd
  have hpos : 0<chosen C (C.p^C.dim) (C.p^C.dim) :=
    (LightTernaryRowSelector.pick_pos_iff _ _).mpr ⟨c,hc,(equiv c hc).mpr hi⟩
  have hle : chosen C (C.p^C.dim) (C.p^C.dim)≤C.p^C.dim := LightTernaryRowSelector.pick_le _ _
  exact ⟨hpos,hle,(equiv _ (by omega)).mp (LightTernaryRowSelector.pick_good _ _ hpos)⟩

def setupTime (C : Layout) (q T : ℕ) : ℕ :=
  powTableTime (2*C.dim+1)+searchTime C q T+LightCoefficientDecode.time (2*C.dim) (2*q)+300

theorem setup_meets (C : Layout) [Fact C.p.Prime] {q ctx T depth : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : depth+12<lim.depth)
    (B : Budget lim C q ctx T) (hq : q=C.p^C.dim) :
    Meets lim program 15 depth [C.p,C.dim,q,C.powers,C.target,ctx,C.left,C.right] μ
      (setupTime C q T)
      (fun r ν => ∃ c<q, r=(c+1 : ℕ) ∧ Irreducible (monicOfCode (p := C.p) C.dim c) ∧
        (∀ i<2*C.dim, ν (C.target+i)=(codeDigits (p := C.p) (c+q) i : ℤ)) ∧
        (∀ i≤2*C.dim, ν (C.powers+i)=((C.p^i : ℕ) : ℤ)) ∧ Kept μ ν C.powers) := by
  have hcontrols := B.controls
  have hs := B.space
  have hl := B.leftRight
  have hct := B.ctxLeft
  have htc := B.targetCtx
  have hpt := B.powersTarget
  have hdb := B.decodeWord
  unfold LightCoefficientDecode.word at hdb
  have hp := B.primeBase
  have hchosen := chosen_irreducible C B.dimpos
  rw [←hq] at hchosen
  rcases hchosen with ⟨hpos,hle,hirred⟩
  let c := chosen C q q-1
  have hc : c<q := by dsimp [c]; omega
  have hcOne : chosen C q q=c+1 := by dsimp [c]; omega
  have hpow := powTable_meets (P := program) (d := depth+1) (p := 14) (dst := C.powers)
    (L := 2*C.dim+1) (b := C.p) (μ := μ) rfl hw (by omega) (by
      intro j hj
      have hh := Nat.pow_le_pow_right (Nat.le_of_lt hp) hj
      exact (Int.ofNat_le.mpr hh).trans (by omega))
  apply Meets.of_body (by rfl : program[15]?=some setupBody)
  unfold setupBody setupTime
  light_call hpow with r ν ⟨hPowers,hOutside⟩
  have hpows : ∀i≤2*C.dim, ν (C.powers+i)=((C.p^i : ℕ) : ℤ) := by
    intro i hi
    exact (hPowers i (by simp; omega)).trans (getElem_powList (by simp; omega))
  have hscan := search_meets C (depth := depth+1) ν hw (by omega) B hpows
  light_call hscan with picked η ⟨hPicked,hKeep⟩
  have hpows' : ∀i≤2*C.dim, η (C.powers+i)=((C.p^i : ℕ) : ℤ) := by
    intro i hi; rw [hKeep _ (by omega),hpows i hi]
  have hdecWord : (LightCoefficientDecode.word (2*C.dim) C.p (c+q) 0 1 : ℤ)≤lim.word := by
    apply le_trans _ B.decodeWord
    exact_mod_cast (show LightCoefficientDecode.word (2*C.dim) C.p (c+q) 0 1≤
        LightCoefficientDecode.word (2*C.dim) C.p (2*q) 0 1 by unfold LightCoefficientDecode.word; omega)
  have hdec := LightCoefficientDecode.meets (d := depth+1) (P := program) (pMain := 2) (pDigit := 3) (pDivide := 4)
    (W := 2*C.dim) (p := C.p) (k := c+q) (powers := C.powers) (start := 0) (stride := 1)
    (dst := C.target) (n := 2*C.dim) rfl rfl rfl hw (by omega) (by omega)
    (by omega) (by omega) (Or.inl B.powersTarget) hdecWord (by intro i hi; omega) hpows'
  have hdect := hdec.mono_time (show LightCoefficientDecode.time (2*C.dim) (c+q)≤
      LightCoefficientDecode.time (2*C.dim) (2*q) by unfold LightCoefficientDecode.time LightRadixDigit.time; gcongr <;> omega)
  have hPicked' : picked=(c+1 : ℕ) := by simpa only [hcOne] using hPicked
  light_call hdect using hPicked',Nat.cast_add,Nat.cast_one with out ξ ⟨hTarget,hOut⟩
  light_set (c+1 : ℕ) using hPicked'
  refine ⟨c,hc,by simp,hirred,?_,?_,?_⟩
  · simpa only [LightCoefficientDecode.digit,codeDigits,zero_add,one_mul] using hTarget
  · intro i hi
    change ξ (C.powers+i)=((C.p^i : ℕ) : ℤ)
    rw [hOut _ (Or.inl (by omega)),hpows' i hi]
  · intro x hx
    change ξ x=μ x
    rw [hOut _ (Or.inl (by omega)),hKeep x (by omega),hOutside x (Or.inl hx)]

end ThreeSum.LightIrreducibleFinder
