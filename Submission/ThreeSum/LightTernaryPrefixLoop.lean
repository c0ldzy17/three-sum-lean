import Submission.ThreeSum.LightTernarySeedController
import Submission.ThreeSum.LightTernaryPrefixSetup
import Submission.ThreeSum.LightTernaryInitialKeys
import Submission.ThreeSum.LightTernaryCommitKeys
import Submission.ThreeSum.LightTernaryCommitSpan
import Submission.ThreeSum.LightTernaryRepeatWord
import Submission.ThreeSum.LightTernaryBudgetStep

/-! Concrete outer prefix program. The 106-word and 48-word templates are
constructed by the arena initializer. This module updates every
prefix-dependent scalar by executing arithmetic and verified kernels. -/
noncomputable section
namespace ThreeSum.LightTernaryPrefixLoop
open Light
set_option maxHeartbeats 7000000
set_option maxRecDepth 24000

def headerWrites : List (ℕ×ℕ) := [
  (6,3),(12,19),(14,17),(15,16),(16,18),(17,14),(21,21),(22,15),
  (29,3),(35,19),(37,17),(38,16),(39,18),(40,14),(44,21),(45,15),
  (46,12),(47,17),(48,16),(50,14),(52,15),
  (58,12),(62,17),(63,16),(64,28),(65,14),(66,13),(71,22),(72,14),
  (75,12),(79,17),(80,16),(81,29),(82,14),(83,13),(88,22),(89,14),
  (93,27),(95,26),(102,23),(103,24)]

def stores : List (ℕ×ℕ)→ Stmt
  | []=>.skip
  | (field,reg)::xs=>.store (v 1 +' k field) (v reg) ;; stores xs

/-- [template106,live106,prefixHeader8,s,m,p,powerOld,alpha2,alphaRank,
localQcode,wordRadix,J]. All pointer fields are from the actual arena. -/
def headerBody : Stmt :=
  .call 177 [v 0,v 1,k 106] 30 ;;
  .set 12 (M (v 2)) ;;
  .set 13 (M (v 2 +' k 1)) ;;
  .set 14 (M (v 2 +' k 2)) ;;
  .set 15 (M (v 2 +' k 3)) ;;
  .set 16 (M (v 2 +' k 4)) ;;
  .set 17 (M (v 2 +' k 5)) ;;
  .set 18 (M (v 2 +' k 6)) ;;
  .set 19 (v 6 *' v 5) ;;
  .set 20 (v 7 *' v 3) ;;
  .call 168 [k 2,v 20] 21 ;;
  .set 22 (v 8 *' v 3) ;;
  .set 23 ((v 12 +' k 1) *' v 16) ;;
  .set 24 (v 12 *' v 16) ;;
  .set 25 (k 2 *' v 22) ;;
  .set 26 (v 25 -' v 13 -' k 1) ;;
  .call 178 [v 9,v 10,v 3] 27 ;;
  .set 28 (M (v 0 +' k 99) +' v 24) ;;
  .set 29 (M (v 0 +' k 100) +' v 24) ;;
  stores headerWrites ;;
  .store (v 1 +' k 104) (k 0) ;;
  .set 0 (v 19)

def seedArgs : List Expr := (List.range 48).map (fun i=>M (v 3 +' k i))

/-- [m,F,p,liveSeed48,template106,live106,prefixFree,alpha2,alphaRank,
localQcode,wordRadix,J,a,b,scaleBase,j,powerOld]. The bank is built for s=j+1. -/
def prepareBody : Stmt :=
  .set 17 (v 15 +' k 1) ;;
  .call 172 [v 17,v 0,v 1,v 6] 18 ;;
  .call 179 [v 4,v 5,v 18,v 17,v 0,v 2,v 16,v 7,v 8,v 9,v 10,v 11] 19 ;;
  .store (v 3 +' k 4) (v 16) ;;
  .store (v 3 +' k 6) (v 16) ;;
  .store (v 3 +' k 24) (v 5) ;;
  .store (v 3 +' k 39) (v 17) ;;
  .call 183 [v 3 +' k 41,v 2,v 12,v 13,v 14] 26 ;;
  .set 0 (v 19)

def stepBody : Stmt :=
  .call 184 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 19 ;;
  .call 166 seedArgs 26 ;;
  .call 176 [M (v 3 +' k 9),M (v 3 +' k 8),M (v 3 +' k 10),
    M (v 3 +' k 13),M (v 3 +' k 12),M (v 3 +' k 14),
    M (v 3 +' k 17),M (v 3 +' k 16),M (v 3 +' k 18)] 26 ;;
  .call 177 [M (v 3 +' k 47),M (v 3 +' k 3),v 19 *' v 11] 26 ;;
  .set 0 (v 19)

/-- [rounds,m,F,p,liveSeed48,template106,live106,prefixFree,alpha2,
alphaRank,localQcode,wordRadix,J,a,b,scaleBase]. -/
def roundArgs : List Expr :=
  [v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 17,v 16]
def loopBody : Stmt :=
  .set 16 (k 1) ;;
  .for 17 (v 0) (.call 180 roundArgs 18 ;; .set 16 (v 18)) ;;
  .set 0 (v 16)

/-- The same sixteen loop arguments followed by the actual seed template pointer.
The old keys and empty digit span are initialized by real zero fills. -/
def initBody : Stmt :=
  .call 177 [v 16,v 4,k 48] 17 ;;
  .call 174 [M (v 4 +' k 8),M (v 4 +' k 10),M (v 4 +' k 12),
    M (v 4 +' k 14),M (v 4 +' k 16),M (v 4 +' k 18)] 17 ;;
  .call 0 [M (v 4 +' k 3),v 12,k 0] 17 ;;
  .call 181 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15] 0

def priorProcs (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  LightTernarySeedController.program p R S K raws words maps xl yl zl xr yr zr++
    LightTernaryPrefixSetup.allocatedProgram.map (ReportingHostRelocation.relocate 167)++
    LightTernaryInitialKeys.program.map (ReportingHostRelocation.relocate 173)++
    LightTernaryCommitKeys.program.map (ReportingHostRelocation.relocate 175)++
    LightTernaryCommitSpan.program.map (ReportingHostRelocation.relocate 177)

def program (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) : Program :=
  priorProcs p R S K raws words maps xl yl zl xr yr zr++
    [LightTernaryRepeatWord.body,headerBody,stepBody,loopBody,initBody,LightTernaryBudgetStep.body,prepareBody]

@[simp] theorem prefix_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (priorProcs p R S K raws words maps xl yl zl xr yr zr).length=178 := by
  simp [priorProcs,LightTernaryPrefixSetup.allocatedProgram,LightTernaryPrefixSetup.program,
    LightTernaryInitialKeys.program,LightTernaryCommitKeys.program,LightTernaryCommitSpan.program]

@[simp] theorem program_length (p R S K : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (xl yl zl xr yr zr : List ℤ) :
    (program p R S K raws words maps xl yl zl xr yr zr).length=185 := by simp [program]

def args (rounds m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase : ℕ) : List ℤ :=
  [rounds,m,F,p,liveSeed,template,liveHeader,prefixFree,alpha2,alphaRank,localQ,radix,J,a,b,scaleBase]

def stepArgs (m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase j power : ℕ) : List ℤ :=
  [m,F,p,liveSeed,template,liveHeader,prefixFree,alpha2,alphaRank,localQ,radix,J,a,b,scaleBase,j,power]

def time (r stepTime : ℕ) : ℕ := r*(stepTime+200)+100

def Inv (argv : List ℤ) (p : ℕ) (I : ℕ→ (ℕ→ ℤ)→ Prop) (j : ℕ) (σ : State) : Prop :=
  ∃ ret ν, σ=⟨frame (argv++[((p^j:ℕ):ℤ),(j:ℤ),ret]),ν⟩ ∧ I j ν

/-- Phase interface for the actual fixed outer loop. The concrete step is
entry180 above, not an externally supplied procedure. Its execution receipt
is discharged by the source/score/span factories in the whole controller. -/
theorem loop_meets {lim : Limits} {P : Program}
    {pMain rounds m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase d T : ℕ}
    (hmain : P[pMain]?=some loopBody) (μ : ℕ→ ℤ) (I : ℕ→ (ℕ→ ℤ)→ Prop)
    (hstart : I 0 μ) (hr : (rounds:ℤ)≤ lim.word) (hd : d<lim.depth)
    (hpower : ∀ j≤ rounds, ((p^j:ℕ):ℤ)≤ lim.word)
    (hstep : ∀ j<rounds, ∀ ν, I j ν→
      Meets lim P 180 (d+1)
        (stepArgs m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase j (p^j))
        ν T (fun z ξ=>z=((p^(j+1):ℕ):ℤ) ∧ I (j+1) ξ)) :
    Meets lim P pMain d
      (args rounds m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase)
      μ (time rounds T) (fun z ν=>z=((p^rounds:ℕ):ℤ) ∧ I rounds ν) := by
  let argv:= args rounds m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scaleBase
  have h1 : (1:ℤ)≤ lim.word := by simpa using hpower 0 (Nat.zero_le _)
  apply Meets.of_body hmain
  change Ends _ _ _ _ ⟨frame argv,μ⟩ _ _
  unfold loopBody time
  light_set (1:ℕ)
  refine Ends.pieceThen (Ends.for (T:= rounds*(T+150)+30)
    (Q:= Inv argv p I rounds) (Inv argv p I) rounds (T+100)
    ?start ?round ?done ?bound) ?after (hT:= by light_time)
  case start =>
    refine ⟨0,μ,?_,hstart⟩
    simp only [Inv,argv,args,pow_zero,update_frame_setLocal,setLocal]
    congr 1
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j σ hj hc ⟨ret,ν,rfl,hI⟩
    have hh:= hstep j hj ν hI
    have hcost : (roundArgs.map Expr.cost).sum=17 := by decide
    light_call hh using argv,args,stepArgs,roundArgs with z ξ ⟨hz,hnext⟩
    have hfit:= hpower (j+1) (by omega)
    light_set (p^(j+1):ℕ) using argv,args,hz
    refine ⟨by simp [argv,args],z,ξ,?_,hnext⟩
    simp [argv,args,update_frame_setLocal]
  case done =>intro σ _ hI; exact hI
  case bound =>rintro j σ hj hc ⟨ret,ν,rfl,hI⟩; light_side [argv,args]
  case after =>
    rintro σ ⟨ret,ν,rfl,hI⟩
    have hf:= hpower rounds le_rfl
    light_set (p^rounds:ℕ) using argv,args
    exact ⟨rfl,hI⟩

end ThreeSum.LightTernaryPrefixLoop
