import Submission.ThreeSum.LightTernaryControllerFull

noncomputable section
namespace ThreeSum.LightTernaryControllerFactory
open Light LightTernarySeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

/-- A pure state invariant, concrete candidate guards, and the actual span
layout derive all operational premises of the finite menu controller. -/
theorem run_full {C : Config} [Fact C.p.Prime] (D : Family C) {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ)
    (I : ℕ→(ℕ→ℤ)→Prop) (Replay Final : (ℕ→ℤ)→Prop)
    (hw : (lim.space:ℤ)≤lim.word)
    (hFlags : C.flags+n≤lim.space) (hBs : C.scoreB+n≤lim.space)
    (hCs : C.scoreC+n≤lim.space) (hPs : C.scorePaired+n≤lim.space)
    (hWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP:ℤ)≤lim.word)
    (hLen : C.J+2≤lim.space)
    (hRow : C.menu+(D.pick K n dB dC dP tB tC tP-1)*(C.J+2)≤lim.space)
    (hd : depth<lim.depth) (hstart : I 0 μ)
    (hguard : ∀i<n, ∀ν, I i ν→(D.candidate i).Guard lim (depth+1) K R S raws words maps ν)
    (htime : ∀i<n, (D.candidate i).runtime K R S raws words maps≤seedTime)
    (hnext : ∀i<n, ∀ν ξ, I i ν→(D.candidate i).Done K ν ξ→I (i+1) ξ)
    (hread : ∀ν, I n ν→
      (∀i<n, ν (C.flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
      (∀i<n, ν (C.scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
      (∀i<n, ν (C.scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
      (∀i<n, ν (C.scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U))
    (hexist : ∃i<n, LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
      dB dC dP tB tC tP i)
    (hreplayGuard : ∀ν, I n ν→
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).FullGuard lim (depth+1) K R S raws words maps ν)
    (hreplay : ∀ν ξ, I n ν→(D.candidate (D.pick K n dB dC dP tB tC tP-1)).FullDone K R S raws words maps ν ξ→Replay ξ)
    (hspan : ∀ν, Replay ν→SpanGuard (withSeed C (D.pick K n dB dC dP tB tC tP-1))
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data lim (depth+1) newSpan ν)
    (hfinal : ∀ν ξ, Replay ν→SpanDone (withSeed C (D.pick K n dB dC dP tB tC tP-1))
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data newSpan ν ξ→Final ξ) :
    Meets lim (LightTernarySeedController.program C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr)
      166 depth (LightTernarySeedController.args (withSeed C 0).argv n dB dC dP tB tC tP newSpan)
      μ (LightTernarySeedController.time n seedTime (LightSpanCatalogStep.time C.J C.p C.catalogRows))
      (fun r ν=>r=(D.pick K n dB dC dP tB tC tP:ℤ) ∧ Final ν) :=by
  have hpos : 0<D.pick K n dB dC dP tB tC tP :=
    (LightTernaryRowSelector.pick_pos_iff _ _).mpr hexist
  have hle : D.pick K n dB dC dP tB tC tP≤n :=LightTernaryRowSelector.pick_le _ _
  have hi : D.pick K n dB dC dP tB tC tP-1<n :=by omega
  apply LightTernarySeedController.program_meets raws words maps D.xl D.yl D.zl D.xr D.yr D.zr
    μ D.flag D.scoreB D.scoreC (D.scoreP K) I Replay Final hw hFlags hBs hCs hPs hWord hLen hRow hd hstart
  · intro i hi ν hI
    have hh:=Candidate.run (hguard i hi ν hI)
    rw [D.leftX i,D.leftY i,D.leftZ i,D.rightX i,D.rightY i,D.rightZ i] at hh
    apply hh.mono (htime i hi)
    intro r ξ hξ
    exact hnext i hi ν ξ hI hξ.2
  · exact hread
  · exact hexist
  · intro ν hI
    have hh:=Candidate.run_full (hreplayGuard ν hI)
    rw [D.leftX _,D.leftY _,D.leftZ _,D.rightX _,D.rightY _,D.rightZ _] at hh
    apply hh.mono (htime _ hi)
    intro r ξ hξ
    exact hreplay ν ξ hI hξ.2
  · intro ν hν
    have hcast : ((D.pick K n dB dC dP tB tC tP-1:ℕ):ℤ)=
        (D.pick K n dB dC dP tB tC tP:ℤ)-1 :=by omega
    dsimp only [Family.pick] at hcast
    simpa only [withSeed,Config.row,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hcast,Family.pick] using
      (hspan ν hν).run.mono le_rfl (fun _ ξ hξ=>hfinal ν ξ hν hξ)


/-- Pure certificates consumed by the actual controller. No execution
receipt is stored in this structure. -/
structure FullPlan (C : Config) [Fact C.p.Prime] (D : Family C) (lim : Limits)
    (depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ) where
  invariant : ℕ→(ℕ→ℤ)→Prop
  replay : (ℕ→ℤ)→Prop
  finalState : (ℕ→ℤ)→Prop
  spaceWord : (lim.space:ℤ)≤lim.word
  flags : C.flags+n≤lim.space
  Bscores : C.scoreB+n≤lim.space
  Cscores : C.scoreC+n≤lim.space
  Pscores : C.scorePaired+n≤lim.space
  selectorWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP:ℤ)≤lim.word
  length : C.J+2≤lim.space
  row : C.menu+(D.pick K n dB dC dP tB tC tP-1)*(C.J+2)≤lim.space
  depthBound : depth<lim.depth
  initial : invariant 0 μ
  candidate : ∀i<n, ∀ν, invariant i ν→(D.candidate i).Guard lim (depth+1) K R S raws words maps ν
  runtime : ∀i<n, (D.candidate i).runtime K R S raws words maps≤seedTime
  nextState : ∀i<n, ∀ν ξ, invariant i ν→(D.candidate i).Done K ν ξ→invariant (i+1) ξ
  reads : ∀ν, invariant n ν→
    (∀i<n, ν (C.flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
    (∀i<n, ν (C.scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
    (∀i<n, ν (C.scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
    (∀i<n, ν (C.scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U)
  existsRow : ∃i<n, LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
    dB dC dP tB tC tP i
  replayGuard : ∀ν, invariant n ν→
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).FullGuard lim (depth+1) K R S raws words maps ν
  replayState : ∀ν ξ, invariant n ν→(D.candidate (D.pick K n dB dC dP tB tC tP-1)).FullDone K R S raws words maps ν ξ→ replay ξ
  spanGuard : ∀ν, replay ν→SpanGuard (withSeed C (D.pick K n dB dC dP tB tC tP-1))
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data lim (depth+1) newSpan ν
  finish : ∀ν ξ, replay ν→SpanDone (withSeed C (D.pick K n dB dC dP tB tC tP-1))
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data newSpan ν ξ→ finalState ξ

def FullPlan.run {C : Config} [Fact C.p.Prime] {D : Family C} {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (H : FullPlan C D lim depth K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps μ) :=
  ThreeSum.LightTernaryControllerFactory.run_full D raws words maps μ H.invariant H.replay H.finalState H.spaceWord H.flags H.Bscores H.Cscores H.Pscores
    H.selectorWord H.length H.row H.depthBound H.initial H.candidate H.runtime H.nextState H.reads H.existsRow
    H.replayGuard H.replayState H.spanGuard H.finish


end ThreeSum.LightTernaryControllerFactory
