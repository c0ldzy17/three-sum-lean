import Submission.ThreeSum.LightTernaryControllerFactory

noncomputable section
namespace ThreeSum.LightTernaryControllerFactory
open Light LightTernarySeedScoreFactory

/-- Pure certificates consumed by the actual controller. No execution
receipt is stored in this structure. -/
structure Plan (C : Config) [Fact C.p.Prime] (D : Family C) (lim : Limits)
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
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).Guard lim (depth+1) K R S raws words maps ν
  replayState : ∀ν ξ, invariant n ν→(D.candidate (D.pick K n dB dC dP tB tC tP-1)).Done K ν ξ→ replay ξ
  spanGuard : ∀ν, replay ν→SpanGuard (withSeed C (D.pick K n dB dC dP tB tC tP-1))
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data lim (depth+1) newSpan ν
  finish : ∀ν ξ, replay ν→SpanDone (withSeed C (D.pick K n dB dC dP tB tC tP-1))
    (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data newSpan ν ξ→ finalState ξ

def Plan.run {C : Config} [Fact C.p.Prime] {D : Family C} {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (H : Plan C D lim depth K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps μ) :=
  ThreeSum.LightTernaryControllerFactory.run D raws words maps μ H.invariant H.replay H.finalState H.spaceWord H.flags H.Bscores H.Cscores H.Pscores
    H.selectorWord H.length H.row H.depthBound H.initial H.candidate H.runtime H.nextState H.reads H.existsRow
    H.replayGuard H.replayState H.spanGuard H.finish

end ThreeSum.LightTernaryControllerFactory
