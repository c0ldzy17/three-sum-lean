import Submission.ThreeSum.LightTernaryPrefixStep

noncomputable section
namespace ThreeSum.LightTernaryPrefixPhases
open Light LightTernarySeedScoreFactory LightTernaryControllerFactory LightTernaryPrefixLoop
open LightTernaryPrefixStep
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

/-- A phase certificate contains finite data, physical read certificates,
scalar bounds and the already constructed actual controller plans. -/
structure Phase (X : Inputs) (lim : Limits) (depth K R S p : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) (μ : ℕ→ℤ) where
  C : Config
  [prime : Fact C.p.Prime]
  family : Family C
  n : ℕ
  U : ℕ
  dB : ℕ
  dC : ℕ
  dP : ℕ
  tB : ℕ
  tC : ℕ
  tP : ℕ
  newSpan : ℕ
  seedTime : ℕ
  programPrime : C.p=p
  leftX : family.xl=xl
  leftY : family.yl=yl
  leftZ : family.zl=zl
  rightX : family.xr=xr
  rightY : family.yr=yr
  rightZ : family.zr=zr
  prepare : PrepareReady X lim (depth+1) μ
  inputPrime : X.p=C.p
  inputJ : X.J=C.J
  plans : ∀ν, Prepared X μ ν→FullPlan C family lim (depth+1) K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps ν
  layout : LightTernaryPrefixFinish.Layout C lim X.seed (X.power*X.p) newSpan
  headerRead : ∀ν, Prepared X μ ν→Seg ν X.seed (LightTernaryPrefixFinish.header C n dB dC dP tB tC tP newSpan)
  finalHeader : ∀ν, ∀h : Prepared X μ ν, ∀ξ, (plans ν h).finalState ξ→
    Seg ξ X.seed (LightTernaryPrefixFinish.header C n dB dC dP tB tC tP newSpan)

attribute [instance] Phase.prime

def Phase.Output {X : Inputs} {lim : Limits} {depth K R S p : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : Phase X lim depth K R S p raws words maps xl yl zl xr yr zr μ) (ω : ℕ→ℤ) : Prop :=
  ∃ν, ∃h : Prepared X μ ν, ∃ξ, (H.plans ν h).finalState ξ ∧
    LightTernaryPrefixFinish.Committed H.C (X.power*X.p) H.newSpan ξ ω ∧
    Seg ω X.seed (LightTernaryPrefixFinish.header H.C H.n H.dB H.dC H.dP H.tB H.tC H.tP H.newSpan)

def Phase.time {X : Inputs} {lim : Limits} {depth K R S p : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : Phase X lim depth K R S p raws words maps xl yl zl xr yr zr μ) : ℕ :=
  LightTernaryPrefixStep.time X H.C H.n H.seedTime

theorem Phase.run {X : Inputs} {lim : Limits} {depth K R S p : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : Phase X lim depth K R S p raws words maps xl yl zl xr yr zr μ) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 180 depth X.argv μ H.time
      (fun z ω=>z=((X.power*X.p:ℕ):ℤ) ∧ H.Output ω) :=by
  letI : Fact H.C.p.Prime:=H.prime
  have hh:=LightTernaryPrefixStep.meets μ H.prepare H.inputPrime H.inputJ H.plans H.layout H.headerRead H.finalHeader
  have hprogram : program H.C.p R S K raws words maps H.family.xl H.family.yl H.family.zl H.family.xr H.family.yr H.family.zr=program p R S K raws words maps xl yl zl xr yr zr :=by
    rw [H.programPrime,H.leftX,H.leftY,H.leftZ,H.rightX,H.rightY,H.rightZ]
  rw [hprogram] at hh
  exact hh

/-- The actual fixed loop is derived from pure certificates for each phase.
There is no arbitrary execution callback in this interface. -/
theorem loop_meets {lim : Limits} {rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
    depth K R S T : ℕ} {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ}
    (μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop) (hstart : I 0 μ)
    (hrounds : (rounds:ℤ)≤lim.word) (hd : depth<lim.depth)
    (hpowers : ∀j≤rounds, ((p^j:ℕ):ℤ)≤lim.word)
    (X : ℕ→Inputs)
    (hargs : ∀j<rounds, (X j).argv=stepArgs m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale j (p^j))
    (hpower : ∀j<rounds, (X j).power*(X j).p=p^(j+1))
    (stages : ∀j<rounds, ∀ν,I j ν→Phase (X j) lim (depth+1) K R S p raws words maps xl yl zl xr yr zr ν)
    (hcost : ∀(j : ℕ)(hj : j<rounds), ∀ν,∀h:I j ν,(stages j hj ν h).time≤T)
    (hnext : ∀(j : ℕ)(hj : j<rounds), ∀ν,∀h:I j ν,∀ω,(stages j hj ν h).Output ω→I (j+1) ω) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 181 depth
      (args rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale)
      μ (LightTernaryPrefixLoop.time rounds T) (fun z ν=>z=((p^rounds:ℕ):ℤ) ∧ I rounds ν) :=by
  apply LightTernaryPrefixLoop.loop_meets
    (program_library p R S K raws words maps xl yl zl xr yr zr).loop μ I hstart hrounds hd hpowers
  intro j hj ν hI
  have hh:=(stages j hj ν hI).run
  rw [hargs j hj] at hh
  apply hh.mono (hcost j hj ν hI)
  intro z ω hω
  exact ⟨by simpa only [hpower j hj] using hω.1,hnext j hj ν hI ω hω.2⟩

/-- A pure certificate for the entire actual prefix loop. -/
structure LoopPlan (lim : Limits) (rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
    depth K R S T : ℕ) (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ) (μ : ℕ→ℤ) where
  invariant : ℕ→(ℕ→ℤ)→Prop
  initial : invariant 0 μ
  roundsWord : (rounds:ℤ)≤lim.word
  depthBound : depth<lim.depth
  powerWords : ∀j≤rounds, ((p^j:ℕ):ℤ)≤lim.word
  inputs : ℕ→Inputs
  arguments : ∀j<rounds, (inputs j).argv=stepArgs m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale j (p^j)
  powers : ∀j<rounds, (inputs j).power*(inputs j).p=p^(j+1)
  stages : ∀j<rounds, ∀ν,invariant j ν→Phase (inputs j) lim (depth+1) K R S p raws words maps xl yl zl xr yr zr ν
  costs : ∀(j : ℕ)(hj : j<rounds),∀ν,∀h:invariant j ν,(stages j hj ν h).time≤T
  transition : ∀(j : ℕ)(hj : j<rounds),∀ν,∀h:invariant j ν,∀ω,(stages j hj ν h).Output ω→invariant (j+1) ω

theorem LoopPlan.run {lim : Limits} {rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
    depth K R S T : ℕ} {raws : List ℤ} {words maps : List ℕ} {xl yl zl xr yr zr : List ℤ} {μ : ℕ→ℤ}
    (H : LoopPlan lim rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale
      depth K R S T raws words maps xl yl zl xr yr zr μ) :
    Meets lim (program p R S K raws words maps xl yl zl xr yr zr) 181 depth
      (args rounds m F p seed template host prefixFree alpha2 alphaRank localQ radix J a b scale)
      μ (LightTernaryPrefixLoop.time rounds T) (fun z ν=>z=((p^rounds:ℕ):ℤ) ∧ H.invariant rounds ν) :=
  loop_meets μ H.invariant H.initial H.roundsWord H.depthBound H.powerWords H.inputs H.arguments H.powers
    H.stages H.costs H.transition

end ThreeSum.LightTernaryPrefixPhases
