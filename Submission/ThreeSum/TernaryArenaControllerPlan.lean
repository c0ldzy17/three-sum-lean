import Submission.ThreeSum.TernaryArenaControllerCore
import Submission.ThreeSum.LightTernaryFullController

noncomputable section
namespace ThreeSum.TernaryArenaControllerPlan
open Light LightTernaryControllerFactory LightTernarySeedScoreFactory
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaScoreScan
open TernaryArenaControllerCore TernaryArenaLayout
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
set_option maxHeartbeats 5000000
variable {p m F r : ℕ} [Fact p.Prime]

def Replay {A : Inputs} (I : Input) (D : Family (config p r I A 0))
    (K R S i : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ ν : ℕ→ℤ) : Prop :=
  KeepInputs I μ ν ∧
    LightTernarySeedScoreFull.Outputs (withSeed (config p r I A 0) i)
      (D.candidate i).data R S raws words maps ν

def Final {A : Inputs} (I : Input) (D : Family (config p r I A 0))
    (K R S i newSpan : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ ν : ℕ→ℤ) : Prop :=
  ∃ξ, Replay I D K R S i raws words maps μ ξ ∧
    SpanDone (withSeed (config p r I A 0) i) (D.candidate i).data newSpan ξ ν

/-- The actual canonical controller plan. Its scan, replay, and span
transitions are derived here from physical input reads and scalar bounds. -/
def plan {lim : Limits} {depth K U n positionCap scoreCap dB dC dP tB tC tP : ℕ}
    {maps : Fin F→Weight m p} {τ cap : ℕ} {Q : TernaryGoodOutputCatalog.Output m}
    {I : Input} {A : Inputs} {D : (seed : ℕ)→Data (config p r I A seed)}
    {μ : ℕ→ℤ} {L R : ℕ→ℕ→ℤ}
    (H : InputsReady (lim := lim) (depth := depth) (K := K) (U := U) (n := n)
      (positionCap := positionCap) maps τ cap Q I A D μ L R)
    (hn : n≤I.capacity) (hspan : A.J*p^(r-1)*p≤I.capacity)
    (hword : (LightTernaryRowSelector.word n scoreCap dB dC dP tB tC tP : ℤ)≤lim.word)
    (hB : ∀i < n, |(family maps τ cap U Q I A D L R).scoreB i|≤scoreCap)
    (hC : ∀i < n, |(family maps τ cap U Q I A D L R).scoreC i|≤scoreCap)
    (hP : ∀i < n, |(family maps τ cap U Q I A D L R).scoreP K i|≤scoreCap)
    (hexist : ∃i < n, LightTernaryRowSelector.Good
      (family maps τ cap U Q I A D L R).flag (family maps τ cap U Q I A D L R).scoreB
      (family maps τ cap U Q I A D L R).scoreC ((family maps τ cap U Q I A D L R).scoreP K)
      dB dC dP tB tC tP i) :
    FullPlan (config p r I A 0) (family maps τ cap U Q I A D L R) lim depth K
      (4^fixedLength m) F n scoreCap dB dC dP tB tC tP (addr I.free I.capacity 8)
      (seedTime (family maps τ cap U Q I A D L R) K (4^fixedLength m) F n
        (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
        (TernaryGoodOutputCatalog.mapCodes maps τ))
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ := by
  let f := family maps τ cap U Q I A D L R
  let chosen := f.pick K n dB dC dP tB tC tP-1
  have hpos : 0 < f.pick K n dB dC dP tB tC tP :=
    (LightTernaryRowSelector.pick_pos_iff _ _).mpr hexist
  have hle : f.pick K n dB dC dP tB tC tP≤n := LightTernaryRowSelector.pick_le _ _
  have hi : chosen < n := by dsimp [chosen]; omega
  have hiC : chosen < I.capacity := hi.trans_le hn
  have G := H.tensor chosen hi
  have B := H.resources chosen hi
  have hs := G.capacity.endSpace
  have hcapacity := G.headerCells
  have hClim : I.capacity≤lim.space := by
    change finish I.free I.capacity≤lim.space at hs
    unfold finish addr slots at hs
    omega
  refine {
    invariant:=Invariant I (values f K) μ
    replay:=Replay I f K (4^fixedLength m) F chosen
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ
    finalState:=Final I f K (4^fixedLength m) F chosen (addr I.free I.capacity 8)
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ
    spaceWord:=G.wordSpace
    flags:=region_space (by decide) hn hs
    Bscores:=region_space (by decide) hn hs
    Cscores:=region_space (by decide) hn hs
    Pscores:=region_space (by decide) hn hs
    selectorWord:=hword
    length:=B.coordinates.trans hClim
    row:=?_
    depthBound:=by have := B.depth; omega
    initial:=initial I (values f K) μ
    candidate:=?_
    runtime:=fun i hi => runtime_le f K (4^fixedLength m) F n _ _ _ i hi
    nextState:=fun i hi ν ξ h done => next hcapacity (hi.trans_le hn) h done
    reads:=fun ν h => reads h (fun i _ => flag_bound f i) hB hC hP
    existsRow:=hexist
    replayGuard:=?_
    replayState:=?_
    spanGuard:=?_
    finish:=fun ν ξ h hs => ⟨ν,h,hs⟩ }
  · have hm := (H.reads chosen hi).menu
    have hf : I.free≤lim.space := by change finish I.free I.capacity≤lim.space at hs; unfold finish addr slots at hs; omega
    exact (Nat.le_add_right _ (A.J+2)).trans (hm.trans hf)
  · intro i hi ν h
    exact candidate_guard H i hi h.1
  · intro ν h
    exact TernaryArenaGuardTransport.full_guard maps τ cap Q I A (D chosen) μ ν L R
      (H.reads chosen hi) G B h.1 H.prefixAt H.threshold H.nonempty (H.pairedWord chosen hi)
  · intro ν ξ h done
    exact ⟨h.1.trans (done_keep hiC done.1),done.2⟩
  · intro ν h
    exact TernaryArenaGuardTransport.span_guard maps τ cap Q I A (D chosen) μ ν L R
      (H.reads chosen hi) G B h.1 H.prefixAt H.threshold H.nonempty (H.pairedWord chosen hi) hspan

/-- The live controller record survives the replay and span extension.
This supplies the literal header premise of the actual commit suffix. -/
theorem final_seed {I : Input} {A : Inputs} {D : Family (config p r I A 0)}
    {K R S i : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ→ℤ}
    (h : Final I D K R S i (addr I.free I.capacity 8) raws words maps μ ν)
    (hc : 106≤I.capacity) {xs : List ℤ} (hlen : xs.length≤I.capacity)
    (hseed : Seg μ (addr I.free I.capacity 3) xs) :
    Seg ν (addr I.free I.capacity 3) xs := by
  obtain ⟨ξ,hrep,hspan⟩ := h
  intro j hj
  have hjC : j < I.capacity := hj.trans_le hlen
  have hlt : addr I.free I.capacity 3+j<addr I.free I.capacity 8 := by
    unfold addr
    omega
  have hp : Protected I (addr I.free I.capacity 3+j) := by
    unfold Protected addr at *
    omega
  rw [hspan.2.2.2 _ (Or.inl hlt),hrep.1 _ hp]
  exact hseed j hj

end ThreeSum.TernaryArenaControllerPlan
