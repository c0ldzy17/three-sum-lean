import Submission.ThreeSum.TernaryArenaSeedPrimitiveGuards

noncomputable section
namespace ThreeSum.TernaryArenaCandidateGuard
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
open LightTernarySeedScoreFactory TernaryArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

/-- Remaining literal scalar capacities for the three appends, span test,
wanted enumerator and original-key collision histograms. -/
structure Resources {lim : Limits} {depth seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (A : Inputs)
    (D : Data (config p r I A seed)) : Prop where
  requester : I.requesterCount≤I.capacity
  coordinates : A.J+2≤I.capacity
  catalog : A.J*p^(r-1)≤I.capacity
  histogram : p^(r-1)*p≤I.capacity
  wanted : 3*I.requesterCount*(F*TernaryGoodOutputCatalog.cap m p τ)^r≤I.capacity
  divide : Nat.log 2 (2*TernaryArenaSeedPrimitiveGuards.rawCap m p r+1)+2≤I.capacity
  word : (TernaryArenaSeedPrimitiveGuards.word maps τ I A seed positionCap D : ℤ)≤lim.word
  depth : depth+r+6<lim.depth
  seed : seed<I.capacity

def actual (maps : Fin F→Weight m p) (τ cap U : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (seed : ℕ) (D : Data (config p r I A seed))
    (L R : ℕ→ℕ→ℤ) : LightTernaryControllerFactory.Candidate (config p r I A seed) :=
  candidate maps τ cap U (TernaryArenaSeedPrimitiveGuards.rawCap m p r)
    (TernaryNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q I)) Q I A seed D L R

/-- A complete actual candidate guard from canonical data/read invariants
and finite scalar bounds. Every algorithmic component is executed by the
included closed program; no component receipt is an input. -/
theorem guard {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : TernaryArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (hτ : 0<τ) (hraw : 1≤(TernaryGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(actual maps τ cap U Q I A seed D L R).score K|≤lim.word) :
    (actual maps τ cap U Q I A seed D L R).Guard lim depth K (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ := by
  obtain ⟨ga,gs,gw,gc⟩ := TernaryArenaSeedPrimitiveGuards.guards maps τ I A D μ M
    G.wordSpace G.capacity.endSpace G.nB G.nC B.requester B.coordinates B.catalog B.histogram
    B.wanted B.divide B.word B.depth G.family hτ hraw
  exact ⟨TernaryArenaSeedScoreReady.ready maps τ cap Q I A D μ L R ga gs gw gc G B.seed,hpaired⟩

end ThreeSum.TernaryArenaCandidateGuard
