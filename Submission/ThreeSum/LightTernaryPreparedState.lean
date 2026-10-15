import Submission.ThreeSum.LightTernaryPreparedWanted

/-! A snapshot of genuine scalar resources and retained-bank memory. Its
execution theorem is the actual prepared-query implementation. -/
noncomputable section
namespace ThreeSum.LightTernaryPreparedState
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
open ThreeSum.LightTernaryPreparedWanted
set_option maxHeartbeats 6000000

structure Snapshot (lim : Limits) {N : ℕ} (out bankValues caps : ℕ) (f g : Config)
    (μ : ℕ→ℤ) (Q : TritWord N) (E : Enumeration N f.T f.nb) (F G : TritWord N→ℤ) : Prop where
  fResources : Resources lim (rows Q f.T) f F
  gResources : Resources lim (rows Q f.T) g G
  outside : f.T<rank Q
  ga : g.a=f.a
  gp : g.powers=f.powers
  gactive : g.activeBase=f.activeBase
  gbank : g.bank=f.bank
  gnb : g.nb=f.nb
  gT : g.T=f.T
  bankRead : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ)
  bankSorted : ∀ j k, j<k → k<f.nb → address (E.word j)<address (E.word k)
  Fbank : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j)
  Gbank : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j)
  bankBefore : f.bank+f.nb≤f.a
  Fbefore : f.bv+f.nb≤f.a
  Gbefore : g.bv+f.nb≤f.a
  Hbefore : bankValues+(N+1)*f.nb≤f.a
  Hbank : LightTernaryBankSweep.Stages E
    (fun k => stageValue k (LightTernaryWantedQuery.H F G)) bankValues N μ
  dst : f.a+rows Q f.T≤caps
  caps : caps+N≤f.activeBase
  active : f.activeBase+N≤f.powers
  setupWord : ((4^(N+1) : ℕ) : ℤ)≤lim.word
  GRead : ReadBefore N (rows Q f.T) g f.ws
  FbeforeG : f.vals+rows Q f.T≤g.ws
  Fout : f.vals+rows Q f.T≤out
  Gout : g.vals+rows Q f.T≤out
  outSpace : out+rows Q f.T≤lim.space
  outKeep : f.ws≤out
  productWord : (f.U : ℤ)*(g.U : ℤ)≤lim.word
  queryWord : 4*((4^N : ℕ) : ℤ)*((f.U*g.U : ℕ) : ℤ)+3≤lim.word

theorem Snapshot.meets {lim : Limits} {P : Program} {e : LightTernaryPreparedWanted.Entries} {pMain N out bankValues caps d : ℕ}
    (hmain : P[pMain]?=some (LightTernaryPreparedWanted.body e)) (lib : LightTernaryPreparedWanted.Library P e)
    {f g : Config} {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G)
    (hd : d+3*N+f.L+13≤lim.depth) :
    Meets lim P pMain d (LightTernaryPreparedWanted.args out bankValues caps f g Q) μ (LightTernaryPreparedWanted.time f g Q)
      (fun v ν => v=stageValue N (LightTernaryWantedQuery.H F G) Q ∧ Kept μ ν f.a) := by
  exact LightTernaryPreparedWanted.meets hmain lib f g μ Q E F G
    S.fResources S.gResources S.outside S.ga S.gp S.gactive S.gbank S.gnb S.gT
    S.bankRead S.bankSorted S.Fbank S.Gbank S.bankBefore S.Fbefore S.Gbefore S.Hbefore S.Hbank
    S.dst S.caps S.active S.setupWord S.GRead S.FbeforeG S.Fout S.Gout S.outSpace S.outKeep
    S.productWord S.queryWord hd

theorem Snapshot.transfer {lim : Limits} {N out bankValues caps cut : ℕ}
    {f g : Config} {μ ν : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G)
    (H : ∀ x<cut, ν x=μ x)
    (hcodes : f.bank+f.nb≤cut) (hF : f.bv+f.nb≤cut) (hG : g.bv+f.nb≤cut)
    (hH : bankValues+(N+1)*f.nb≤cut) : Snapshot lim out bankValues caps f g ν Q E F G := by
  refine { S with bankRead:=?_,Fbank:=?_,Gbank:=?_,Hbank:=?_ }
  · intro j hj; rw [H _ (by omega)]; exact S.bankRead j hj
  · intro j hj; rw [H _ (by omega)]; exact S.Fbank j hj
  · intro j hj; rw [H _ (by omega)]; exact S.Gbank j hj
  · intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb hk
    have hs : (N+1)*f.nb=N*f.nb+f.nb := by ring
    rw [H _ (by omega)]
    exact S.Hbank k hk j hj

theorem Snapshot.result_bound {lim : Limits} {N out bankValues caps : ℕ}
    {f g : Config} {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb}
    {F G : TritWord N→ℤ} (S : Snapshot lim out bankValues caps f g μ Q E F G) :
    |stageValue N (LightTernaryWantedQuery.H F G) Q|≤lim.word := by
  have hH : ∀ R, |LightTernaryWantedQuery.H F G R|≤((f.U*g.U : ℕ) : ℤ) := by
    intro R
    rw [LightTernaryWantedQuery.H,abs_mul]
    simpa only [Nat.cast_mul] using mul_le_mul (S.fResources.hvalue R) (S.gResources.hvalue R) (abs_nonneg _) (by positivity)
  have hv := stageValue_abs N le_rfl _ (f.U*g.U) hH Q
  have hnonneg : 0≤((4^N : ℕ) : ℤ)*((f.U*g.U : ℕ) : ℤ) := by positivity
  exact hv.trans (by nlinarith only [S.queryWord,hnonneg])

/-- Geometry and pure source bounds, with no retained-bank memory assumed. -/
structure Plan (lim : Limits) {N : ℕ} (out bankValues caps : ℕ) (f g : Config)
    (Q : TritWord N) (E : Enumeration N f.T f.nb) (F G : TritWord N→ℤ) : Prop where
  fResources : Resources lim (rows Q f.T) f F
  gResources : Resources lim (rows Q f.T) g G
  outside : f.T<rank Q
  ga : g.a=f.a
  gp : g.powers=f.powers
  gactive : g.activeBase=f.activeBase
  gbank : g.bank=f.bank
  gnb : g.nb=f.nb
  gT : g.T=f.T
  bankSorted : ∀ j k, j<k → k<f.nb → address (E.word j)<address (E.word k)
  bankBefore : f.bank+f.nb≤f.a
  Fbefore : f.bv+f.nb≤f.a
  Gbefore : g.bv+f.nb≤f.a
  Hbefore : bankValues+(N+1)*f.nb≤f.a
  dst : f.a+rows Q f.T≤caps
  caps : caps+N≤f.activeBase
  active : f.activeBase+N≤f.powers
  setupWord : ((4^(N+1) : ℕ) : ℤ)≤lim.word
  GRead : ReadBefore N (rows Q f.T) g f.ws
  FbeforeG : f.vals+rows Q f.T≤g.ws
  Fout : f.vals+rows Q f.T≤out
  Gout : g.vals+rows Q f.T≤out
  outSpace : out+rows Q f.T≤lim.space
  outKeep : f.ws≤out
  productWord : (f.U : ℤ)*(g.U : ℤ)≤lim.word
  queryWord : 4*((4^N : ℕ) : ℤ)*((f.U*g.U : ℕ) : ℤ)+3≤lim.word

theorem Plan.snapshot {lim : Limits} {N out bankValues caps : ℕ} {f g : Config}
    {μ : ℕ→ℤ} {Q : TritWord N} {E : Enumeration N f.T f.nb} {F G : TritWord N→ℤ}
    (R : Plan lim out bankValues caps f g Q E F G)
    (hbank : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hF : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j))
    (hG : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j))
    (hH : LightTernaryBankSweep.Stages E
      (fun k => stageValue k (LightTernaryWantedQuery.H F G)) bankValues N μ) :
    Snapshot lim out bankValues caps f g μ Q E F G := by
  exact { R with bankRead := hbank, Fbank := hF, Gbank := hG, Hbank := hH }

end ThreeSum.LightTernaryPreparedState
