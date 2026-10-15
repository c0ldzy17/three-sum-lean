import Submission.ThreeSum.TernarySourceExecutionFactory
import Submission.ThreeSum.TernaryFrontendResources

/-! Pure count-frontend readiness and its actual execution theorem. Source
bank reads are supplied by the preceding source executions, never advice. -/
noncomputable section
namespace ThreeSum.TernaryCountExecutionFactory
open Light TernaryJointType TernaryBank TernaryCodeSemantics
open TernaryBankStageModel
open LightTernaryNearPair LightTernaryWantedRowDispatch LightTernaryPreparedState
open LightSubsetAddress

structure Setup (N : ℕ) where
  f : Config
  g : Config
  Qstar : TritWord N
  Q : ℕ→TritWord N
  group : ℕ→ℕ
  E : Enumeration N f.T f.nb
  bankPowers : ℕ
  keyBase : ℕ
  groups : ℕ
  fsource : ℕ
  gsource : ℕ
  fbase : ℕ
  gbase : ℕ
  hbase : ℕ
  out : ℕ
  caps : ℕ
  records : ℕ
  count : ℕ
  dst : ℕ
  V : ℕ
  t : ℕ

def Setup.argv {N : ℕ} (S : Setup N) : List ℤ :=
  LightTernaryCountFrontend.args S.f S.g S.Qstar S.bankPowers S.keyBase S.groups
    S.fsource S.gsource S.fbase S.gbase S.hbase S.out S.caps S.records S.count S.dst

def Setup.runtime {N : ℕ} (S : Setup N) : ℕ :=
  LightTernaryCountFrontend.time S.groups N S.f.L S.f.nb S.count S.t

structure Ready {N : ℕ} (S : Setup N) (lim : Limits) (d : ℕ) (μ : ℕ→ℤ)
    (F G : ℕ→TritWord N→ℤ) : Prop where
  hw : (lim.space : ℤ)≤lim.word
  ha : S.f.bank+S.f.nb≤S.keyBase
  hfs : S.fsource+S.groups*S.f.nb≤S.keyBase
  hgs : S.gsource+S.groups*S.f.nb≤S.keyBase
  hmeta : S.keyBase+4*S.f.nb≤S.bankPowers
  hpows : S.bankPowers+(2*N+1)≤S.fbase
  hfg : S.fbase+S.groups*((N+1)*S.f.nb)≤S.gbase
  hgh : S.gbase+S.groups*((N+1)*S.f.nb)≤S.hbase
  hHdst : S.hbase+S.groups*((N+1)*S.f.nb)≤S.dst
  hword : ((S.f.nb+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word
  hNword : 2*(N : ℤ)+3≤lim.word
  hgroupsWord : (S.groups : ℤ)+1≤lim.word
  hcodes : ∀ j<S.f.nb, μ (S.f.bank+j)=(address (S.E.word j) : ℤ)
  hsorted : ∀ j k, j<k → k<S.f.nb → address (S.E.word j)<address (S.E.word k)
  hF : ∀ bucket<S.groups, ∀ R, |F bucket R|≤(S.V : ℤ)
  hG : ∀ bucket<S.groups, ∀ R, |G bucket R|≤(S.V : ℤ)
  hforwardWord : 4*((4^N*S.V : ℕ) : ℤ)+3≤lim.word
  hproductWord : (LightTernaryBankAssembly.valueBound N S.V : ℤ)≤lim.word
  hinverseWord : 4*((4^N*LightTernaryBankAssembly.valueBound N S.V : ℕ) : ℤ)+3≤lim.word
  hL : S.f.L≤2*N
  hn : S.f.nb<2^S.f.L
  hrecords : S.records+3*S.count≤S.keyBase
  hdst : S.dst+S.count≤S.f.a
  hspace : S.f.a≤lim.space
  hreadGroup : ∀ j<S.count, μ (S.records+3*j+2)=(S.group j : ℤ)
  hreadQ : ∀ j<S.count, μ (S.records+3*j+1)=(address (S.Q j) : ℤ)
  hgroup : ∀ j<S.count, S.group j<S.groups
  hRank : ∀ j<S.count, rank (S.Q j)=rank S.Qstar
  hcountWord : (S.count : ℤ)+1≤lim.word
  hstrideWord : (((N+1)*S.f.nb : ℕ) : ℤ)≤lim.word
  htailWord : ((N*S.f.nb : ℕ) : ℤ)≤lim.word
  hplan : ∀ j<S.count, Plan lim S.out (S.hbase+S.group j*((N+1)*S.f.nb)) S.caps
      (sourceConfig S.f S.fbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j))
      (sourceConfig S.g S.gbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j))
      (S.Q j) S.E (F (S.group j)) (G (S.group j))
  htime : ∀ j<S.count, LightTernaryPreparedWanted.time
      (sourceConfig S.f S.fbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j))
      (sourceConfig S.g S.gbase ((N+1)*S.f.nb) (N*S.f.nb) (S.group j)) (S.Q j)≤S.t
  hd : d+3*N+S.f.L+16≤lim.depth

/-- All source-value reads are consequences of actual source receipts. All
remaining premises are pure finite, memory, or resource bounds. -/
theorem Ready.run {N : ℕ} {S : Setup N} {lim : Limits} {d : ℕ} {μ : ℕ→ℤ}
    {F G : ℕ→TritWord N→ℤ} (H : Ready S lim d μ F G)
    (hsourceF : LightTernarySourceCountHost.BankReads μ S.fsource S.groups S.f.nb
      (fun g r => F g (S.E.word r)))
    (hsourceG : LightTernarySourceCountHost.BankReads μ S.gsource S.groups S.f.nb
      (fun g r => G g (S.E.word r))) :
    Meets lim LightTernaryCountFrontend.program 50 d S.argv μ S.runtime
      (fun _ ν => Kept μ ν S.keyBase ∧ ∀ j<S.count,
        ν (S.dst+j)=LightTernaryWantedRows.score F G S.group S.Q j) := by
  exact LightTernaryCountFrontend.meets S.f S.g S.Qstar S.Q S.group F G S.E μ
    H.hw H.ha H.hfs H.hgs H.hmeta H.hpows H.hfg H.hgh H.hHdst H.hword H.hNword H.hgroupsWord H.hcodes hsourceF hsourceG H.hsorted H.hF H.hG H.hforwardWord H.hproductWord H.hinverseWord H.hL H.hn H.hrecords H.hdst H.hspace H.hreadGroup H.hreadQ H.hgroup H.hRank H.hcountWord H.hstrideWord H.htailWord H.hplan H.htime H.hd

theorem Ready.transport {N : ℕ} {S : Setup N} {lim : Limits} {d keep : ℕ}
    {μ ν : ℕ→ℤ} {F G : ℕ→TritWord N→ℤ}
    (H : Ready S lim d μ F G) (hkeep : Kept μ ν keep)
    (hcodes : S.f.bank+S.f.nb≤keep) (hrecords : S.records+3*S.count≤keep) :
    Ready S lim d ν F G := by
  refine {H with hcodes := ?_,hreadGroup := ?_,hreadQ := ?_}
  · intro i hi
    exact (hkeep _ (by omega)).trans (H.hcodes i hi)
  · intro i hi
    have hm := Nat.mul_le_mul_left 3 (show i+1≤S.count by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hm
    exact (hkeep _ (by omega)).trans (H.hreadGroup i hi)
  · intro i hi
    have hm := Nat.mul_le_mul_left 3 (show i+1≤S.count by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hm
    exact (hkeep _ (by omega)).trans (H.hreadQ i hi)

end ThreeSum.TernaryCountExecutionFactory
