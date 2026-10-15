import Submission.ThreeSum.LightTernaryQueryPlan
import Submission.ThreeSum.TernaryNearCanonical

/-! Actual query-local setup followed by Euler reconstruction and full inverse
query. Every near dictionary, power-table and active-mask read is supplied by
preceding machine writes; source and product banks remain read-only. -/
noncomputable section
namespace ThreeSum.LightTernaryPreparedWanted
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}

structure Entries where
  wanted : LightTernaryWantedQuery.Entries
  wantedMain : ℕ
  setup : ℕ
  powers : ℕ
  digits : ℕ
  enum : ℕ
  branch : ℕ

structure Library (P : Program) (e : Entries) : Prop where
  wanted : LightTernaryWantedQuery.Library P e.wanted
  wantedMain : P[e.wantedMain]?=some (LightTernaryWantedQuery.body e.wanted)
  setup : P[e.setup]?=some (LightTernaryNearSetup.body e.powers e.digits e.enum)
  powers : P[e.powers]?=some powTableBody
  digits : P[e.digits]?=some (LightTernaryNearDigits.body e.wanted.near.digit)
  enum : P[e.enum]?=some (LightTernaryNearEnumeration.body e.branch)
  branch : P[e.branch]?=some (LightTernaryNearEnumeration.branchBody e.enum)

def body (e : Entries) : Stmt :=
  .call e.setup [v 0,v 37,v 35,v 1,v 3,v 38,v 9] 39 ;;
  .set 2 (v 39) ;;
  .set 19 (v 39) ;;
  .call e.wantedMain [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,
    v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36] 0

def D {N : ℕ} (Q : TritWord N) (T : ℕ) : ℕ :=rank Q-(T+1)
def rows {N : ℕ} (Q : TritWord N) (T : ℕ) : ℕ :=
  (TernaryNearEnumeration.codes (TernaryBankEnumeration.wordList Q) (D Q T)).length

def args {N : ℕ} (out bankValues caps : ℕ) (f g : Config) (Q : TritWord N) : List ℤ :=
  LightTernaryWantedQuery.args 0 out bankValues f g Q++[(D Q f.T : ℤ),(caps : ℤ)]

def time {N : ℕ} (f g : Config) (Q : TritWord N) : ℕ :=
  LightTernaryNearSetup.time Q (D Q f.T)+LightTernaryWantedQuery.time (rows Q f.T) f g Q+400

theorem meets {e : Entries} {pMain N out bankValues caps d : ℕ}
    (hmain : P[pMain]?=some (body e)) (lib : Library P e)
    (f g : Config) (μ : ℕ→ℤ) (Q : TritWord N) (E : Enumeration N f.T f.nb)
    (F G : TritWord N→ℤ)
    (Rf : Resources lim (rows Q f.T) f F) (Rg : Resources lim (rows Q f.T) g G)
    (hQ : f.T<rank Q)
    (hga : g.a=f.a) (hgp : g.powers=f.powers) (hgactive : g.activeBase=f.activeBase)
    (hgbank : g.bank=f.bank) (hgnb : g.nb=f.nb) (hgT : g.T=f.T)
    (hbankRead : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hbankSorted : ∀ j k, j<k → k<f.nb → address (E.word j)<address (E.word k))
    (hFbank : ∀ j<f.nb, μ (f.bv+j)=binomialZeta F (E.word j))
    (hGbank : ∀ j<f.nb, μ (g.bv+j)=binomialZeta G (E.word j))
    (hbankBefore : f.bank+f.nb≤f.a) (hFbefore : f.bv+f.nb≤f.a) (hGbefore : g.bv+f.nb≤f.a)
    (hHbefore : bankValues+(N+1)*f.nb≤f.a)
    (hHbank : LightTernaryBankSweep.Stages E
      (fun k => stageValue k (LightTernaryWantedQuery.H F G)) bankValues N μ)
    (hdst : f.a+rows Q f.T≤caps) (hcaps : caps+N≤f.activeBase)
    (hactive : f.activeBase+N≤f.powers)
    (hsetupWord : ((4^(N+1) : ℕ) : ℤ)≤lim.word)
    (hGRead : ReadBefore N (rows Q f.T) g f.ws) (hFbeforeG : f.vals+rows Q f.T≤g.ws)
    (hFout : f.vals+rows Q f.T≤out) (hGout : g.vals+rows Q f.T≤out)
    (hOutSpace : out+rows Q f.T≤lim.space) (hOutKeep : f.ws≤out)
    (hproductWord : (f.U : ℤ)*(g.U : ℤ)≤lim.word)
    (hqueryWord : 4*((4^N : ℕ) : ℤ)*((f.U*g.U : ℕ) : ℤ)+3≤lim.word)
    (hd : d+3*N+f.L+13≤lim.depth) :
    Meets lim P pMain d (args out bankValues caps f g Q) μ (time f g Q)
      (fun v ν => v=stageValue N (LightTernaryWantedQuery.H F G) Q ∧ Kept μ ν f.a) := by
  have hw := Rf.hw
  have hws : f.ws≤lim.space := by have := Rf.hmetadataRanks; have := Rf.hrankVals; have := Rf.hvals; have := Rf.hfr; omega
  have hD : D Q f.T≤2*N := (Nat.sub_le _ _).trans (LightTernaryFrozenQuery.rank_le_twice Q)
  have hsetup := LightTernaryNearSetup.meets (d := d+1)
    lib.setup lib.powers lib.digits lib.wanted.near.digit lib.wanted.near.erase lib.enum lib.branch
    μ Q hw (Rf.hp.trans hws) hsetupWord hD hdst hcaps hactive (by omega)
  apply Meets.of_body hmain
  unfold body args time
  light_call hsetup using LightTernaryWantedQuery.args,LightTernaryNearPair.args,rows,D,
    LightTernaryNearSetup.time with count ν ⟨hcount,hNear,hPowers,hActive,hkeep⟩
  have hcount' : count=(rows Q f.T : ℤ) := hcount
  have hrowsWord : (rows Q f.T : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (show rows Q f.T≤lim.space by have := Rf.ha; omega)).trans hw
  light_set (rows Q f.T) using hcount',LightTernaryWantedQuery.args,LightTernaryNearPair.args
  light_set (rows Q f.T) using hcount',LightTernaryWantedQuery.args,LightTernaryNearPair.args
  let nearWords := TernaryNearCanonical.word Q (D Q f.T)
  have hnearRead : ∀ j<rows Q f.T, ν (f.a+j)=(address (nearWords j) : ℤ) :=
    TernaryNearCanonical.read_of_seg Q ν hNear
  have hbankRead' : ∀ j<f.nb, ν (f.bank+j)=(address (E.word j) : ℤ) := by
    intro j hj
    rw [hkeep _ (by omega)]
    exact hbankRead j hj
  have hFbank' : ∀ j<f.nb, ν (f.bv+j)=binomialZeta F (E.word j) := by
    intro j hj
    rw [hkeep _ (by omega)]
    exact hFbank j hj
  have hGbank' : ∀ j<g.nb, ν (g.bv+j)=binomialZeta G (E.word j) := by
    intro j hj
    rw [hkeep _ (by omega)]
    exact hGbank j (by omega)
  have hnearSorted : ∀ j k, j<k → k<rows Q f.T → address (nearWords j)<address (nearWords k) :=
    TernaryNearCanonical.sorted Q (D Q f.T)
  have hnearPresent : ∀ W, Below W Q → f.T<rank W → ∃ j<rows Q f.T, nearWords j=W :=
    fun W hW hR => TernaryNearCanonical.outside_complete Q W hQ hW hR
  have hnearRows : ∀ j<rows Q f.T, Below (nearWords j) Q ∧ f.T<rank (nearWords j) :=
    fun j hj => TernaryNearCanonical.outside_rows Q hQ hj
  have Rf' : Ready lim (rows Q f.T) f ν Q E.word nearWords F :=
    ready Rf hnearRead hbankRead' hActive hPowers hFbank' hbankSorted hnearSorted E.complete hnearPresent hnearRows
  have Rg' : Ready lim (rows Q f.T) g ν Q E.word nearWords G := by
    apply ready Rg
    · simpa only [hga] using hnearRead
    · simpa only [hgbank,hgnb] using hbankRead'
    · simpa only [hgactive] using hActive
    · simpa only [hgp] using hPowers
    · exact hGbank'
    · simpa only [hgnb] using hbankSorted
    · exact hnearSorted
    · simpa only [hgT,hgnb] using E.complete
    · simpa only [hgT] using hnearPresent
    · simpa only [hgT] using hnearRows
  have hHbank' : LightTernaryBankSweep.Stages E
      (fun k => stageValue k (LightTernaryWantedQuery.H F G)) bankValues N ν := by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb hk
    have hs : (N+1)*f.nb=N*f.nb+f.nb := by ring
    rw [hkeep _ (by omega)]
    exact hHbank k hk j hj
  have hWanted := LightTernaryWantedQuery.meets (d := d+1) lib.wantedMain lib.wanted f g ν Q E nearWords F G
    Rf' Rg' hGRead hFbeforeG hFout hGout hOutSpace hOutKeep
    (by have := Rf.ha; omega) hHbank' hproductWord hqueryWord (by omega)
  light_call hWanted using LightTernaryWantedQuery.args,LightTernaryNearPair.args,
    LightTernaryNearSetup.time with result ξ ⟨hout,hkeepWanted⟩
  refine ⟨hout,?_⟩
  intro x hx
  exact (hkeepWanted x (by have := Rf.ha; omega)).trans (hkeep x hx)

/-- Twenty-eight concrete procedures, including physical query setup. -/
def entries : Entries :=⟨LightTernaryWantedQuery.entries,21,22,23,24,25,26⟩

def program : Program :=LightTernaryWantedQuery.program++
  [LightTernaryNearSetup.body 23 24 25,powTableBody,
   LightTernaryNearDigits.body 6,LightTernaryNearEnumeration.body 26,
   LightTernaryNearEnumeration.branchBody 25,body entries]

@[simp] theorem program_length : program.length=28 := rfl

theorem program_library : Library program entries := by
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨?_,rfl,rfl,rfl⟩
  constructor <;> rfl

@[simp] theorem program_main : program[27]?=some (body entries) := rfl

def program_meets {N out bankValues caps d : ℕ} :=
  meets (lim := lim) (P := program) (pMain := 27) (N := N) (out := out)
    (bankValues := bankValues) (caps := caps) (d := d) program_main program_library

end ThreeSum.LightTernaryPreparedWanted
