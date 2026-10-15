import Submission.ThreeSum.LightTernaryNearPair
import Submission.ThreeSum.LightTernaryFrozenQueryPhysical
import Submission.ThreeSum.LightTernaryBankAssembly

/-! Per-wanted physical reconstruction and exact full inverse query. The large
retained banks are read, not rebuilt; query-local work is charged separately. -/
noncomputable section
namespace ThreeSum.LightTernaryWantedQuery
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 12000
variable {lim : Limits} {P : Program}

structure Entries where
  near : LightTernaryNearPair.Entries
  pair : ℕ
  query : ℕ
  lookup : ℕ

structure Library (P : Program) (e : Entries) : Prop where
  near : LightTernaryNearPair.Library P e.near
  pair : P[e.pair]?=some (LightTernaryNearPair.body e.near.source e.near.product)
  query : P[e.query]?=some (LightTernaryFrozenQuery.body e.query e.lookup e.near.digit e.near.zero e.near.erase)
  lookup : P[e.lookup]?=some (LightTernaryQueryLookup.body e.near.search)

def body (e : Entries) : Stmt :=
  .call e.near.rank [v 0,v 35,v 3] 37 ;;
  .call e.pair [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,
    v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34] 38 ;;
  .call e.query [v 0,v 0,v 37,v 8,v 35,v 4,v 5,v 36,v 1,v 2,v 34,v 3,v 7] 0

def args {N : ℕ} (rows out bankValues : ℕ) (f g : Config) (Q : TritWord N) : List ℤ :=
  LightTernaryNearPair.args N rows f++LightTernaryNearPair.args N rows g++
    [(out : ℤ),(address Q : ℤ),(bankValues : ℤ)]

def H {N : ℕ} (F G : TritWord N→ℤ) (R : TritWord N) : ℤ :=
  ThreeSum.TernaryEuler.binomialZeta F R*ThreeSum.TernaryEuler.binomialZeta G R

def time {N : ℕ} (rows : ℕ) (f g : Config) (Q : TritWord N) : ℕ :=
  LightTernaryRank.time N+pairTime N rows f g+LightTernaryFrozenQuery.queryTime f.L f.T N Q+300

theorem meets {e : Entries} {pMain N rows out bankValues d : ℕ}
    (hmain : P[pMain]?=some (body e)) (lib : Library P e)
    (f g : Config) (μ : ℕ→ℤ) (Q : TritWord N) (E : Enumeration N f.T f.nb)
    (nearWords : ℕ→TritWord N) (F G : TritWord N→ℤ)
    (Rf : Ready lim rows f μ Q E.word nearWords F) (Rg : Ready lim rows g μ Q E.word nearWords G)
    (hGRead : ReadBefore N rows g f.ws) (hFbeforeG : f.vals+rows≤g.ws)
    (hFout : f.vals+rows≤out) (hGout : g.vals+rows≤out)
    (hOutSpace : out+rows≤lim.space) (hOutKeep : f.ws≤out)
    (hbankBefore : bankValues+(N+1)*f.nb≤f.ws)
    (hbankStages : LightTernaryBankSweep.Stages E (fun k => stageValue k (H F G)) bankValues N μ)
    (hproductWord : (f.U : ℤ)*(g.U : ℤ)≤lim.word)
    (hqueryWord : 4*((4^N : ℕ) : ℤ)*((f.U*g.U : ℕ) : ℤ)+3≤lim.word)
    (hd : d+3*N+f.L+12≤lim.depth) :
    Meets lim P pMain d (args rows out bankValues f g Q) μ (time rows f g Q)
      (fun v ν => v=stageValue N (H F G) Q ∧ Kept μ ν f.ws) := by
  have hw := Rf.hw
  have hws : f.ws≤lim.space := by have := Rf.hmetadataRanks; have := Rf.hrankVals; have := Rf.hvals; have := Rf.hfr; omega
  have hpSpace : f.powers+(2*N+1)≤lim.space := Rf.hp.trans hws
  have hwordPow : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word := by have := Rf.hword; omega
  have hscalar : ((2*N+16 : ℕ) : ℤ)≤lim.word := by have := Rf.hmemoWord; omega
  have hNword : 2*(N : ℤ)+3≤lim.word := by have := Rf.hmemoWord; omega
  have hcutWord : (f.T : ℤ)+1≤lim.word := by have := Rf.hcontrols; omega
  have hqueryBaseWord : ((f.nb+rows+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word := by have := Rf.hword; omega
  have hrank := LightTernaryRank.meets (d := d+1) lib.near.rank lib.near.digit lib.near.erase
    μ hw hpSpace hwordPow hscalar Rf.hpowers (address_lt_pow_two Q) (by omega)
  apply Meets.of_body hmain
  unfold body args time
  light_call hrank using LightTernaryNearPair.args,LightTernaryRank.time with rankValue μr ⟨hrankValue,hmem⟩
  subst μr
  have hrankQ : rankValue=(rank Q : ℤ) := by rw [hrankValue,LightTernaryRank.partialRank_address]
  have hpair := LightTernaryNearPair.meets (d := d+1) lib.pair lib.near f g μ Q E.word nearWords F G
    Rf Rg hGRead hFbeforeG hFout hGout hOutSpace hOutKeep hproductWord (by omega)
  light_call hpair using LightTernaryNearPair.args,LightTernaryRank.time,LightTernaryNearPair.pairTime
    with result ν ⟨_,hkeep,hnearH⟩
  have hH : ∀ R, |H F G R|≤((f.U*g.U : ℕ) : ℤ) := by
    intro R
    rw [H,abs_mul]
    simpa only [Nat.cast_mul] using mul_le_mul (Rf.hvalue R) (Rg.hvalue R) (abs_nonneg _) (by positivity)
  have hbankRead : ∀ j<f.nb, ν (f.bank+j)=(address (E.word j) : ℤ) := by
    intro j hj
    rw [hkeep _ (by have := Rf.hb; omega)]
    exact Rf.hbankRead j hj
  have hpowers : Powers ν f.powers (2*N) := by
    intro j hj
    rw [hkeep _ (by have := Rf.hp; omega)]
    exact Rf.hpowers j hj
  have hbankValues : ∀ k≤N, ∀ j<f.nb,
      ν (bankValues+k*f.nb+j)=stageValue k (H F G) (E.word j) := by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb hk
    have hs : (N+1)*f.nb=N*f.nb+f.nb := by ring
    rw [hkeep _ (by omega)]
    exact hbankStages k hk j hj
  have hnearRead : ∀ j<rows, ν (f.a+j)=(address (nearWords j) : ℤ) := by
    intro j hj
    rw [hkeep _ (by have := Rf.ha; omega)]
    exact Rf.hread j hj
  have hnearValues : ∀ j<rows, ν (out+j)=H F G (nearWords j) := hnearH
  have hquery := LightTernaryFrozenQuery.meets
    lib.query lib.lookup lib.near.search lib.near.digit lib.near.zero lib.near.erase
    f.T f.bank f.nb bankValues f.a rows out f.powers f.L (f.U*g.U)
    E.word nearWords (H F G) Q ν hw (Rf.hb.trans hws) (hbankBefore.trans hws)
    (Rf.ha.trans hws) hOutSpace hpSpace hqueryBaseWord hNword hcutWord hqueryWord
    hpowers Rf.hL Rf.hnb Rf.hnn hH hbankRead Rf.hbankSorted E.complete hbankValues
    hnearRead Rf.hnearSorted Rf.hnearPresent hnearValues N le_rfl Q (fun _ => le_rfl) (d+1) (by omega)
  light_call hquery using hrankQ,LightTernaryFrozenQuery.inputs,LightTernaryNearPair.args,
    LightTernaryRank.time,LightTernaryNearPair.pairTime with output ν' ⟨hout,hmem⟩
  subst ν'
  exact ⟨hout,hkeep⟩

/-- The source values required by Euler reconstruction are exactly the final
forward-stage cells produced by the bank assembler. -/
theorem source_bank_read {N T n base : ℕ} (E : Enumeration N T n)
    (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hs : LightTernaryBankSweep.Stages E (fun k => forwardStage k F) base N μ) :
    ∀ j<n, μ (base+N*n+j)=ThreeSum.TernaryEuler.binomialZeta F (E.word j) := by
  intro j hj
  simpa only [forwardStage_full] using hs N le_rfl j hj

/-- The assembler's product is the full transformed product consumed by both
near reconstruction and the frozen query. -/
theorem assembled_product_eq {N : ℕ} (F G : TritWord N→ℤ) :
    LightTernaryBankAssembly.product F G=H F G := by
  funext R
  simp only [LightTernaryBankAssembly.product,H,forwardStage_full]

theorem assembled_inverse_bank {N T n base : ℕ} (E : Enumeration N T n)
    (F G : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hs : LightTernaryBankSweep.Stages E
      (fun k => stageValue k (LightTernaryBankAssembly.product F G)) base N μ) :
    LightTernaryBankSweep.Stages E (fun k => stageValue k (H F G)) base N μ := by
  simpa only [assembled_product_eq] using hs

/-- The finite query implementation reuses the reconstruction library's actual
rank, digit, mask-erasure and search procedures. -/
def entries : Entries :=⟨LightTernaryNearPair.entries,18,19,20⟩

def program : Program :=LightTernaryNearPair.program++
  [LightTernaryFrozenQuery.body 19 20 6 7 8,
   LightTernaryQueryLookup.body 10,body entries]

@[simp] theorem program_length : program.length=22 := rfl

theorem program_library : Library program entries := by
  refine ⟨?_,rfl,rfl,rfl⟩
  constructor <;> rfl

@[simp] theorem program_main : program[21]?=some (body entries) := rfl

def program_meets {N rows out bankValues d : ℕ} :=
  meets (lim := lim) (P := program) (pMain := 21) (N := N) (rows := rows)
    (out := out) (bankValues := bankValues) (d := d) program_main program_library

/-- Rewrite the actual physical result to the original additive count. This
uses the proved full-stage factorial convolution identity. -/
theorem weighted_count_spec {N a b pMain d t : ℕ} (argv : List ℤ) (μ : ℕ→ℤ)
    (f g : TritWord N→ℤ) (Q : TritWord N) (keep : ℕ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (hQ : rank Q=a+b)
    (hquery : Meets lim P pMain d argv μ t (fun v ν =>
      v=stageValue N (H (fun A => ThreeSum.TernaryConvolution.factorial A*f A)
        (fun B => ThreeSum.TernaryConvolution.factorial B*g B)) Q ∧ Kept μ ν keep)) :
    Meets lim P pMain d argv μ t (fun v ν =>
      v=ThreeSum.TernaryConvolution.factorial Q*ThreeSum.TernaryConvolution.convolution f g Q ∧
        Kept μ ν keep) := by
  apply hquery.mono le_rfl
  intro v ν hv
  refine ⟨hv.1.trans ?_,hv.2⟩
  exact LightTernaryFrozenQuery.stageValue_count f g hf hg Q hQ

end ThreeSum.LightTernaryWantedQuery
