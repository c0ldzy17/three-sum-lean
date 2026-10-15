import Submission.ThreeSum.LightTernaryWantedRowDispatch
import Submission.ThreeSum.LightTernaryPreparedState

/-! Actual literal wanted-row traversal with map-vector bank dispatch. Each
row has original-position, canonical target-code, and map-group cells. Equal
rows and equal input values remain separate occurrences. -/
noncomputable section
namespace ThreeSum.LightTernaryWantedRows
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 7000000
set_option maxRecDepth 18000
variable {lim : Limits} {P : Program}

def roundBody (pRow : ℕ) : Stmt :=
  .call pRow [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,
    v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,
    v 39 +' k 3 *' v 48,v 47 +' v 48,v 41,v 42,v 43,v 44,v 45] 49

def body (pRow : ℕ) : Stmt :=.for 48 (v 46) (roundBody pRow)

def args {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (out bankValues caps records count dst fbase gbase hbase stride tail : ℕ) : List ℤ :=
  LightTernaryWantedRowDispatch.args f g Qstar out bankValues caps records dst fbase gbase hbase stride tail++
    [(count : ℤ),dst]

def time (count t : ℕ) : ℕ :=count*(LightTernaryWantedRowDispatch.time t+200)+100

def score {N : ℕ} (F G : ℕ→TritWord N→ℤ) (group : ℕ→ℕ) (Q : ℕ→TritWord N) (j : ℕ) : ℤ :=
  stageValue N (LightTernaryWantedQuery.H (F (group j)) (G (group j))) (Q j)

def Inv {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (out bankValues caps records count dst fbase gbase hbase stride tail : ℕ)
    (μ : ℕ→ℤ) (value : ℕ→ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ→ℤ),
    σ=⟨frame (args f g Qstar out bankValues caps records count dst fbase gbase hbase stride tail++[(j : ℤ),r]),ν⟩ ∧
    Kept μ ν dst ∧ ∀ k<j, ν (dst+k)=value k

theorem meets {e : LightTernaryPreparedWanted.Entries}
    {pMain pRow pPrepare N out bankValues caps records count dst fbase gbase hbase stride tail groups d t : ℕ}
    (hmain : P[pMain]?=some (body pRow))
    (hrow : P[pRow]?=some (LightTernaryWantedRowDispatch.body pPrepare))
    (hprepare : P[pPrepare]?=some (LightTernaryPreparedWanted.body e))
    (lib : LightTernaryPreparedWanted.Library P e)
    (f g : Config) (Qstar : TritWord N) (Q : ℕ→TritWord N) (group : ℕ→ℕ)
    (F G : ℕ→TritWord N→ℤ) (E : Enumeration N f.T f.nb) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hrecords : records+3*count≤dst) (hdst : dst+count≤f.a) (hspace : f.a≤lim.space)
    (hcodesBefore : f.bank+f.nb≤dst)
    (hfg : fbase+groups*stride≤gbase) (hgh : gbase+groups*stride≤hbase)
    (hHdst : hbase+groups*stride≤dst) (htail : tail+f.nb=stride) (hstage : stride=(N+1)*f.nb)
    (hreadGroup : ∀ j<count, μ (records+3*j+2)=(group j : ℤ))
    (hreadQ : ∀ j<count, μ (records+3*j+1)=(address (Q j) : ℤ))
    (hgroup : ∀ j<count, group j<groups)
    (hRank : ∀ j<count, rank (Q j)=rank Qstar)
    (hgroupsWord : (groups : ℤ)≤lim.word) (hcountWord : (count : ℤ)+1≤lim.word)
    (hstrideWord : (stride : ℤ)≤lim.word) (htailWord : (tail : ℤ)≤lim.word)
    (hsnapshot : ∀ j<count, Snapshot lim out (hbase+group j*stride) caps
      (sourceConfig f fbase stride tail (group j)) (sourceConfig g gbase stride tail (group j))
      μ (Q j) E (F (group j)) (G (group j)))
    (htime : ∀ j<count, LightTernaryPreparedWanted.time
      (sourceConfig f fbase stride tail (group j)) (sourceConfig g gbase stride tail (group j)) (Q j)≤t)
    (hd : d+3*N+f.L+15≤lim.depth) :
    Meets lim P pMain d (args f g Qstar out bankValues caps records count dst fbase gbase hbase stride tail)
      μ (time count t)
      (fun _ ν => Kept μ ν dst ∧ ∀ j<count, ν (dst+j)=score F G group Q j) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv f g Qstar out bankValues caps records count dst fbase gbase hbase stride tail μ (score F G group Q)) count
    (LightTernaryWantedRowDispatch.time t+180) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,?_,?_⟩
    · simp only [update_frame_setLocal]
      congr 1
      simp only [args,LightTernaryWantedRowDispatch.args,LightTernaryPreparedWanted.args,
        LightTernaryWantedQuery.args,LightTernaryNearPair.args,setLocal]
      exact (frame_append_zeros _ 1).symm
    · intro x _; rfl
    · intro k hk; omega
  case round =>
    rintro j _ hj _ ⟨r,ν,rfl,hkeep,hvalues⟩
    have hg := hgroup j hj
    have hnext : group j*stride+stride≤groups*stride := by
      have h := Nat.mul_le_mul_right stride (show group j+1≤groups by omega)
      simpa only [Nat.add_mul,Nat.one_mul] using h
    have hFbefore : fbase+group j*stride+tail+f.nb≤dst := by omega
    have hGbefore : gbase+group j*stride+tail+f.nb≤dst := by omega
    have hHbefore : hbase+group j*stride+(N+1)*f.nb≤dst := by
      rw [← hstage]
      omega
    have S := (hsnapshot j hj).transfer hkeep hcodesBefore hFbefore hGbefore hHbefore
    have hquery := (S.meets hprepare lib (d := d+2) (by dsimp [sourceConfig]; omega)).mono_time (htime j hj)
    have hrG : ν ((records+3*j)+2)=(group j : ℤ) := by rw [hkeep _ (by omega)]; exact hreadGroup j hj
    have hrQ : ν ((records+3*j)+1)=(address (Q j) : ℤ) := by rw [hkeep _ (by omega)]; exact hreadQ j hj
    have hD : LightTernaryPreparedWanted.D (Q j) f.T=LightTernaryPreparedWanted.D Qstar f.T := by
      unfold LightTernaryPreparedWanted.D
      rw [hRank j hj]
    have hqNat : address (Q j)≤4^(N+1) := by
      have hlt : address (Q j)<4^N := by
        simpa only [address,TernaryBankEnumeration.wordList_length] using
          TernaryAddresses.code_lt (TernaryBankEnumeration.wordList (Q j)) (TernaryBankEnumeration.wordList_digits (Q j))
      exact (Nat.le_of_lt hlt).trans (Nat.pow_le_pow_right (by decide) (by omega))
    have hQWord : (address (Q j) : ℤ)≤lim.word :=
      (Int.ofNat_le.mpr hqNat).trans (hsnapshot j hj).setupWord
    have hmulWord : (group j : ℤ)*(stride : ℤ)≤lim.word :=
      (by exact_mod_cast (show group j*stride≤lim.space by omega) : (group j : ℤ)*(stride : ℤ)≤(lim.space : ℤ)).trans hw
    have hfWord : (fbase : ℤ)+(group j : ℤ)*(stride : ℤ)+(tail : ℤ)≤lim.word :=
      (by exact_mod_cast (show fbase+group j*stride+tail≤lim.space by omega) :
        (fbase : ℤ)+(group j : ℤ)*(stride : ℤ)+(tail : ℤ)≤(lim.space : ℤ)).trans hw
    have hgWord : (gbase : ℤ)+(group j : ℤ)*(stride : ℤ)+(tail : ℤ)≤lim.word :=
      (by exact_mod_cast (show gbase+group j*stride+tail≤lim.space by omega) :
        (gbase : ℤ)+(group j : ℤ)*(stride : ℤ)+(tail : ℤ)≤(lim.space : ℤ)).trans hw
    have hhWord : (hbase : ℤ)+(group j : ℤ)*(stride : ℤ)≤lim.word :=
      (by exact_mod_cast (show hbase+group j*stride≤lim.space by omega) :
        (hbase : ℤ)+(group j : ℤ)*(stride : ℤ)≤(lim.space : ℤ)).trans hw
    have hgWord' : (group j : ℤ)≤lim.word := by
      have hz : (group j : ℤ)<(groups : ℤ) := by exact_mod_cast hg
      omega
    have hc := LightTernaryWantedRowDispatch.meets (d := d+1)
      (record := records+3*j) (dst := dst+j) (bankValues := bankValues) hrow f g Qstar (Q j) ν (score F G group Q j)
      hw (by omega) (by omega) hrG hrQ hgWord'
      hQWord hstrideWord htailWord hmulWord hfWord hgWord hhWord hD (S.result_bound) (by omega) hquery
    have htrip : (3 : ℤ)*(j : ℤ)≤lim.word :=
      (by exact_mod_cast (show 3*j≤lim.space by omega) : (3 : ℤ)*(j : ℤ)≤(lim.space : ℤ)).trans hw
    have hrecordWord : (records : ℤ)+3*(j : ℤ)≤lim.word :=
      (by exact_mod_cast (show records+3*j≤lim.space by omega) : (records : ℤ)+3*(j : ℤ)≤(lim.space : ℤ)).trans hw
    have hdstWord : (dst : ℤ)+(j : ℤ)≤lim.word :=
      (by exact_mod_cast (show dst+j≤lim.space by omega) : (dst : ℤ)+(j : ℤ)≤(lim.space : ℤ)).trans hw
    unfold roundBody
    light_call hc using args,LightTernaryWantedRowDispatch.args,LightTernaryPreparedWanted.args,
      LightTernaryWantedQuery.args,LightTernaryNearPair.args,LightTernaryWantedRowDispatch.time with result ξ ⟨ν',hkeep',rfl⟩
    refine ⟨by simp [args,LightTernaryWantedRowDispatch.args,LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,LightTernaryNearPair.args,setLocal],result,Function.update ν' (dst+j) (score F G group Q j),?_,?_,?_⟩
    · simp [Inv,update_frame_setLocal,args,LightTernaryWantedRowDispatch.args,LightTernaryPreparedWanted.args,
        LightTernaryWantedQuery.args,LightTernaryNearPair.args]
    · intro x hx
      rw [Function.update_of_ne (by omega),hkeep' x (by omega)]
      exact hkeep x hx
    · intro k hk
      by_cases he : k=j
      · subst k; simp
      · have hkj : k<j := by omega
        rw [Function.update_of_ne (by omega),hkeep' _ (by omega)]
        exact hvalues k hkj
  case done =>
    rintro _ _ ⟨r,ν,rfl,hkeep,hvalues⟩
    exact ⟨hkeep,hvalues⟩
  case bound =>
    rintro j _ hj _ ⟨r,ν,rfl,hkeep,hvalues⟩
    light_side [args,LightTernaryWantedRowDispatch.args,LightTernaryPreparedWanted.args,
      LightTernaryWantedQuery.args,LightTernaryNearPair.args]

/-- Closed thirty-procedure wanted-row frontend. Retained group banks are
built once by `LightTernaryGroupedBanks`, then read by this program. -/
def program : Program :=LightTernaryPreparedWanted.program++
  [LightTernaryWantedRowDispatch.body 27,body 28]

@[simp] theorem program_length : program.length=30 := rfl

theorem program_library : LightTernaryPreparedWanted.Library program LightTernaryPreparedWanted.entries := by
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨?_,rfl,rfl,rfl⟩
  constructor <;> rfl

def program_meets {N out bankValues caps records count dst fbase gbase hbase stride tail groups d t : ℕ} :=
  meets (lim := lim) (P := program) (pMain := 29) (pRow := 28) (pPrepare := 27)
    (N := N) (out := out) (bankValues := bankValues) (caps := caps) (records := records)
    (count := count) (dst := dst) (fbase := fbase) (gbase := gbase) (hbase := hbase)
    (stride := stride) (tail := tail) (groups := groups) (d := d) (t := t)
    rfl rfl rfl program_library

end ThreeSum.LightTernaryWantedRows
