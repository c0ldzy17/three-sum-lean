import Submission.ThreeSum.LightTernaryGroupBankResources
import Submission.ThreeSum.LightTernaryWantedRows

/-! One concrete program for paid group-bank construction followed by physical
wanted-row counting. Its dictionaries and source histograms are inputs from
the actual join/histogram frontend. -/
noncomputable section
namespace ThreeSum.LightTernaryCountFrontend
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryWantedRowDispatch ThreeSum.LightTernaryPreparedState
set_option maxHeartbeats 8000000
set_option maxRecDepth 18000

def nearEntries : LightTernaryNearPair.Entries :=
  ⟨20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37⟩
def wantedEntries : LightTernaryWantedQuery.Entries :=⟨nearEntries,38,39,40⟩
def preparedEntries : LightTernaryPreparedWanted.Entries :=⟨wantedEntries,41,42,43,44,45,46⟩

def body : Stmt :=
  .call 51 [v 3,k 2 *' v 0 +' k 1,k 2] 60 ;;
  .call 19 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11] 60 ;;
  .call 49 [v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,
    v 29,v 30,v 31,v 32,v 33,v 34,v 35,v 36,v 37,v 38,v 39,v 40,v 41,v 42,v 43,v 44,v 45,v 46,v 47,v 48,v 49,v 50,v 51,v 52,v 53,v 54,v 55,v 56,v 57,v 58,v 59] 0

def tail : Program :=[
  LightTernaryNearSource.body 21 22 23,LightTernaryRankTable.body 29,
  LightTernaryEulerMetadata.body 24,LightTernaryEulerMemo.body 31,
  LightTernaryPredecessorTable.body 25 26,LightTernaryPredecessor.body 26 27 28 29 30,
  LightTernaryCodes.digitBody 28,LightTernaryCodes.zeroBody 28,LightMaskErase.body 28,
  LightTernaryRank.body 26,LightBandLookup.searchBody 30,LightTernaryEulerScan.body 32,
  LightTernaryEulerRow.fillBody 33,LightTernaryEulerRow.body 34 35,LightTernaryWeightedSum.body,
  LightTernaryDivide.body 36,LightOutputDecodeDivide.body,LightTernaryProduct.body,
  LightTernaryNearPair.body 20 37,
  LightTernaryFrozenQuery.body 39 40 26 27 28,LightTernaryQueryLookup.body 30,
  LightTernaryWantedQuery.body wantedEntries,
  LightTernaryNearSetup.body 43 44 45,powTableBody,LightTernaryNearDigits.body 26,
  LightTernaryNearEnumeration.body 46,LightTernaryNearEnumeration.branchBody 45,
  LightTernaryPreparedWanted.body preparedEntries,
  LightTernaryWantedRowDispatch.body 47,LightTernaryWantedRows.body 48,body,powTableBody]

def program : Program :=LightTernaryGroupedBanks.program++tail

@[simp] theorem program_length : program.length=52 := rfl

theorem library : LightTernaryPreparedWanted.Library program preparedEntries := by
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl⟩
  refine ⟨?_,rfl,rfl,rfl⟩
  constructor <;> rfl

@[simp] theorem main : program[50]?=some body := rfl
@[simp] theorem rows : program[49]?=some (LightTernaryWantedRows.body 48) := rfl
@[simp] theorem row : program[48]?=some (LightTernaryWantedRowDispatch.body 47) := rfl
@[simp] theorem prepared : program[47]?=some (LightTernaryPreparedWanted.body preparedEntries) := rfl


def args {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst : ℕ) : List ℤ :=
  [(N : ℤ),f.bank,f.nb,bankPowers,f.L,keyBase,groups,fsource,gsource,fbase,gbase,hbase]++
    LightTernaryWantedRows.args f g Qstar out hbase caps records count dst fbase gbase hbase
      ((N+1)*f.nb) (N*f.nb)

def time (groups N L n count t : ℕ) : ℕ :=
  powTableTime (2*N+1)+LightTernaryGroupedBanks.time groups N L n+LightTernaryWantedRows.time count t+700

theorem meets {lim : Limits} {N bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst d V t : ℕ}
    (f g : Config) (Qstar : TritWord N) (Q : ℕ→TritWord N) (group : ℕ→ℕ)
    (F G : ℕ→TritWord N→ℤ) (E : Enumeration N f.T f.nb) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : f.bank+f.nb≤keyBase) (hfs : fsource+groups*f.nb≤keyBase) (hgs : gsource+groups*f.nb≤keyBase)
    (hmeta : keyBase+4*f.nb≤bankPowers) (hpows : bankPowers+(2*N+1)≤fbase)
    (hfg : fbase+groups*((N+1)*f.nb)≤gbase) (hgh : gbase+groups*((N+1)*f.nb)≤hbase)
    (hHdst : hbase+groups*((N+1)*f.nb)≤dst)
    (hword : ((f.nb+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word) (hgroupsWord : (groups : ℤ)+1≤lim.word)
    (hcodes : ∀ j<f.nb, μ (f.bank+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ g<groups, ∀ j<f.nb, μ (fsource+g*f.nb+j)=F g (E.word j))
    (hsourceG : ∀ g<groups, ∀ j<f.nb, μ (gsource+g*f.nb+j)=G g (E.word j))
    (hsorted : ∀ j k, j<k → k<f.nb → address (E.word j)<address (E.word k))
    (hF : ∀ g<groups, ∀ R, |F g R|≤(V : ℤ)) (hG : ∀ g<groups, ∀ R, |G g R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (LightTernaryBankAssembly.valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*LightTernaryBankAssembly.valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : f.L≤2*N) (hn : f.nb<2^f.L)
    (hrecords : records+3*count≤keyBase) (hdst : dst+count≤f.a) (hspace : f.a≤lim.space)
    (hreadGroup : ∀ j<count, μ (records+3*j+2)=(group j : ℤ))
    (hreadQ : ∀ j<count, μ (records+3*j+1)=(address (Q j) : ℤ))
    (hgroup : ∀ j<count, group j<groups) (hRank : ∀ j<count, rank (Q j)=rank Qstar)
    (hcountWord : (count : ℤ)+1≤lim.word)
    (hstrideWord : (((N+1)*f.nb : ℕ) : ℤ)≤lim.word) (htailWord : ((N*f.nb : ℕ) : ℤ)≤lim.word)
    (hplan : ∀ j<count, Plan lim out (hbase+group j*((N+1)*f.nb)) caps
      (sourceConfig f fbase ((N+1)*f.nb) (N*f.nb) (group j))
      (sourceConfig g gbase ((N+1)*f.nb) (N*f.nb) (group j))
      (Q j) E (F (group j)) (G (group j)))
    (htime : ∀ j<count, LightTernaryPreparedWanted.time
      (sourceConfig f fbase ((N+1)*f.nb) (N*f.nb) (group j))
      (sourceConfig g gbase ((N+1)*f.nb) (N*f.nb) (group j)) (Q j)≤t)
    (hd : d+3*N+f.L+16≤lim.depth) :
    Meets lim program 50 d
      (args f g Qstar bankPowers keyBase groups fsource gsource fbase gbase hbase out caps records count dst)
      μ (time groups N f.L f.nb count t)
      (fun _ ν => Kept μ ν keyBase ∧ ∀ j<count, ν (dst+j)=LightTernaryWantedRows.score F G group Q j) := by
  have hbankSpace : hbase+groups*((N+1)*f.nb)≤lim.space := by omega
  have hpowerSpace : bankPowers+(2*N+1)≤lim.space := by omega
  have hpowBound : ∀ j≤2*N+1, ((2^j : ℕ) : ℤ)≤lim.word := by
    intro j hj
    have hle := Nat.pow_le_pow_right (by decide : 1≤2) hj
    have hcast : ((2^j : ℕ) : ℤ)≤((2^(2*N+1) : ℕ) : ℤ) := by exact_mod_cast hle
    exact hcast.trans (by omega)
  have hpow := powTable_meets (P := program) (p := 51) (d := d+1)
    (μ := μ) (dst := bankPowers) (L := 2*N+1) (b := 2) rfl hw hpowerSpace hpowBound
  apply Meets.of_body main
  unfold body args time
  light_call hpow using LightTernaryWantedRows.args,LightTernaryWantedRowDispatch.args,
    LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,LightTernaryNearPair.args,
    powTableTime with powerResult μp ⟨hpowSeg,hpowOutside⟩
  have hpowerPrefix : Kept μ μp keyBase := by
    intro x hx
    exact hpowOutside x (Or.inl (by omega))
  have hcodesP : ∀ j<f.nb, μp (f.bank+j)=(address (E.word j) : ℤ) := by
    intro j hj
    rw [hpowerPrefix _ (by omega)]
    exact hcodes j hj
  have hsourceFp : ∀ k<groups, ∀ j<f.nb, μp (fsource+k*f.nb+j)=F k (E.word j) := by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb (show k+1≤groups by omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    rw [hpowerPrefix _ (by omega)]
    exact hsourceF k hk j hj
  have hsourceGp : ∀ k<groups, ∀ j<f.nb, μp (gsource+k*f.nb+j)=G k (E.word j) := by
    intro k hk j hj
    have hm := Nat.mul_le_mul_right f.nb (show k+1≤groups by omega)
    rw [Nat.add_mul,Nat.one_mul] at hm
    rw [hpowerPrefix _ (by omega)]
    exact hsourceG k hk j hj
  have hbank := (LightTernaryGroupedBanks.meets (d := d+1)
    E F G μp hw ha hfs hgs hmeta hpows hfg hgh hbankSpace
    hword hNword hgroupsWord hcodesP hsourceFp hsourceGp (powers_of_segment hpowSeg) hsorted hF hG
    hforwardWord hproductWord hinverseWord hL hn (by omega)).append tail
  light_call hbank using LightTernaryWantedRows.args,LightTernaryWantedRowDispatch.args,
    LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,LightTernaryNearPair.args,
    LightTernaryGroupedBanks.time,powTableTime with bankResult ν ⟨hFst,hGst,hHst,hkeep,hpowers'⟩
  have hprefix : Kept μ ν keyBase := by
    intro x hx
    exact (hkeep x (Or.inl hx) (Or.inl (by omega)) (Or.inl (by omega)) (Or.inl (by omega))).trans (hpowerPrefix x hx)
  have hcodes' : ∀ j<f.nb, ν (f.bank+j)=(address (E.word j) : ℤ) := by
    intro j hj
    rw [hprefix _ (by omega)]
    exact hcodes j hj
  have hsnapshot : ∀ j<count, Snapshot lim out (hbase+group j*((N+1)*f.nb)) caps
      (sourceConfig f fbase ((N+1)*f.nb) (N*f.nb) (group j))
      (sourceConfig g gbase ((N+1)*f.nb) (N*f.nb) (group j))
      ν (Q j) E (F (group j)) (G (group j)) := by
    intro j hj
    apply (hplan j hj).snapshot hcodes'
    · exact LightTernaryWantedQuery.source_bank_read E (F (group j)) ν (hFst (group j) (hgroup j hj))
    · exact LightTernaryWantedQuery.source_bank_read E (G (group j)) ν (hGst (group j) (hgroup j hj))
    · exact LightTernaryWantedQuery.assembled_inverse_bank E (F (group j)) (G (group j)) ν (hHst (group j) (hgroup j hj))
  have hrowsGroup : ∀ j<count, ν (records+3*j+2)=(group j : ℤ) := by
    intro j hj
    rw [hprefix _ (by omega)]
    exact hreadGroup j hj
  have hrowsQ : ∀ j<count, ν (records+3*j+1)=(address (Q j) : ℤ) := by
    intro j hj
    rw [hprefix _ (by omega)]
    exact hreadQ j hj
  have hrows := LightTernaryWantedRows.meets (P := program) (pMain := 49) (pRow := 48) (pPrepare := 47)
    (d := d+1) (bankValues := hbase) rows row prepared library f g Qstar Q group F G E ν hw
    (by omega) hdst hspace (by omega) hfg hgh hHdst (by ring) rfl
    hrowsGroup hrowsQ hgroup hRank (by omega) hcountWord hstrideWord htailWord hsnapshot htime (by omega)
  light_call hrows using LightTernaryWantedRows.args,LightTernaryWantedRowDispatch.args,
    LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,LightTernaryNearPair.args,
    LightTernaryGroupedBanks.time,LightTernaryWantedRows.time,powTableTime with result ξ ⟨hrowsKeep,hout⟩
  refine ⟨?_,hout⟩
  intro x hx
  exact (hrowsKeep x (by omega)).trans (hprefix x hx)


theorem time_bound (groups N L n count t : ℕ) :
    time groups N L n count t≤40000*(groups+1)*(N+1)*(N+L+1)*(n+1)+(count+1)*(t+1000) := by
  have hb := LightTernaryGroupedBanks.time_bound groups N L n
  have hp : 1≤(groups+1)*(N+L+1)*(n+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_right (N+1) hp
  unfold time LightTernaryWantedRows.time LightTernaryWantedRowDispatch.time powTableTime
  nlinarith only [hb,hs]

/-- The actual output array is the factorial-scaled original additive count
when source histograms use their proved factorial weighting. -/
theorem weighted_count_spec {lim : Limits} {P : Program}
    {N a b pMain d t count dst keep : ℕ} (argv : List ℤ) (μ : ℕ→ℤ)
    (f g : ℕ→TritWord N→ℤ) (group : ℕ→ℕ) (Q : ℕ→TritWord N)
    (hf : ∀ j<count, ∀ A, f (group j) A≠0 → rank A=a)
    (hg : ∀ j<count, ∀ B, g (group j) B≠0 → rank B=b)
    (hQ : ∀ j<count, rank (Q j)=a+b)
    (h : Meets lim P pMain d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=LightTernaryWantedRows.score
        (fun k A => ThreeSum.TernaryConvolution.factorial A*f k A)
        (fun k B => ThreeSum.TernaryConvolution.factorial B*g k B) group Q j)) :
    Meets lim P pMain d argv μ t (fun _ ν => Kept μ ν keep ∧ ∀ j<count,
      ν (dst+j)=ThreeSum.TernaryConvolution.factorial (Q j)*
        ThreeSum.TernaryConvolution.convolution (f (group j)) (g (group j)) (Q j)) := by
  apply h.mono le_rfl
  intro r ν hv
  refine ⟨hv.1,?_⟩
  intro j hj
  rw [hv.2 j hj]
  exact LightTernaryFrozenQuery.stageValue_count (f (group j)) (g (group j)) (hf j hj) (hg j hj) (Q j) (hQ j hj)

end ThreeSum.LightTernaryCountFrontend
