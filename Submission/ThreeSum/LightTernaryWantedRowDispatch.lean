import Submission.ThreeSum.LightTernaryPreparedWanted

/-! Physical map-group dispatch for one literal three-cell wanted row. -/
noncomputable section
namespace ThreeSum.LightTernaryWantedRowDispatch
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.TernaryBankStageModel
open ThreeSum.LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
variable {lim : Limits} {P : Program}

def sourceConfig (c : Config) (base stride tail group : ℕ) : Config :=
  {c with bv:=base+group*stride+tail}

def body (pPrepare : ℕ) : Stmt :=
  .set 46 (M (v 39 +' k 2)) ;;
  .set 47 (M (v 39 +' k 1)) ;;
  .call pPrepare [v 0,v 1,v 2,v 3,v 4,v 5,
    v 41 +' v 46 *' v 44 +' v 45,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16,
    v 17,v 18,v 19,v 20,v 21,v 22,v 42 +' v 46 *' v 44 +' v 45,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33,v 34,
    v 47,v 43 +' v 46 *' v 44,v 37,v 38] 48 ;;
  .store (v 40) (v 48)

def args {N : ℕ} (f g : Config) (Qstar : TritWord N)
    (out bankValues caps record dst fbase gbase hbase stride tail : ℕ) : List ℤ :=
  LightTernaryPreparedWanted.args out bankValues caps f g Qstar++
    [(record : ℤ),dst,fbase,gbase,hbase,stride,tail]

def time (t : ℕ) : ℕ :=t+500

/-- Dispatch executes a proved prepared-query call at the bank addresses read
from the actual row's map group, then stores its literal result. This lemma is
used with `LightTernaryPreparedWanted.meets` in the row-loop instantiation. -/
theorem meets {pMain pPrepare N out bankValues caps record dst fbase gbase hbase stride tail group d t : ℕ}
    (hmain : P[pMain]?=some (body pPrepare))
    (f g : Config) (Qstar Q : TritWord N) (μ : ℕ→ℤ) (value : ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hrecord : record+3≤lim.space) (hdst : dst<lim.space)
    (hreadGroup : μ (record+2)=(group : ℤ)) (hreadQ : μ (record+1)=(address Q : ℤ))
    (hgroupWord : (group : ℤ)≤lim.word) (hcodeWord : (address Q : ℤ)≤lim.word)
    (hstrideWord : (stride : ℤ)≤lim.word) (htailWord : (tail : ℤ)≤lim.word)
    (hmulWord : (group : ℤ)*(stride : ℤ)≤lim.word)
    (hfWord : (fbase : ℤ)+(group : ℤ)*(stride : ℤ)+(tail : ℤ)≤lim.word)
    (hgWord : (gbase : ℤ)+(group : ℤ)*(stride : ℤ)+(tail : ℤ)≤lim.word)
    (hhWord : (hbase : ℤ)+(group : ℤ)*(stride : ℤ)≤lim.word)
    (hD : LightTernaryPreparedWanted.D Q f.T=LightTernaryPreparedWanted.D Qstar f.T)
    (hvalue : |value|≤lim.word) (hd : d<lim.depth)
    (hquery : Meets lim P pPrepare (d+1)
      (LightTernaryPreparedWanted.args out (hbase+group*stride) caps
        (sourceConfig f fbase stride tail group) (sourceConfig g gbase stride tail group) Q)
      μ t (fun v ν => v=value ∧ Kept μ ν f.a)) :
    Meets lim P pMain d (args f g Qstar out bankValues caps record dst fbase gbase hbase stride tail)
      μ (time t) (fun _ ν => ∃ μ', Kept μ μ' f.a ∧ ν=Function.update μ' dst value) := by
  have ha2 : ((record : ℤ)+2).toNat=record+2 := by omega
  have ha1 : ((record : ℤ)+1).toNat=record+1 := by omega
  have hmulNonneg : 0≤(group : ℤ)*(stride : ℤ) := by positivity
  apply Meets.of_body hmain
  unfold body args time
  light_set group using LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,
    LightTernaryNearPair.args,ha2,hreadGroup
  light_set (address Q) using LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,
    LightTernaryNearPair.args,ha1,hreadQ
  light_call hquery using LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,
    LightTernaryNearPair.args,sourceConfig,hD with result ν ⟨hout,hkeep⟩
  light_store dst value using hout,LightTernaryPreparedWanted.args,LightTernaryWantedQuery.args,
    LightTernaryNearPair.args
  exact ⟨ν,hkeep,rfl⟩

end ThreeSum.LightTernaryWantedRowDispatch
