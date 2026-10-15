import Submission.ThreeSum.LightTernaryBankResources

/-! Actual source-group stage-0 copies followed by the closed bank assembler. -/
namespace ThreeSum.LightTernaryGroupBankStep
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryFrozenQueryStages ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 5000000
variable {lim : Limits}

def body (pCopy : ℕ) : Stmt :=
  .call pCopy [v 6,v 8,v 2] 11 ;;
  .call pCopy [v 7,v 9,v 2] 11 ;;
  .call 0 [v 0,v 1,v 2,v 3,v 4,v 5,v 8,v 9,v 10] 11

def time (N L n : ℕ) : ℕ :=2*copyTime n+LightTernaryBankAssembly.time N L n+200

def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase ∨ fbase+(N+1)*n≤x) →
    (x<gbase ∨ gbase+(N+1)*n≤x) →
    (x<hbase ∨ hbase+(N+1)*n≤x) → μ' x=μ x

theorem meets {tail : Program} {pMain pCopy N T n a powers L keyBase fsource gsource fbase gbase hbase d V : ℕ}
    (hmain : (LightTernaryBankAssembly.program++tail)[pMain]?=some (body pCopy))
    (hcopy : (LightTernaryBankAssembly.program++tail)[pCopy]?=some copyBody)
    (E : Enumeration N T n) (F G : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hfs : fsource+n≤keyBase) (hgs : gsource+n≤keyBase)
    (hmeta : keyBase+4*n≤powers) (hpows : powers+(2*N+1)≤fbase)
    (hfg : fbase+(N+1)*n≤gbase) (hgh : gbase+(N+1)*n≤hbase)
    (hspace : hbase+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ j<n, μ (fsource+j)=F (E.word j))
    (hsourceG : ∀ j<n, μ (gsource+j)=G (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hG : ∀ R, |G R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (LightTernaryBankAssembly.valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*LightTernaryBankAssembly.valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+7≤lim.depth) :
    Meets lim (LightTernaryBankAssembly.program++tail) pMain d
      [N,a,n,powers,L,keyBase,fsource,gsource,fbase,gbase,hbase] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) fbase N μ' ∧
        Stages E (fun s => forwardStage s G) gbase N μ' ∧
        Stages E (fun s => stageValue s (LightTernaryBankAssembly.product F G)) hbase N μ' ∧
        Preserved μ μ' keyBase n fbase gbase hbase N ∧ Powers μ' powers (2*N)) := by
  have hstep : (N+1)*n=N*n+n := by ring
  have hfn : fbase+n≤gbase := by omega
  have hgn : gbase+n≤hbase := by omega
  have hhn : hbase+n≤lim.space := by omega
  apply Meets.of_body hmain
  unfold body time
  have hcf := copy_meets (d := d+1) (μ := μ) (src := fsource) (dst := fbase) (n := n)
    hcopy hw (by omega) (by omega) (Or.inl (by omega))
  light_call hcf using copyTime with rf μf ⟨houtF,hkeepF⟩
  have hcg := copy_meets (d := d+1) (μ := μf) (src := gsource) (dst := gbase) (n := n)
    hcopy hw (by omega) (by omega) (Or.inl (by omega))
  light_call hcg using copyTime with rg μg ⟨houtG,hkeepG⟩
  have hcodesG : ∀ j<n, μg (a+j)=(address (E.word j) : ℤ) := by
    intro j hj
    exact (hkeepG _ (Or.inl (by omega))).trans ((hkeepF _ (Or.inl (by omega))).trans (hcodes j hj))
  have hpowG : Powers μg powers (2*N) := by
    intro j hj
    exact (hkeepG _ (Or.inl (by omega))).trans ((hkeepF _ (Or.inl (by omega))).trans (hpowers j hj))
  have hsF : ∀ j<n, μg (fbase+j)=F (E.word j) := by
    intro j hj
    exact (hkeepG _ (Or.inl (by omega))).trans ((houtF j hj).trans (hsourceF j hj))
  have hsG : ∀ j<n, μg (gbase+j)=G (E.word j) := by
    intro j hj
    exact (houtG j hj).trans ((hkeepF _ (Or.inl (by omega))).trans (hsourceG j hj))
  have hc := (LightTernaryBankAssembly.meets (d := d+1)
    E F G μg hw ha hmeta hpows hfg hgh hspace hword hNword hcodesG hsF hsG hpowG hsorted
    hF hG hforwardWord hproductWord hinverseWord hL hn (by omega)).append tail
  light_call hc using LightTernaryBankAssembly.time,copyTime with r μ' ⟨hF',hG',hH',hkeep,hpow⟩
  refine ⟨hF',hG',hH',?_,hpow⟩
  intro x hm hf hg hh
  have hf' : x<fbase+n ∨ fbase+(N+1)*n≤x := by omega
  have hg' : x<gbase+n ∨ gbase+(N+1)*n≤x := by omega
  have hfc : x<fbase ∨ fbase+n≤x := by omega
  have hgc : x<gbase ∨ gbase+n≤x := by omega
  exact (hkeep x hm hf' hg' hh).trans ((hkeepG x hgc).trans (hkeepF x hfc))

def program : Program :=LightTernaryBankAssembly.program++[body 18,copyBody]

theorem program_length : program.length=19 := by rfl

end ThreeSum.LightTernaryGroupBankStep
