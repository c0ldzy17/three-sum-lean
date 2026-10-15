import Submission.ThreeSum.LightTernaryBankStages
import Submission.ThreeSum.LightTernaryProduct

/-! A closed seventeen-procedure program constructs both forward source banks,
their point product, and every partial inverse product bank. -/
namespace ThreeSum.LightTernaryBankAssembly
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery ThreeSum.TernaryFrozenQueryStages
open ThreeSum.LightTernaryBankSweep
set_option maxHeartbeats 6000000
variable {lim : Limits}

def body : Stmt :=
  .call 1 [v 0,v 1,v 2,v 3,v 4,v 5,v 6] 9 ;;
  .call 1 [v 0,v 1,v 2,v 3,v 4,v 5,v 7] 9 ;;
  .call 16 [v 6 +' v 0 *' v 2,v 7 +' v 0 *' v 2,v 8,v 2] 9 ;;
  .call 11 [v 0,v 1,v 2,v 3,v 4,v 5,v 8] 9

def program : Program := [body,
  LightTernaryBankSweep.body 2,
  LightTernaryBankCoordinate.body 3 7,
  LightTernaryMetadata.body 4 5 6,
  LightTernaryCodes.zeroBody 6,
  LightTernaryCodes.digitBody 6,
  LightMaskErase.body 6,
  LightTernaryPass.body 8,
  LightTernaryLookup.body 9 10,
  LightBandLookup.searchBody 9,
  LightTernaryCell.zetaBody,
  LightTernaryBankSweep.body 12,
  LightTernaryBankCoordinate.body 3 13,
  LightTernaryInversePass.body 14,
  LightTernaryLookup.body 9 15,
  LightTernaryCell.inverseBody,
  LightTernaryProduct.body]

@[simp] theorem program_length : program.length=17 := rfl

def product {N : ℕ} (F G : TritWord N→ℤ) (R : TritWord N) : ℤ :=
  forwardStage N F R*forwardStage N G R

def valueBound (N V : ℕ) : ℕ :=(4^N*V)*(4^N*V)

theorem product_abs {N : ℕ} (F G : TritWord N→ℤ) (V : ℕ)
    (hF : ∀ R, |F R|≤(V : ℤ)) (hG : ∀ R, |G R|≤(V : ℤ)) (R : TritWord N) :
    |product F G R|≤(valueBound N V : ℤ) := by
  rw [product,abs_mul]
  have h1 := LightTernaryBankStages.forward_bound N le_rfl F V hF R
  have h2 := LightTernaryBankStages.forward_bound N le_rfl G V hG R
  simpa [valueBound,Nat.cast_mul] using mul_le_mul h1 h2 (abs_nonneg _) (by positivity)

def time (N L n : ℕ) : ℕ :=3*LightTernaryBankSweep.time N L n+LightTernaryProduct.time n+300

def Preserved (μ μ' : ℕ→ℤ) (keyBase n fbase gbase hbase N : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) →
    (x<fbase+n ∨ fbase+(N+1)*n≤x) →
    (x<gbase+n ∨ gbase+(N+1)*n≤x) →
    (x<hbase ∨ hbase+(N+1)*n≤x) → μ' x=μ x

theorem meets {N T n a powers L keyBase fbase gbase hbase d V : ℕ}
    (E : Enumeration N T n) (F G : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤fbase)
    (hfg : fbase+(N+1)*n≤gbase) (hgh : gbase+(N+1)*n≤hbase)
    (hspace : hbase+(N+1)*n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsourceF : ∀ j<n, μ (fbase+j)=F (E.word j))
    (hsourceG : ∀ j<n, μ (gbase+j)=G (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ R, |F R|≤(V : ℤ)) (hG : ∀ R, |G R|≤(V : ℤ))
    (hforwardWord : 4*((4^N*V : ℕ) : ℤ)+3≤lim.word)
    (hproductWord : (valueBound N V : ℤ)≤lim.word)
    (hinverseWord : 4*((4^N*valueBound N V : ℕ) : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+6≤lim.depth) :
    Meets lim program 0 d [N,a,n,powers,L,keyBase,fbase,gbase,hbase] μ (time N L n)
      (fun _ μ' => Stages E (fun s => forwardStage s F) fbase N μ' ∧
        Stages E (fun s => forwardStage s G) gbase N μ' ∧
        Stages E (fun s => stageValue s (product F G)) hbase N μ' ∧
        Preserved μ μ' keyBase n fbase gbase hbase N ∧ Powers μ' powers (2*N)) := by
  have hstageLength : (N+1)*n=N*n+n := by ring
  have hfg' : fbase+N*n+n≤gbase := by nlinarith only [hfg]
  have hgh' : gbase+N*n+n≤hbase := by nlinarith only [hgh]
  have hspace' : hbase+N*n+n≤lim.space := by nlinarith only [hspace]
  have hfn : fbase+n≤gbase := by omega
  have hgn : gbase+n≤hbase := by omega
  have hhn : hbase+n≤lim.space := by omega
  have hcf := LightTernaryBankStages.zeta_meets (P := program) (pMain := 1) (pCoord := 2)
    (pMeta := 3) (pZero := 4) (pDigit := 5) (pErase := 6) (pPass := 7)
    (pCell := 8) (pSearch := 9) (pValue := 10) (d := d+1)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E F μ hw ha hmeta hpows (by omega) hword hNword hcodes hsourceF hpowers hsorted
    hF hforwardWord hL hn (by omega)
  apply Meets.of_body (show program[0]?=some body from rfl)
  unfold body time
  light_call hcf using LightTernaryBankSweep.time with rf μf ⟨hstF,hkeepF,hpowF⟩
  have hcodesF : ∀ j<n, μf (a+j)=(address (E.word j) : ℤ) := by
    intro j hj
    exact (hkeepF _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodes j hj)
  have hsourceGf : ∀ j<n, μf (gbase+j)=G (E.word j) := by
    intro j hj
    exact (hkeepF _ (Or.inr (by omega)) (Or.inr (by omega))).trans (hsourceG j hj)
  have hcg := LightTernaryBankStages.zeta_meets (P := program) (pMain := 1) (pCoord := 2)
    (pMeta := 3) (pZero := 4) (pDigit := 5) (pErase := 6) (pPass := 7)
    (pCell := 8) (pSearch := 9) (pValue := 10) (d := d+1)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E G μf hw ha hmeta (by omega) (by omega) hword hNword hcodesF hsourceGf hpowF hsorted
    hG hforwardWord hL hn (by omega)
  light_call hcg using LightTernaryBankSweep.time with rg μg ⟨hstG,hkeepG,hpowG⟩
  have hstFg : Stages E (fun s => forwardStage s F) fbase N μg := by
    intro s hs j hj
    have hm := Nat.mul_le_mul_right n hs
    exact (hkeepG _ (Or.inr (by omega)) (Or.inl (by omega))).trans (hstF s hs j hj)
  have hcp := LightTernaryProduct.meets (P := program) (p := 16) (d := d+1)
    (a := fbase+N*n) (b := gbase+N*n) (dst := hbase) (n := n)
    (U := 4^N*V) (V := 4^N*V) rfl μg hw
    (by omega) (by omega) hhn
    (Or.inr (Or.inl (by omega))) (Or.inr (Or.inl (by omega)))
    (fun j hj => by rw [hstFg N le_rfl j hj]; exact LightTernaryBankStages.forward_bound N le_rfl F V hF _)
    (fun j hj => by rw [hstG N le_rfl j hj]; exact LightTernaryBankStages.forward_bound N le_rfl G V hG _)
    (by simpa [valueBound,Nat.cast_mul] using hproductWord)
  have hnm : ((N : ℤ)*(n : ℤ))≤lim.word := by
    have : N*n≤lim.space := by omega
    exact (by exact_mod_cast this : (N : ℤ)*(n : ℤ)≤(lim.space : ℤ)).trans hw
  have hfaddr : (fbase : ℤ)+(N : ℤ)*(n : ℤ)≤lim.word := by
    have : fbase+N*n≤lim.space := by omega
    exact (by exact_mod_cast this : (fbase : ℤ)+(N : ℤ)*(n : ℤ)≤(lim.space : ℤ)).trans hw
  have hgaddr : (gbase : ℤ)+(N : ℤ)*(n : ℤ)≤lim.word := by
    have : gbase+N*n≤lim.space := by omega
    exact (by exact_mod_cast this : (gbase : ℤ)+(N : ℤ)*(n : ℤ)≤(lim.space : ℤ)).trans hw
  light_call hcp using LightTernaryProduct.time with rp μp ⟨hstP,hkeepP⟩
  have hcodesP : ∀ j<n, μp (a+j)=(address (E.word j) : ℤ) := by
    intro j hj
    exact (hkeepP _ (Or.inl (by omega))).trans
      ((hkeepG _ (Or.inl (by omega)) (Or.inl (by omega))).trans (hcodesF j hj))
  have hpowP : Powers μp powers (2*N) := by
    intro j hj
    exact (hkeepP _ (Or.inl (by omega))).trans (hpowG j hj)
  have hsourceH : ∀ j<n, μp (hbase+j)=product F G (E.word j) := by
    intro j hj
    rw [hstP j hj,hstFg N le_rfl j hj,hstG N le_rfl j hj]
    rfl
  have hci := LightTernaryBankStages.inverse_meets (P := program) (pMain := 11) (pCoord := 12)
    (pMeta := 3) (pZero := 4) (pDigit := 5) (pErase := 6) (pPass := 13)
    (pCell := 14) (pSearch := 9) (pValue := 15) (d := d+1)
    rfl rfl rfl rfl rfl rfl rfl rfl rfl rfl
    E (product F G) μp hw ha hmeta (by omega) hspace hword hNword hcodesP hsourceH hpowP hsorted
    (product_abs F G V hF hG) hinverseWord hL hn (by omega)
  light_call hci using LightTernaryBankSweep.time,LightTernaryProduct.time with ri μi ⟨hstH,hkeepI,hpowI⟩
  refine ⟨?_,?_,hstH,?_,hpowI⟩
  · intro s hs j hj
    have hm := Nat.mul_le_mul_right n hs
    exact (hkeepI _ (Or.inr (by omega)) (Or.inl (by omega))).trans
      ((hkeepP _ (Or.inl (by omega))).trans (hstFg s hs j hj))
  · intro s hs j hj
    have hm := Nat.mul_le_mul_right n hs
    exact (hkeepI _ (Or.inr (by omega)) (Or.inl (by omega))).trans
      ((hkeepP _ (Or.inl (by omega))).trans (hstG s hs j hj))
  · intro x hxMeta hxF hxG hxH
    have hxI : x<hbase+n ∨ hbase+(N+1)*n≤x := by rcases hxH with h|h; exact Or.inl (by omega); exact Or.inr h
    have hxP : x<hbase ∨ hbase+n≤x := by rcases hxH with h|h; exact Or.inl h; exact Or.inr (by omega)
    exact (hkeepI x hxMeta hxI).trans ((hkeepP x hxP).trans
      ((hkeepG x hxMeta hxG).trans (hkeepF x hxMeta hxF)))

end ThreeSum.LightTernaryBankAssembly
