import Submission.ThreeSum.TernaryPrefixHeaderSegment
import Submission.ThreeSum.TernaryPrefixSetupResources

noncomputable section
namespace ThreeSum.LightTernaryPrefixPrepare
open Light LightTernaryPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

def seedChanged (μ : ℕ→ℤ) (seed power header s : ℕ) : ℕ→ℤ :=
  Function.update (Function.update (Function.update (Function.update μ (seed+4) power)
    (seed+6) power) (seed+24) header) (seed+39) s

def time (m j alpha2 : ℕ) : ℕ :=
  LightTernaryPrefixSetup.allocateTime m (j+1)+LightTernaryPrefixHeader.time (j+1) alpha2+1250

def headerLoc (m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase : ℕ)
    (ret : ℤ) : ℕ→ℤ :=
  frame (LightTernaryPrefixHeader.args template liveHeader
    (LightTernaryPrefixSetup.headerAt prefixFree m (j+1)) (j+1) m p power alpha2 alphaRank localQ radix J++
    LightTernaryPrefixHeader.locals (LightTernaryPrefixSetup.N m (j+1))
      (LightTernaryPrefixSetup.T m (j+1)) (2*LightTernaryPrefixSetup.N m (j+1))
      (F^(j+1)) (LightTernaryPrefixSetup.nb m (j+1)) prefixFree
      (LightTernaryPrefixSetup.workAt prefixFree m (j+1)) (j+1) p power alpha2 alphaRank localQ radix Fbase Gbase++[ret])

def HeaderReceipt (μ ν : ℕ→ℤ)
    (m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase : ℕ) : Prop :=
  ∃ μcopy ret, (∀i<106, μcopy (liveHeader+i)=μ (template+i)) ∧ SameOutside μ μcopy liveHeader 106 ∧
    ν=Function.update (LightTernaryPrefixHeader.patch liveHeader
      (headerLoc m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase ret)
      μcopy headerWrites) (liveHeader+104) 0

/-- This is a genuine execution certificate for the preparation prefix of
entry180: all bank enumeration, header construction, and budget arithmetic
execute. The inputs contain ordinary memory and arithmetic guards only. -/
theorem meets {lim : Limits} {P : Program}
    {main m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scale j power
      Fbase Gbase xB xC xP tB tC tP d : ℕ}
    (hmain : P[main]?=some prepareBody)
    (hpAllocate : P[172]?=some (LightTernaryPrefixSetup.allocateBody 168 167))
    (hpPrefix : P[167]?=some (LightTernaryPrefixSetup.body 168 169))
    (hpPower : P[168]?=some LightNatPower.body)
    (hpSetup : P[169]?=some (LightTernaryEnumerationSetup.body 170 171))
    (hpPowers : P[170]?=some powTableBody)
    (hpEnum : P[171]?=some (LightTernaryEnumeration.body 171))
    (hpHeader : P[179]?=some headerBody) (hpCopy : P[177]?=some copyBody)
    (hpRepeat : P[178]?=some LightTernaryRepeatWord.body)
    (hpBudget : P[183]?=some LightTernaryBudgetStep.body)
    (μ : ℕ→ℤ) (hw : (lim.space:ℤ)≤lim.word)
    (hprefixSpace : LightTernaryPrefixSetup.endAt prefixFree m (j+1)≤lim.space)
    (hprefixWord : (LightTernaryPrefixSetup.word m (j+1) F:ℤ)≤lim.word)
    (hdepth : d+LightTernaryPrefixSetup.N m (j+1)+5≤lim.depth)
    (hj : ((j+1:ℕ):ℤ)≤lim.word)
    (htemplate : template+106≤liveHeader) (hheader : liveHeader+106≤liveSeed)
    (hseed : liveSeed+48≤prefixFree)
    (hF : μ (template+99)=(Fbase:ℤ)) (hG : μ (template+100)=(Gbase:ℤ))
    (hD : LightTernaryPrefixSetup.T m (j+1)+1≤2*(alphaRank*(j+1)))
    (hN1 : (LightTernaryPrefixSetup.N m (j+1):ℤ)+1≤lim.word)
    (hfits : ∀x∈(LightTernaryPrefixHeader.args template liveHeader
      (LightTernaryPrefixSetup.headerAt prefixFree m (j+1)) (j+1) m p power alpha2 alphaRank localQ radix J++
      LightTernaryPrefixHeader.locals (LightTernaryPrefixSetup.N m (j+1))
        (LightTernaryPrefixSetup.T m (j+1)) (2*LightTernaryPrefixSetup.N m (j+1))
        (F^(j+1)) (LightTernaryPrefixSetup.nb m (j+1)) prefixFree
        (LightTernaryPrefixSetup.workAt prefixFree m (j+1)) (j+1) p power alpha2 alphaRank localQ radix Fbase Gbase),
      |x|≤lim.word)
    (hpower : ∀i≤alpha2*(j+1), ((2^i:ℕ):ℤ)≤lim.word)
    (hquery : ∀i≤j+1, (LightTernaryRepeatWord.value localQ radix i:ℤ)≤lim.word)
    (hbudget : Seg μ (liveSeed+41) (LightTernaryBudgetStep.oldValues xB xC xP tB tC tP))
    (hnext : ∀x∈LightTernaryBudgetStep.nextValues p a b scale xB xC xP tB tC tP, x≤lim.word)
    (hmid : ((tP*b:ℕ):ℤ)≤lim.word) (h9 : (9:ℤ)≤lim.word) :
    Meets lim P main d (stepArgs m F p liveSeed template liveHeader prefixFree alpha2 alphaRank localQ radix J a b scale j power)
      μ (time m j alpha2)
      (fun r ν=>r=((power*p:ℕ):ℤ) ∧ ∃ μ₁ μ₂,
        Seg μ₁ (LightTernaryPrefixSetup.headerAt prefixFree m (j+1))
          (LightTernaryPrefixSetup.header m (j+1) F prefixFree (LightTernaryPrefixSetup.workAt prefixFree m (j+1))) ∧
        Seg μ₁ prefixFree ((TernaryAddresses.codes (LightTernaryPrefixSetup.N m (j+1))
          (LightTernaryPrefixSetup.T m (j+1))).map (fun (c:ℕ)=>(c:ℤ))) ∧
        LightSubsetAddress.Powers μ₁ (LightTernaryPrefixSetup.workAt prefixFree m (j+1))
          (2*LightTernaryPrefixSetup.N m (j+1)) ∧ Kept μ μ₁ prefixFree ∧
        HeaderReceipt μ₁ μ₂ m F p template liveHeader prefixFree alpha2 alphaRank localQ radix J j power Fbase Gbase ∧
        SameOutside μ₁ μ₂ liveHeader 106 ∧
        ν=LightTernaryBudgetStep.changed (seedChanged μ₂ liveSeed power liveHeader (j+1))
          (liveSeed+41) p a b scale xB xC xP tB tC tP) :=by
  have hprefixEnd : prefixFree≤lim.space :=by
    have hh:=hprefixSpace
    unfold LightTernaryPrefixSetup.endAt LightTernaryPrefixSetup.headerAt LightTernaryPrefixSetup.workAt at hh
    generalize 4^(LightTernaryPrefixSetup.N m (j+1))=mask at hh
    omega
  have hseedWord : (liveSeed:ℤ)+48≤lim.word :=(by exact_mod_cast (show liveSeed+48≤lim.space by omega) : (liveSeed:ℤ)+48≤(lim.space:ℤ)).trans hw
  have hpowerWord : (power:ℤ)≤lim.word :=by
    have hh:=hfits (power:ℤ) (by simp [LightTernaryPrefixHeader.args])
    exact (le_abs_self _).trans hh
  have hd : d<lim.depth :=by omega
  have hcPrefix:=LightTernaryPrefixSetup.allocate_meets (d:=d+1)
    hpAllocate hpPower hpPrefix hpSetup hpPowers hpEnum μ hw hprefixSpace hprefixWord (by omega)
  apply Meets.of_body hmain
  unfold prepareBody time
  light_set (j+1:ℕ) using stepArgs,LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
  light_call hcPrefix using stepArgs,LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
    with hdr μ₁ ⟨hHdr,hHeader,hCodes,hPowers,hKeep⟩
  have hF₁ : μ₁ (template+99)=(Fbase:ℤ) :=(hKeep _ (by omega)).trans hF
  have hG₁ : μ₁ (template+100)=(Gbase:ℤ) :=(hKeep _ (by omega)).trans hG
  have hHdrSpace : LightTernaryPrefixSetup.headerAt prefixFree m (j+1)+8≤lim.space :=hprefixSpace
  have hAfterSeed : liveHeader+106≤LightTernaryPrefixSetup.headerAt prefixFree m (j+1) :=by
    have hh : prefixFree≤LightTernaryPrefixSetup.headerAt prefixFree m (j+1) :=by
      unfold LightTernaryPrefixSetup.headerAt LightTernaryPrefixSetup.workAt
      generalize 4^(LightTernaryPrefixSetup.N m (j+1))=mask
      omega
    omega
  have hcHeader:=LightTernaryPrefixHeader.meets (d:=d+1) hpHeader hpCopy hpPower hpRepeat μ₁ hw
    htemplate hAfterSeed hHdrSpace (by omega) hHeader hF₁ hG₁ hD hN1 hfits hpower hquery
  light_call hcHeader using stepArgs,LightTernaryPrefixHeader.args,hHdr,
    LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
    with newPower μ₂ ⟨hNewPower,μcopy,copyRet,hCopied,hCopyKeep,hμ₂⟩
  have hOutside : SameOutside μ₁ μ₂ liveHeader 106 :=by
    subst μ₂
    intro x hx
    rw [Function.update_of_ne (by omega)]
    rw [LightTernaryPrefixHeader.patch_outside _ _ _ _ (fun ir hir=>(LightTernaryPrefixHeader.headerWrites_good ir hir).1) x hx]
    exact hCopyKeep x hx
  light_store (liveSeed+4) power using stepArgs,LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
  light_store (liveSeed+6) power using stepArgs,LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
  light_store (liveSeed+24) liveHeader using stepArgs,LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
  light_store (liveSeed+39) (j+1:ℕ) using stepArgs,LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
  have hBudgetRead : Seg (seedChanged μ₂ liveSeed power liveHeader (j+1)) (liveSeed+41)
      (LightTernaryBudgetStep.oldValues xB xC xP tB tC tP) :=by
    intro i hi
    have hii : i<6 :=by simpa [LightTernaryBudgetStep.oldValues] using hi
    simp only [seedChanged]
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      hOutside _ (Or.inr (by omega)),hKeep _ (by omega)]
    exact hbudget i hi
  have hcBudget:=LightTernaryBudgetStep.meets (d:=d+1) hpBudget
    (seedChanged μ₂ liveSeed power liveHeader (j+1)) hw h9 (by omega) hBudgetRead hnext hmid
  light_call hcBudget using stepArgs,seedChanged,LightTernaryPrefixSetup.allocateTime,
    LightTernaryPrefixHeader.time with budgetRet ν ⟨hBudgetRet,hν⟩
  have hResultWord : ((power*p:ℕ):ℤ)≤lim.word :=by
    have hh:=hfits ((power*p:ℕ):ℤ) (by simp [LightTernaryPrefixHeader.locals])
    exact (le_abs_self _).trans hh
  light_set (power*p:ℕ) using stepArgs,hNewPower,LightTernaryPrefixSetup.allocateTime,LightTernaryPrefixHeader.time
  exact ⟨rfl,μ₁,μ₂,hHeader,hCodes,hPowers,hKeep,
    ⟨μcopy,copyRet,hCopied,hCopyKeep,hμ₂⟩,hOutside,hν⟩

end ThreeSum.LightTernaryPrefixPrepare
