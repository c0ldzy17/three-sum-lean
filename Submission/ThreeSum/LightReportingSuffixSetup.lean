import Submission.ThreeSum.LightReportingSuffixTable

/-!
# Complete suffix-local box preprocessing, including its own shift factor

The program constructs the mask-lifting power, fills every local compact leaf
through the original global source reads, and builds every local prefix-zeta
stage. Its exponentially sized domain is the residual width V.
-/

namespace ThreeSum.LightReportingSuffixSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits}

def coreBody (pTable pStages : ℕ) : Stmt :=
  .call pTable [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14] 15 ;;
  .call pStages [v 8,v 2,v 12,v 13,v 14] 0

def body (pPowers pCore : ℕ) : Stmt :=
  .call pPowers [v 14,v 9 +' k 1,k 2] 15 ;;
  .set 16 (M (v 14 +' v 9)) ;;
  .call pCore [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 16,v 10,v 11,v 12,v 13,v 14] 0

def program : Program := LightReportingSuffixTable.program ++ [coreBody 27 2,body 14 28]

def procs : LightSignedLeafCell.Procs program 6 10 where
  pUnion := 7
  pLookup := 8
  pSign := 19
  pSize := 9
  pSetup := 11
  pBuild := 12
  pFill := 13
  pRow := 15
  pLinear := 24
  pPowers := 14
  pRank := 16
  pOffset := 17
  pErase := 18
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl

def coreTime (W V cut : ℕ) : ℕ := LightReportingSuffixTable.time W V cut+LightBoxStages.time V cut+70
def time (W V cut offset : ℕ) : ℕ := powTableTime (offset+1)+coreTime W V cut+100

theorem core_meets {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(V+1)*downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim program 28 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,2^offset,baseL,baseR,boxBase,maskBase,work] μ (coreTime W V boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (leafWeight hfit f g stage preL preR) V ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((V+1)*downsetCap V boxCut)) := by
  have hV : V ≤ W := by omega
  have hcap : downsetCap V boxCut ≤ (V+1)*downsetCap V boxCut :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^stage*B)*(2^stage*D) ≤ 2^V*((2^stage*B)*(2^stage*D)) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    exact (by exact_mod_cast hh : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤
      ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ)).trans hvalueWord
  have hleafBound : ∀ S, S.card ≤ boxCut →
      |leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    intro S hS
    apply leafWeight_abs_le (sourceCut := sourceCut) hfit f g preL preR S hstage
    · have he := Finset.card_union_le preL (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreL)
    · have he := Finset.card_union_le preR (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreR)
    · exact hf
    · exact hg
  apply Meets.of_body (p := 28) (by rfl : program[28]? = some (coreBody 27 2))
  unfold coreBody coreTime
  have hl := LightReportingSuffixTable.meets (P := program) (pMain := 27)
    (pEnumSetup := 3) (pEnum := 20) (pBatch := 26) (pCell := 25) (d := d+1) (μ := μ)
    rfl procs rfl rfl rfl rfl hfit preL preR f g hw hcut hboxCut hstage
    (by omega) (by omega) (by omega) hmasks (Or.inl hdataL) (Or.inl hdataR)
    hspace hword hproductWord hpreL hpreR hf hg hstoredL hstoredR (by omega)
  light_call hl using LightReportingSuffixTable.time,LightBoxStages.time
    with leafRet μ₁ ⟨hleaves,hkeepLeaf⟩
  have hb := LightBoxStages.meets (P := program) (pMain := 2) (pSize := 9) (pPass := 21)
    (pEnumSetup := 3) (pEnum := 20) (pBatch := 22) (pCell := 23) (d := d+1) (μ := μ₁)
    rfl procs.size rfl rfl rfl rfl rfl procs.setup procs.offset procs.erase
    (leafWeight hfit f g stage preL preR) hw hboxCut hbox hmasks
    (LightReportingSuffixCell.small_space hV hspace) (LightReportingSuffixCell.small_word hV hword)
    hvalueWord hleaves hleafBound (by omega)
  light_call hb using LightReportingSuffixTable.time,LightBoxStages.time
    with boxRet μ₂ ⟨hboxes,hkeepBox⟩
  have hkept : KeptBut μ μ₂ maskBase boxBase ((V+1)*downsetCap V boxCut) := by
    intro i hi
    exact (hkeepBox i hi).trans (hkeepLeaf i ⟨hi.1,by omega⟩)
  refine ⟨hboxes,?_,?_,hkept⟩
  · apply LightSignedLeafBatch.storedThrough_of_on hstoredL
    intro i hi₀ hi₁
    exact hkept i ⟨by omega,Or.inl (by omega)⟩
  · apply LightSignedLeafBatch.storedThrough_of_on hstoredR
    intro i hi₀ hi₁
    exact hkept i ⟨by omega,Or.inl (by omega)⟩

theorem program_meets {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(V+1)*downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+11 ≤ lim.depth) :
    Meets lim program 29 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,offset,baseL,baseR,boxBase,maskBase,work] μ (time W V boxCut offset)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (leafWeight hfit f g stage preL preR) V ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((V+1)*downsetCap V boxCut)) := by
  have hpowWord (j : ℕ) (hj : j ≤ offset+1) : ((2^j : ℕ) : ℤ) ≤ lim.word := by
    have hm : 2^j ≤ (W+1)*2^(W+1) :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    exact (by exact_mod_cast hm : ((2^j : ℕ) : ℤ) ≤
      (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body (p := 29) (by rfl : program[29]? = some (body 14 28))
  unfold body time
  have hp := powTable_meets (P := program) (p := 14) (d := d+1) (μ := μ)
    (dst := work) (L := offset+1) (b := 2) rfl hw (by omega) hpowWord
  light_call hp using powTableTime,coreTime with powRet μ₁ ⟨hpowers,hkeepPowers⟩
  have hpower := powers_of_segment hpowers
  have hread : μ₁ (work+offset) = ((2^offset : ℕ) : ℤ) := hpower offset le_rfl
  have hreadInt : μ₁ (work+offset) = (2 : ℤ)^offset := by simpa using hread
  have hpWord := hpowWord offset (by omega)
  light_set (2^offset : ℕ) using hread,hreadInt,powTableTime,coreTime
  have hstoredL₁ := LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro i _ hi; exact hkeepPowers i (Or.inl (by omega)))
  have hstoredR₁ := LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro i _ hi; exact hkeepPowers i (Or.inl (by omega)))
  have hcore := core_meets (d := d+1) (μ := μ₁) hfit preL preR f g hw hcut hboxCut hstage
    hdataL hdataR hbox hmasks hspace hword hvalueWord hpreL hpreR hf hg hstoredL₁ hstoredR₁ (by omega)
  light_call hcore using powTableTime,coreTime with res μ₂ ⟨hboxes,hL,hR,hkeepCore⟩
  refine ⟨hboxes,hL,hR,?_⟩
  intro i hi
  exact (hkeepCore i hi).trans (hkeepPowers i (Or.inl (by omega)))

theorem coreTime_bound {W V cut : ℕ} (hV : V ≤ W) (hcut : cut ≤ V) :
    coreTime W V cut ≤ 19000*(W+1)^4*(downsetCap V cut+1) := by
  have hl := LightReportingSuffixTable.time_bound hV hcut
  have hb := LightBoxStages.time_bound hcut
  have hp : (W+1)^3 ≤ (W+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hv := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 4
  have hm := Nat.mul_le_mul_right (downsetCap V cut+1) (Nat.mul_le_mul_left 12000 hp)
  have hn := Nat.mul_le_mul_right (downsetCap V cut+1) (Nat.mul_le_mul_left 6000 hv)
  have hpos : 1 ≤ (W+1)^4*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold coreTime
  nlinarith

theorem time_bound {W V cut offset : ℕ} (hfit : offset+V ≤ W) (hcut : cut ≤ V) :
    time W V cut offset ≤ 20000*(W+1)^4*(downsetCap V cut+1) := by
  have hc := coreTime_bound (by omega : V ≤ W) hcut
  have hp : W+1 ≤ (W+1)^4 := by
    simpa using (Nat.pow_le_pow_right (by omega : 1 ≤ W+1) (by decide : 1 ≤ 4))
  have hm := Nat.le_mul_of_pos_right ((W+1)^4) (by omega : 0 < downsetCap V cut+1)
  unfold time powTableTime
  nlinarith

end ThreeSum.LightReportingSuffixSetup
