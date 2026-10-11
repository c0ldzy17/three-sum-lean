import Submission.ThreeSum.LightSignedLeafTable

/-!
# Complete compact box preprocessing from the two stored source transforms

The initial signed-product leaf table is computed by machine execution.
The program then constructs every compact prefix-zeta stage, yielding the
exact box-table contract consumed by the sparse query machine.
-/

namespace ThreeSum.LightSignedBoxSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- The arguments agree with the initial leaf-table builder. -/
def body (pLeafTable pBoxStages : ℕ) : Stmt :=
  .call pLeafTable [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 13 ;;
  .call pBoxStages [v 0,v 2,v 10,v 11,v 12] 0

def time (W cut : ℕ) : ℕ := LightSignedLeafTable.time W cut+LightBoxStages.time W cut+60

theorem meets
    {pMain pLeafTable pBoxStages pEnumSetup pEnum pLeafBatch pLeafCell pLeaf pAddress pZetaPass pZetaBatch pZetaCell : ℕ}
    (hmain : P[pMain]? = some (body pLeafTable pBoxStages))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    (hTable : P[pLeafTable]? = some (LightSignedLeafTable.body pEnumSetup pLeafBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body C.pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hLeafBatch : P[pLeafBatch]? = some (LightSignedLeafBatch.body pLeafCell))
    (hLeafCell : P[pLeafCell]? = some (LightSignedLeafCell.body pLeaf pAddress))
    (hBoxStages : P[pBoxStages]? = some (LightBoxStages.body C.pSize pZetaPass))
    (hZetaPass : P[pZetaPass]? = some (LightZetaPass.body pEnumSetup pZetaBatch))
    (hZetaBatch : P[pZetaBatch]? = some (LightZetaBatch.body pZetaCell))
    (hZetaCell : P[pZetaCell]? = some (LightZetaCell.body C.pSetup C.pOffset C.pErase C.pRank))
    {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(W+1)*downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap W boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,boxBase,maskBase,work] μ (time W boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (SignedLeaf.value f g stage preL preR) W ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((W+1)*downsetCap W boxCut)) := by
  have hcap : downsetCap W boxCut ≤ (W+1)*downsetCap W boxCut :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^stage*B)*(2^stage*D) ≤ 2^W*((2^stage*B)*(2^stage*D)) :=
      Nat.le_mul_of_pos_left _ (by positivity)
    exact (by exact_mod_cast hh : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤
      ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ)).trans hvalueWord
  have hleafBound : ∀ S, S.card ≤ boxCut →
      |SignedLeaf.value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    intro S hS
    apply SignedLeaf.abs_value_le (cut := sourceCut) f g stage preL preR S hstage
    · exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hS _).trans hpreL)
    · exact (Finset.card_union_le _ _).trans ((Nat.add_le_add_left hS _).trans hpreR)
    · exact hf
    · exact hg
  apply Meets.of_body hmain
  unfold body time
  have hl := LightSignedLeafTable.meets (d := d+1) (μ := μ)
    hTable C hEnumSetup hEnum hLeafBatch hLeafCell preL preR f g hw hcut hboxCut hstage
    (by omega) (by omega) (by omega) hmasks (Or.inl hdataL) (Or.inl hdataR)
    hspace hword hproductWord hpreL hpreR hf hg hstoredL hstoredR (by omega)
  light_call hl using LightSignedLeafTable.time,LightBoxStages.time
    with leafRet μ₁ ⟨hleaves,hkeepLeaf⟩
  have hb := LightBoxStages.meets (d := d+1) (μ := μ₁)
    hBoxStages C.size hZetaPass hEnumSetup hEnum hZetaBatch hZetaCell C.setup C.offset C.erase
    (SignedLeaf.value f g stage preL preR) hw hboxCut hbox hmasks (by omega) hword hvalueWord
    hleaves hleafBound (by omega)
  light_call hb using LightSignedLeafTable.time,LightBoxStages.time
    with boxRet μ₂ ⟨hboxes,hkeepBox⟩
  have hkept : KeptBut μ μ₂ maskBase boxBase ((W+1)*downsetCap W boxCut) := by
    intro i hi
    exact (hkeepBox i hi).trans (hkeepLeaf i ⟨hi.1,by omega⟩)
  refine ⟨hboxes,?_,?_,hkept⟩
  · apply LightSignedLeafBatch.storedThrough_of_on hstoredL
    intro i hi₀ hi₁
    exact hkept i ⟨by omega,Or.inl (by omega)⟩
  · apply LightSignedLeafBatch.storedThrough_of_on hstoredR
    intro i hi₀ hi₁
    exact hkept i ⟨by omega,Or.inl (by omega)⟩

def program : Program :=
  [body 1 2,LightSignedLeafTable.body 3 4,LightBoxStages.body 9 21,
    LightSubsetEnumerationSetup.body 14 20,LightSignedLeafBatch.body 5,
    LightSignedLeafCell.body 6 10,LightSignedLeafGeneral.body 7 8 19,LightMaskUnion.body 14 18,
    LightStageLookup.body 9 10,LightDownsetSize.body 11 17,LightDownsetAddress.body 11 17,
    LightSubsetSetup.body 12 14 16,buildBody 13 15,fillBody,powTableBody,rowBody 24,
    rankBody 16,LightSubsetOffset.body,LightMaskErase.body 18,LightSign.body,
    LightSubsetEnumeration.body 20,LightZetaPass.body 3 22,LightZetaBatch.body 23,
    LightZetaCell.body 11 17 18 16,LightArray.linearBody]

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

theorem program_meets     {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR boxBase maskBase work B D d : ℕ}
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ boxBase)
    (hbox : boxBase+(W+1)*downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap W boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^W*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim program 0 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,boxBase,maskBase,work] μ (time W boxCut)
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (SignedLeaf.value f g stage preL preR) W ∧
        LightZetaStages.StoredThrough μ' baseL sourceCut f W ∧
        LightZetaStages.StoredThrough μ' baseR sourceCut g W ∧
        KeptBut μ μ' maskBase boxBase ((W+1)*downsetCap W boxCut)) :=
  meets rfl procs rfl rfl rfl rfl rfl rfl rfl rfl rfl preL preR f g
    hw hcut hboxCut hstage hdataL hdataR hbox hmasks hspace hword hvalueWord
    hpreL hpreR hf hg hstoredL hstoredR hd

theorem time_bound {W cut : ℕ} (hcut : cut ≤ W) :
    time W cut ≤ 19000*(W+1)^4*(downsetCap W cut+1) := by
  have hl := LightSignedLeafTable.time_bound hcut
  have hb := LightBoxStages.time_bound hcut
  have hp : (W+1)^3 ≤ (W+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm := Nat.mul_le_mul_right (downsetCap W cut+1) (Nat.mul_le_mul_left 12000 hp)
  have hpos : 1 ≤ (W+1)^4*(downsetCap W cut+1) := by
    have hh : 0 < (W+1)^4*(downsetCap W cut+1) := by positivity
    omega
  unfold time
  nlinarith

end ThreeSum.LightSignedBoxSetup
