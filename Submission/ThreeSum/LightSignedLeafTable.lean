import Submission.ThreeSum.LightSignedLeafBatch
import Submission.ThreeSum.LightSubsetEnumerationSetup

/-!
# Constructing the compact initial signed-product table

This program enumerates each stored cardinality layer, evaluates every
leaf through actual source-stage reads, and writes its exact compact
address. It allocates a downset-sized mask buffer and polynomial scratch.
-/

namespace ThreeSum.LightSignedLeafTable

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def enumBudget (W cut : ℕ) : ℕ := 800*(W+1)*(downsetCap W cut+1)
def batchBudget (W cut : ℕ) : ℕ := 9400*(W+1)^2*(downsetCap W cut+1)
def roundBudget (W cut : ℕ) : ℕ := enumBudget W cut+batchBudget W cut+80

def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  .call pEnumSetup [v 0,v 13,v 11,v 12] 14 ;;
  .call pBatch [v 0,v 1,v 3,v 4,v 5,v 6,v 7,v 13,v 14,v 11,v 8,v 9,v 10,v 12] 15

/-- Width, source and box cutoffs, suffix stage, two prefix cardinalities and
masks, source bases, destination, mask buffer, polynomial scratch. -/
def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 13 (v 2 +' k 1) (roundBody pEnumSetup pBatch)

def time (W cut : ℕ) : ℕ := (cut+1)*(roundBudget W cut+20)+20

def stageValues {W : ℕ} (μ : ℕ → ℤ) (dst j : ℕ)
    (weight : Finset (Fin W) → ℤ) (S : Finset (Fin W)) : ℤ :=
  if S.card < j then weight S else μ (dst+subsetRank S)

def Inv {W : ℕ} (μ : ℕ → ℤ) (sourceCut boxCut stage baseL baseR dst maskBase work : ℕ)
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      baseL,baseR,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap W boxCut) ∧
    TableAt μ' dst boxCut (stageValues μ dst j (SignedLeaf.value f g stage preL preR))

theorem meets {pMain pEnumSetup pEnum pBatch pCell pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pEnumSetup pBatch))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body C.pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightSignedLeafBatch.body pCell))
    (hCell : P[pCell]? = some (LightSignedLeafCell.body pLeaf pAddress))
    {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR dst maskBase work B D d : ℕ}
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdst : dst+downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap W boxCut ≤ work)
    (hsepL : Apart baseL ((W+1)*downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hsepR : Apart baseR ((W+1)*downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+9 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,dst,maskBase,work] μ (time W boxCut)
      (fun _ μ' => TableAt μ' dst boxCut (SignedLeaf.value f g stage preL preR) ∧
        KeptBut μ μ' maskBase dst (downsetCap W boxCut)) := by
  have hword₀ : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(W+1) : ℕ) ≤ (W+1)*2^(W+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(W+1) : ℕ) : ℤ) ≤
      (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ sourceCut boxCut stage baseL baseR dst maskBase work preL preR f g)
    (boxCut+1) (roundBudget W boxCut) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(W : ℤ),sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,dst,maskBase,work,0] =
        frame ([(W : ℤ),sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
          baseL,baseR,dst,maskBase,work,0] ++ [0,0])
      exact (frame_append_zeros _ 2).symm
    · intro S hS
      simp [stageValues]
  case round =>
    rintro j _ hj _ ⟨n,r,μ',rfl,hkept,hout⟩
    have hjcut : j ≤ boxCut := by omega
    have hchoose := LightZetaPass.choose_le_cap hboxCut hjcut
    have hsourceL : LightZetaStages.StoredThrough μ' baseL sourceCut f W :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL (by
        intro i hi₀ hi₁
        exact hkept i ⟨by omega,by omega⟩)
    have hsourceR : LightZetaStages.StoredThrough μ' baseR sourceCut g W :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR (by
        intro i hi₀ hi₁
        exact hkept i ⟨by omega,by omega⟩)
    have hen := LightSubsetEnumerationSetup.meets (d := d+1) hEnumSetup C.setup.powers hEnum
      (μ := μ') (L := W) (k := j) (dst := maskBase) (work := work)
      hw (by omega) hword₀ (by omega) (by omega) (by omega)
    have hentime : LightSubsetEnumerationSetup.time W j ≤ enumBudget W boxCut :=
      (LightSubsetEnumerationSetup.time_bound W j).trans
        (Nat.mul_le_mul_left (800*(W+1)) (Nat.succ_le_succ hchoose))
    unfold roundBody roundBudget
    light_call (hen.mono_time hentime) using enumBudget,batchBudget
      with count μ₁ ⟨hcount,hseg,hpowers,henkept⟩
    have hsourceL₁ : LightZetaStages.StoredThrough μ₁ baseL sourceCut f W :=
      LightSignedLeafBatch.storedThrough_of_on hsourceL (by
        intro i hi₀ hi₁
        exact henkept i ⟨by omega,Or.inl (by omega)⟩)
    have hsourceR₁ : LightZetaStages.StoredThrough μ₁ baseR sourceCut g W :=
      LightSignedLeafBatch.storedThrough_of_on hsourceR (by
        intro i hi₀ hi₁
        exact henkept i ⟨by omega,Or.inl (by omega)⟩)
    have hb := LightSignedLeafBatch.meets (d := d+1) hBatch hCell C
      (enumerateLayer W j) preL preR f g hw hcut hstage (by omega) (by omega) (by omega)
      (by rw [enumerateLayer_length]; omega) hsepL hsepR (Or.inr hdst)
      hspace hword hproductWord hpreL hpreR hf hg hsourceL₁ hsourceR₁ hseg
      (fun m hm => (mem_enumerateLayer W j m).mp hm) hjcut (by omega)
    have hbtime : LightSignedLeafBatch.time W (enumerateLayer W j).length ≤ batchBudget W boxCut := by
      rw [enumerateLayer_length]
      exact (LightSignedLeafBatch.time_bound W (W.choose j)).trans
        (Nat.mul_le_mul_left (9400*(W+1)^2) (Nat.succ_le_succ hchoose))
    light_call (hb.mono_time hbtime) using hcount,enumerateLayer_length,enumBudget,batchBudget
      with res μ₂ ⟨hnew,hbkept⟩
    refine ⟨by simp,count,res,μ₂,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hbkept i ⟨by omega,hi.2⟩).trans
        ((henkept i ⟨by omega,Or.inl hi.1⟩).trans (hkept i hi))
    · intro T hT
      have hr := subsetRank_lt hT
      have hn := hnew T hT
      rw [LightSignedLeafBatch.values_layer] at hn
      have hbefore : μ₁ (dst+subsetRank T) = μ' (dst+subsetRank T) :=
        henkept _ ⟨by omega,Or.inl (by omega)⟩
      by_cases heq : T.card = j
      · have hlt : T.card < j+1 := by omega
        simpa only [stageValues,heq,ite_true,show j < j+1 by omega] using hn
      · rw [if_neg heq,hbefore,hout T hT] at hn
        have hlt : T.card < j+1 ↔ T.card < j := by omega
        simpa only [stageValues,hlt] using hn
  case done =>
    rintro _ _ ⟨n,r,μ',rfl,hkept,hout⟩
    refine ⟨?_,hkept⟩
    intro T hT
    simpa only [stageValues,show T.card < boxCut+1 by omega,ite_true] using hout T hT
  case bound =>
    rintro j _ hj _ ⟨n,r,μ',rfl,_,_⟩
    light_side

def program : Program :=
  [body 1 2,LightSubsetEnumerationSetup.body 12 18,LightSignedLeafBatch.body 3,
    LightSignedLeafCell.body 4 8,LightSignedLeafGeneral.body 5 6 17,LightMaskUnion.body 12 16,
    LightStageLookup.body 7 8,LightDownsetSize.body 9 15,LightDownsetAddress.body 9 15,
    LightSubsetSetup.body 10 12 14,buildBody 11 13,fillBody,powTableBody,rowBody 19,
    rankBody 14,LightSubsetOffset.body,LightMaskErase.body 16,LightSign.body,
    LightSubsetEnumeration.body 18,LightArray.linearBody]

def procs : LightSignedLeafCell.Procs program 4 8 where
  pUnion := 5
  pLookup := 6
  pSign := 17
  pSize := 7
  pSetup := 9
  pBuild := 10
  pFill := 11
  pRow := 13
  pLinear := 19
  pPowers := 12
  pRank := 14
  pOffset := 15
  pErase := 16
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl

theorem program_meets     {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR dst maskBase work B D d : ℕ}
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ W)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdst : dst+downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap W boxCut ≤ work)
    (hsepL : Apart baseL ((W+1)*downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hsepR : Apart baseR ((W+1)*downsetCap W sourceCut) dst (downsetCap W boxCut))
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+9 ≤ lim.depth) :
    Meets lim program 0 d
      [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        baseL,baseR,dst,maskBase,work] μ (time W boxCut)
      (fun _ μ' => TableAt μ' dst boxCut (SignedLeaf.value f g stage preL preR) ∧
        KeptBut μ μ' maskBase dst (downsetCap W boxCut)) :=
  meets rfl procs rfl rfl rfl rfl preL preR f g hw hcut hboxCut hstage
    hdataL hdataR hdst hmasks hsepL hsepR hspace hword hproductWord hpreL hpreR
    hf hg hstoredL hstoredR hd

theorem time_bound {W cut : ℕ} (hcut : cut ≤ W) :
    time W cut ≤ 12000*(W+1)^3*(downsetCap W cut+1) := by
  have hp : 1 ≤ (W+1)^2*(downsetCap W cut+1) := by
    have hh : 0 < (W+1)^2*(downsetCap W cut+1) := by positivity
    omega
  have hlin : W+1 ≤ (W+1)^2 := by nlinarith
  have hsmall := Nat.mul_le_mul_right (downsetCap W cut+1) hlin
  have hb : roundBudget W cut+20 ≤ 11000*((W+1)^2*(downsetCap W cut+1)) := by
    unfold roundBudget enumBudget batchBudget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (11000*((W+1)^2*(downsetCap W cut+1)))
    (Nat.succ_le_succ hcut)
  have hp₃ : 1 ≤ (W+1)^3*(downsetCap W cut+1) := by
    have hh : 0 < (W+1)^3*(downsetCap W cut+1) := by positivity
    omega
  unfold time
  calc
    _ ≤ (W+1)*(11000*((W+1)^2*(downsetCap W cut+1)))+20 :=
      Nat.add_le_add_right (hm.trans hc) 20
    _ = 11000*((W+1)^3*(downsetCap W cut+1))+20 := by ring
    _ ≤ 12000*((W+1)^3*(downsetCap W cut+1)) := by omega
    _ = _ := by ring

end ThreeSum.LightSignedLeafTable
