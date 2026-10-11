import Submission.ThreeSum.LightReportingSuffixBatch

/-!
# Concrete box-leaf preprocessing over the shrinking suffix ground set

Each local cardinality layer is actually enumerated at width V and evaluated
against the width-W source transforms. The exponentially sized storage and
enumeration are downsetCap V boxCut; W occurs only in polynomial overhead.
-/

namespace ThreeSum.LightReportingSuffixTable

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress ReportingHostSuffix

variable {lim : Limits} {P : Program}

def enumBudget (V cut : ℕ) : ℕ := 800*(V+1)*(downsetCap V cut+1)
def batchBudget (W V cut : ℕ) : ℕ := 9400*(W+1)^2*(downsetCap V cut+1)
def roundBudget (W V cut : ℕ) : ℕ := enumBudget V cut+batchBudget W V cut+90

def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  .call pEnumSetup [v 8,v 15,v 13,v 14] 16 ;;
  .call pBatch [v 0,v 1,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 15,v 16,v 13,
    v 10,v 11,v 12,v 14] 17

def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 15 (v 2 +' k 1) (roundBody pEnumSetup pBatch)

def time (W V cut : ℕ) : ℕ := (cut+1)*(roundBudget W V cut+20)+20

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage baseL baseR dst maskBase work : ℕ)
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,baseL,baseR,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap V boxCut) ∧
    TableAt μ' dst boxCut (LightSignedLeafTable.stageValues μ dst j (leafWeight hfit f g stage preL preR))

theorem meets {pMain pEnumSetup pEnum pBatch pCell pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pEnumSetup pBatch))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body C.pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightReportingSuffixBatch.body pCell))
    (hCell : P[pCell]? = some (LightReportingSuffixCell.body pLeaf pAddress))
    {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR dst maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hboxCut : boxCut ≤ V)
    (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ maskBase)
    (hdst : dst+downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hsepL : Apart baseL ((W+1)*downsetCap W sourceCut) dst (downsetCap V boxCut))
    (hsepR : Apart baseR ((W+1)*downsetCap W sourceCut) dst (downsetCap V boxCut))
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
        V,2^offset,baseL,baseR,dst,maskBase,work] μ (time W V boxCut)
      (fun _ μ' => TableAt μ' dst boxCut (leafWeight hfit f g stage preL preR) ∧
        KeptBut μ μ' maskBase dst (downsetCap V boxCut)) := by
  have hV : V ≤ W := by omega
  have hword₀ : ((2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(V+1) : ℕ) ≤ (W+1)*2^(W+1) :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    exact (by exact_mod_cast hh : ((2^(V+1) : ℕ) : ℤ) ≤
      (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv hfit μ sourceCut boxCut stage baseL baseR dst maskBase work preL preR f g)
    (boxCut+1) (roundBudget W V boxCut) ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(W : ℤ),sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,2^offset,baseL,baseR,dst,maskBase,work,0] =
        frame ([(W : ℤ),sourceCut,boxCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
          V,2^offset,baseL,baseR,dst,maskBase,work,0] ++ [0,0])
      exact (frame_append_zeros _ 2).symm
    · intro S hS
      simp [LightSignedLeafTable.stageValues]
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
      (μ := μ') (L := V) (k := j) (dst := maskBase) (work := work)
      hw (by omega) hword₀ (by omega) (by omega) (by omega)
    have hentime : LightSubsetEnumerationSetup.time V j ≤ enumBudget V boxCut :=
      (LightSubsetEnumerationSetup.time_bound V j).trans
        (Nat.mul_le_mul_left (800*(V+1)) (Nat.succ_le_succ hchoose))
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
    have hb := LightReportingSuffixBatch.meets (d := d+1) hBatch hCell C hfit
      (enumerateLayer V j) preL preR f g hw hcut hstage (by omega) (by omega) (by omega)
      (by rw [enumerateLayer_length]; omega) hsepL hsepR (Or.inr hdst)
      hspace hword hproductWord hpreL hpreR hf hg hsourceL₁ hsourceR₁ hseg
      (fun m hm => (mem_enumerateLayer V j m).mp hm) hjcut (by omega)
    have hbtime : LightReportingSuffixBatch.time W V (enumerateLayer V j).length ≤ batchBudget W V boxCut := by
      rw [enumerateLayer_length]
      exact (LightReportingSuffixBatch.time_bound hV (V.choose j)).trans
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
        simpa only [LightSignedLeafTable.stageValues,heq,ite_true,show j < j+1 by omega] using hn
      · rw [if_neg heq,hbefore,hout T hT] at hn
        have hlt : T.card < j+1 ↔ T.card < j := by omega
        simpa only [LightSignedLeafTable.stageValues,hlt] using hn
  case done =>
    rintro _ _ ⟨n,r,μ',rfl,hkept,hout⟩
    refine ⟨?_,hkept⟩
    intro T hT
    simpa only [LightSignedLeafTable.stageValues,show T.card < boxCut+1 by omega,ite_true] using hout T hT
  case bound =>
    rintro j _ hj _ ⟨n,r,μ',rfl,_,_⟩
    light_side

def program : Program := LightSignedBoxSetup.program ++
  [LightReportingSuffixCell.body 6 10,LightReportingSuffixBatch.body 25,body 3 26]

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

theorem time_bound {W V cut : ℕ} (hV : V ≤ W) (hcut : cut ≤ V) :
    time W V cut ≤ 12000*(W+1)^3*(downsetCap V cut+1) := by
  have hp : 1 ≤ (W+1)^2*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlin : V+1 ≤ (W+1)^2 := by nlinarith
  have hsmall := Nat.mul_le_mul_right (downsetCap V cut+1) hlin
  have hb : roundBudget W V cut+20 ≤ 11000*((W+1)^2*(downsetCap V cut+1)) := by
    unfold roundBudget enumBudget batchBudget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (11000*((W+1)^2*(downsetCap V cut+1)))
    (Nat.succ_le_succ (hcut.trans hV))
  have hp₃ : 1 ≤ (W+1)^3*(downsetCap V cut+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time
  calc
    _ ≤ (W+1)*(11000*((W+1)^2*(downsetCap V cut+1)))+20 :=
      Nat.add_le_add_right (hm.trans hc) 20
    _ = 11000*((W+1)^3*(downsetCap V cut+1))+20 := by ring
    _ ≤ 12000*((W+1)^3*(downsetCap V cut+1)) := by omega
    _ = _ := by ring

end ThreeSum.LightReportingSuffixTable
