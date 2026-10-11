import Submission.ThreeSum.ExplicitLayers
import Submission.ThreeSum.LightLeafSum
import Submission.ThreeSum.LightQueryEnumeration

/-!
# Complete execution of the explicit leaves of a sparse query

The loop visits only missing-set cardinalities below the threshold. Each
layer is enumerated inside the actual query mask and immediately evaluated.
One reusable mask buffer is sufficient; all source stages are preserved.
-/

namespace ThreeSum.LightExplicitSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}

structure Procs (P : Program) (pEnum pSum : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pCore : ℕ
  pLeaf : ℕ
  pLookup : ℕ
  pSign : ℕ
  pSize : ℕ
  pAddress : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pRank : ℕ
  pOffset : ℕ
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightLeafSum.body pLeaf)
  leaf : P[pLeaf]? = some (LightSignedLeaf.body pLookup pSign)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  sign : P[pSign]? = some LightSign.body
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  table : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body

def roundBody (pEnum pSum : ℕ) : Stmt :=
  .call pEnum [v 0,v 8,v 15,v 12,v 13] 16 ;;
  .call pSum [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 15,v 16,v 12,v 10,v 11,v 13] 17 ;;
  .set 14 (v 14 +' v 17)

/-- Width, source cutoff, suffix stage, two prefixes, query cardinality and
mask, missing threshold, two source bases, reusable mask buffer and scratch. -/
def body (pEnum pSum : ℕ) : Stmt :=
  .set 14 (k 0) ;;
  .for 15 (v 9) (roundBody pEnum pSum) ;;
  .set 0 (v 14)

def roundTime (W c t : ℕ) : ℕ := 8000*(W+1)^2*(layerOffset c t+1)

def time (W c t : ℕ) : ℕ := t*(roundTime W c t+30)+40

def Inv {W : ℕ} (μ : ℕ → ℤ) (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (stage cut t baseL baseR maskBase work j : ℕ) (σ : State) : Prop :=
  ∃ (count r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,
      ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) j,j,count,r],μ'⟩ ∧
      KeptBut μ μ' work maskBase (layerOffset Q.card t)

theorem meets {pMain pEnum pSum : ℕ}
    (hmain : P[pMain]? = some (body pEnum pSum)) (C : Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+layerOffset Q.card t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim P pMain d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,baseL,baseR,maskBase,work] μ (time W Q.card t)
      (fun r μ' => r = ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) t ∧
        KeptBut μ μ' work maskBase (layerOffset Q.card t)) := by
  have hQcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have henumSpace : work+(2*W+2) ≤ lim.space := by unfold tableSize at hspace; nlinarith
  have henumWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(W+1) : ℕ) ≤ (W+1)*2^(W+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(W+1) : ℕ) : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word := by
    have hh := Nat.le_mul_of_pos_left ((2^stage*B)*(2^stage*D)) (by omega : 0 < layerOffset Q.card t+1)
    exact (by exact_mod_cast hh : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤
      (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ)).trans haccWord
  have hweight (S : Finset (Fin W)) (hS : S ⊆ Q) :
      |SignedLeaf.value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
    SignedLeaf.abs_value_le f g stage preL preR S hstage
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL) hS)).trans hcardL)
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR) hS)).trans hcardR) hf hg
  have hacc (j : ℕ) (hj : j ≤ t) :
      |ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) j| ≤ lim.word := by
    have hh := ExplicitLayers.valueSum_abs_le Q (SignedLeaf.value f g stage preL preR) j hweight
    have hn : layerOffset Q.card j*((2^stage*B)*(2^stage*D)) ≤
        (layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) :=
      Nat.mul_le_mul_right _ ((layerOffset_mono Q.card hj).trans (Nat.le_succ _))
    have hz : ((layerOffset Q.card j*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
        (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by exact_mod_cast hn
    exact hh.trans (hz.trans haccWord)
  have haddr {base : ℕ} (hdata : base+(W+1)*downsetCap W cut ≤ maskBase)
      (j : ℕ) (hj : j ≤ W) (S : Finset (Fin W)) (hS : S.card ≤ cut) :
      LightZetaStages.stageBase base (downsetCap W cut) j+subsetRank S < maskBase := by
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
    unfold LightZetaStages.stageBase
    simp only [Nat.succ_mul] at hm hdata
    omega
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := t*(roundTime W Q.card t+20)+20)
    (Q := Inv μ Q preL preR f g stage cut t baseL baseR maskBase work t)
    (Inv μ Q preL preR f g stage cut t baseL baseR maskBase work)
    t (roundTime W Q.card t) ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,0,μ,?_,SameOn.refl⟩
    simp [update_frame_setLocal]
    change frame [(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,0,0] =
      frame ([(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,0,0] ++ [0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨count,r,μ',rfl,hkeep⟩
    have hcap := ExplicitLayers.choose_le_offset (c := Q.card) hj
    have hEnumTime : LightQueryEnumeration.time W Q.card j ≤
        1400*(W+1)^2*(layerOffset Q.card t+1) :=
      (LightQueryEnumeration.time_bound hQcard).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hcap))
    have hSumTime : LightLeafSum.time W (Q.card.choose j) ≤
        5900*(W+1)^2*(layerOffset Q.card t+1) :=
      (LightLeafSum.time_bound W _).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hcap))
    have hp : 1 ≤ (W+1)^2*(layerOffset Q.card t+1) := Nat.mul_pos (by positivity) (by omega)
    have hround : LightQueryEnumeration.time W Q.card j+
        LightLeafSum.time W (Q.card.choose j)+100 ≤ roundTime W Q.card t := by
      unfold roundTime
      nlinarith
    have he := LightQueryEnumeration.meets (d := d+1) (μ := μ')
      (t := j) (dst := maskBase) (work := work) C.enumerate C.weights C.table.powers C.erase C.core
      Q hw henumSpace henumWord (by omega) (by omega) (by omega)
    unfold roundBody
    light_call he with newCount μ₁ ⟨hcount,hmaskSeg,_,hkeepEnum⟩
    have hkeep₁ : KeptBut μ μ₁ work maskBase (layerOffset Q.card t) := by
      intro i hi
      exact (hkeepEnum i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩).trans (hkeep i hi)
    have hstoredL₁ : LightZetaStages.StoredThrough μ₁ baseL cut f W := by
      intro i hi S hS
      have ha := haddr hdataL i hi S hS
      exact (hkeep₁ _ ⟨by omega,Or.inl ha⟩).trans (hstoredL i hi S hS)
    have hstoredR₁ : LightZetaStages.StoredThrough μ₁ baseR cut g W := by
      intro i hi S hS
      have ha := haddr hdataR i hi S hS
      exact (hkeep₁ _ ⟨by omega,Or.inl ha⟩).trans (hstoredR i hi S hS)
    have hsumWord : (((missingSets Q j).length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word := by
      have hn := Nat.mul_le_mul_right ((2^stage*B)*(2^stage*D)) (hcap.trans (Nat.le_succ _))
      have hz : ((Q.card.choose j*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
        (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by exact_mod_cast hn
      simpa only [missingSets_length] using hz.trans haccWord
    have hs := LightLeafSum.meets (d := d+1) (μ := μ₁) C.sum C.leaf C.lookup C.sign C.size C.address C.table C.offset
      Q preL preR (missingSets Q j) f g hw hcut hstage (by omega) (by omega)
      (by simpa using (show maskBase+Q.card.choose j ≤ work by omega)) hspace hword hproductWord hsumWord
      hdisjL hdisjR hcardL hcardR hf hg
      (fun U hU => (missingSets_mem Q U j).mp hU) hstoredL₁ hstoredR₁ hmaskSeg (by omega)
    light_call hs using hcount,missingSets_length with res μ₂ ⟨hres,hkeepSum⟩
    have hnext := abs_le.mp (hacc (j+1) (by omega))
    have hres' : res = ((missingSets Q j).map fun U => SignedLeaf.value f g stage preL preR (Q \ U)).sum := hres
    have hsucc := ExplicitLayers.valueSum_succ Q (SignedLeaf.value f g stage preL preR) j
    light_set (ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) (j+1)) using hres',hsucc
    refine ⟨by simp,newCount,res,μ₂,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hkeepSum i hi.1).trans (hkeep₁ i hi)
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨count,r,μ',rfl,_⟩
    light_side
  case after =>
    rintro _ ⟨count,r,μ',rfl,hkeep⟩
    have ha := abs_le.mp (hacc t le_rfl)
    light_set (ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) t)
    exact ⟨by simp,hkeep⟩

def program : Program :=
  [body 1 4,LightQueryEnumeration.body 2 3,LightQueryWeights.body 14 17,
    LightSubsetEnumeration.body 3,LightLeafSum.body 5,LightSignedLeaf.body 6 18,
    LightStageLookup.body 7 8,LightDownsetSize.body 9 16,LightDownsetAddress.body 9 16,
    LightSubsetSetup.body 10 14 15,buildBody 11 12,fillBody,rowBody 13,LightArray.linearBody,
    powTableBody,rankBody 15,LightSubsetOffset.body,LightMaskErase.body 17,LightSign.body]

def program_procs : Procs program 1 4 where
  pWeights := 2
  pPowers := 14
  pErase := 17
  pCore := 3
  pLeaf := 5
  pLookup := 6
  pSign := 18
  pSize := 7
  pAddress := 8
  pSetup := 9
  pBuild := 10
  pFill := 11
  pRow := 12
  pLinear := 13
  pRank := 15
  pOffset := 16
  enumerate := rfl
  weights := rfl
  erase := rfl
  core := rfl
  sum := rfl
  leaf := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  table := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl

theorem program_meets    {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+layerOffset Q.card t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,baseL,baseR,maskBase,work] μ (time W Q.card t)
      (fun r μ' => r = ExplicitLayers.valueSum Q (SignedLeaf.value f g stage preL preR) t ∧
        KeptBut μ μ' work maskBase (layerOffset Q.card t)) :=
  meets rfl program_procs Q preL preR f g hw hcut hstage hdataL hdataR hmasks hspace hword
    haccWord ht hdisjL hdisjR hcardL hcardR hf hg hstoredL hstoredR hd

theorem time_bound {W c t : ℕ} (ht : t ≤ W+1) :
    time W c t ≤ 8200*(W+1)^3*(layerOffset c t+1) := by
  have hp : 1 ≤ (W+1)^2*(layerOffset c t+1) := Nat.mul_pos (by positivity) (by omega)
  have hm := Nat.mul_le_mul_right (roundTime W c t+30) ht
  unfold time roundTime at *
  nlinarith

end ThreeSum.LightExplicitSum
