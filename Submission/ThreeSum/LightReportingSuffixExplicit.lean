import Submission.ThreeSum.LightReportingSuffixSum
import Submission.ThreeSum.LightExplicitSum

/-! # Actual output-sensitive enumeration and evaluation of explicit local suffix leaves -/

namespace ThreeSum.LightReportingSuffixExplicit

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostSuffix

variable {lim : Limits} {P : Program}

structure Procs (P : Program) (pEnum pSum : ℕ) where
  (pWeights pCore pLeaf pAddress : ℕ)
  leafProcs : LightSignedLeafCell.Procs P pLeaf pAddress
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body leafProcs.pPowers leafProcs.pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightReportingSuffixSum.body pLeaf)

def roundBody (pEnum pSum : ℕ) : Stmt :=
  .call pEnum [v 7,v 10,v 17,v 14,v 15] 18 ;;
  .call pSum [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 17,v 18,v 14,v 12,v 13,v 15] 19 ;;
  .set 16 (v 16 +' v 19)

def body (pEnum pSum : ℕ) : Stmt :=
  .set 16 (k 0) ;;
  .for 17 (v 11) (roundBody pEnum pSum) ;;
  .set 0 (v 16)

def roundTime (W c t : ℕ) : ℕ := 10500*(W+1)^2*(layerOffset c t+1)
def time (W c t : ℕ) : ℕ := t*(roundTime W c t+30)+40

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage cut t baseL baseR maskBase work j : ℕ) (σ : State) : Prop :=
  ∃ (count r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,
      ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) j,j,count,r],μ'⟩ ∧
      KeptBut μ μ' work maskBase (layerOffset Q.card t)

theorem meets {pMain pEnum pSum : ℕ}
    (hmain : P[pMain]? = some (body pEnum pSum)) (C : Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W V offset cut stage t maskBase baseL baseR work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+layerOffset Q.card t ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim P pMain d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
        Q.card,subsetMask Q,t,baseL,baseR,maskBase,work] μ (time W Q.card t)
      (fun r μ' => r = ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) t ∧
        KeptBut μ μ' work maskBase (layerOffset Q.card t)) := by
  have hV : V ≤ W := by omega
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have henumSpace : work+(2*V+2) ≤ lim.space := by
    unfold tableSize at hspace
    nlinarith [Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2]
  have henumWord : ((2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(V+1) : ℕ) ≤ (W+1)*2^(W+1) :=
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans
        (Nat.le_mul_of_pos_left _ (by omega))
    exact (by exact_mod_cast hh : ((2^(V+1) : ℕ) : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word := by
    have hh := Nat.le_mul_of_pos_left ((2^stage*B)*(2^stage*D)) (by omega : 0 < layerOffset Q.card t+1)
    exact (by exact_mod_cast hh : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤
      (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ)).trans haccWord
  have hweight (S : Finset (Fin V)) (hS : S ⊆ Q) :
      |leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
    leafWeight_abs_le hfit f g preL preR S hstage
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL)
        ((liftSet_subset hfit _ _).mpr hS))).trans hcardL)
      ((Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR)
        ((liftSet_subset hfit _ _).mpr hS))).trans hcardR) hf hg
  have hacc (j : ℕ) (hj : j ≤ t) :
      |ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) j| ≤ lim.word := by
    have hh := ExplicitLayers.valueSum_abs_le Q (leafWeight hfit f g stage preL preR) j hweight
    have hn : layerOffset Q.card j*((2^stage*B)*(2^stage*D)) ≤
        (layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) :=
      Nat.mul_le_mul_right _ ((layerOffset_mono Q.card hj).trans (Nat.le_succ _))
    have hz : ((layerOffset Q.card j*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
        (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by exact_mod_cast hn
    exact hh.trans (hz.trans haccWord)
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := t*(roundTime W Q.card t+20)+20)
    (Q := Inv hfit μ Q preL preR f g stage cut t baseL baseR maskBase work t)
    (Inv hfit μ Q preL preR f g stage cut t baseL baseR maskBase work)
    t (roundTime W Q.card t) ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,0,μ,?_,SameOn.refl⟩
    simp [update_frame_setLocal]
    change frame [(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,0,0] =
      frame ([(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
      Q.card,subsetMask Q,t,baseL,baseR,maskBase,work,0,0] ++ [0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨count,r,μ',rfl,hkeep⟩
    have hcap := ExplicitLayers.choose_le_offset (c := Q.card) hj
    have hEnumTime : LightQueryEnumeration.time V Q.card j ≤
        1400*(W+1)^2*(layerOffset Q.card t+1) := by
      have hv := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
      have hb := (LightQueryEnumeration.time_bound hQcard).trans
        (Nat.mul_le_mul_left (1400*(V+1)^2) (Nat.succ_le_succ hcap))
      exact hb.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 1400 hv))
    have hSumTime : LightReportingSuffixSum.time W (Q.card.choose j) ≤
        8000*(W+1)^2*(layerOffset Q.card t+1) :=
      (LightReportingSuffixSum.time_bound W _).trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ hcap))
    have hp : 1 ≤ (W+1)^2*(layerOffset Q.card t+1) := Nat.mul_pos (by positivity) (by omega)
    have hround : LightQueryEnumeration.time V Q.card j+
        LightReportingSuffixSum.time W (Q.card.choose j)+110 ≤ roundTime W Q.card t := by
      unfold roundTime
      nlinarith
    have he := LightQueryEnumeration.meets (d := d+1) (μ := μ')
      (t := j) (dst := maskBase) (work := work) C.enumerate C.weights C.leafProcs.setup.powers
      C.leafProcs.erase C.core Q hw henumSpace henumWord (by omega) (by omega) (by omega)
    unfold roundBody
    light_call he with newCount μ₁ ⟨hcount,hmaskSeg,_,hkeepEnum⟩
    have hkeep₁ : KeptBut μ μ₁ work maskBase (layerOffset Q.card t) := by
      intro i hi
      exact (hkeepEnum i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩).trans (hkeep i hi)
    have hstoredL₁ := LightSignedLeafBatch.storedThrough_of_on hstoredL (by
      intro i _ hi
      have ha := hi.trans_le hdataL
      exact hkeep₁ i ⟨by omega,Or.inl ha⟩)
    have hstoredR₁ := LightSignedLeafBatch.storedThrough_of_on hstoredR (by
      intro i _ hi
      have ha := hi.trans_le hdataR
      exact hkeep₁ i ⟨by omega,Or.inl ha⟩)
    have hsumWord : (((missingSets Q j).length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word := by
      have hn := Nat.mul_le_mul_right ((2^stage*B)*(2^stage*D)) (hcap.trans (Nat.le_succ _))
      have hz : ((Q.card.choose j*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
          (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by exact_mod_cast hn
      simpa only [missingSets_length] using hz.trans haccWord
    have hs := LightReportingSuffixSum.meets (d := d+1) (μ := μ₁) C.sum C.leafProcs
      hfit Q preL preR (missingSets Q j) f g hw hcut hstage (by omega) (by omega)
      (by simpa using (show maskBase+Q.card.choose j ≤ work by omega)) hspace hword hproductWord hsumWord
      hcardL hcardR hf hg (fun U hU => (missingSets_mem Q U j).mp hU) hstoredL₁ hstoredR₁ hmaskSeg (by omega)
    light_call hs using hcount,missingSets_length with res μ₂ ⟨hres,hkeepSum⟩
    have hnext := abs_le.mp (hacc (j+1) (by omega))
    have hres' : res = ((missingSets Q j).map fun U => leafWeight hfit f g stage preL preR (Q \ U)).sum := hres
    have hsucc := ExplicitLayers.valueSum_succ Q (leafWeight hfit f g stage preL preR) j
    light_set (ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) (j+1)) using hres',hsucc
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
    light_set (ExplicitLayers.valueSum Q (leafWeight hfit f g stage preL preR) t)
    exact ⟨by simp,hkeep⟩

theorem time_bound {W c t : ℕ} (ht : t ≤ W+1) :
    time W c t ≤ 11000*(W+1)^3*(layerOffset c t+1) := by
  have hp : 1 ≤ (W+1)^2*(layerOffset c t+1) := Nat.mul_pos (by positivity) (by omega)
  have hm := Nat.mul_le_mul_right (roundTime W c t+30) ht
  unfold time roundTime at *
  nlinarith

end ThreeSum.LightReportingSuffixExplicit
