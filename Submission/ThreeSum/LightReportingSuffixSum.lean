import Submission.ThreeSum.LightReportingSuffixCell
import Submission.ThreeSum.LightLeafSum

/-! # Explicit local suffix leaves evaluated by actual global source reads -/

namespace ThreeSum.LightReportingSuffixSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits} {P : Program}

def term {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (U : Finset (Fin V)) : ℤ := leafWeight hfit f g stage preL preR (Q \ U)

def partialSum {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) (j : ℕ) : ℤ :=
  ((missing.map (term hfit Q preL preR f g stage)).take j).sum

theorem partialSum_succ {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) {j : ℕ} (hj : j < missing.length) :
    partialSum hfit Q preL preR f g stage missing (j+1) =
      partialSum hfit Q preL preR f g stage missing j+term hfit Q preL preR f g stage missing[j] := by
  unfold partialSum
  rw [List.sum_take_succ _ _ (by simpa using hj),List.getElem_map]

@[simp] theorem partialSum_length {W V offset : ℕ} (hfit : offset+V ≤ W) (Q : Finset (Fin V))
    (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V))) :
    partialSum hfit Q preL preR f g stage missing missing.length =
      (missing.map (term hfit Q preL preR f g stage)).sum := by
  unfold partialSum
  have he : missing.length = (missing.map (term hfit Q preL preR f g stage)).length :=
    (List.length_map _).symm
  rw [he,List.take_length]

def roundBody (pLeaf : ℕ) : Stmt :=
  .set 19 ((v 10 -' M (v 13 +' v 18)) *' v 8) ;;
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 9 -' v 11,v 19,v 14,v 15,v 16] 20 ;;
  .set 17 (v 17 +' v 20)

def body (pLeaf : ℕ) : Stmt :=
  .set 17 (k 0) ;;
  .for 18 (v 12) (roundBody pLeaf) ;;
  .set 0 (v 17)

def time (W n : ℕ) : ℕ := n*(LightSignedLeafGeneral.time W+100)+40

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (Q : Finset (Fin V)) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin V)))
    (cut t maskBase baseL baseR work j : ℕ) (σ : State) : Prop :=
  ∃ (mask r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,
      partialSum hfit Q preL preR f g stage missing j,j,mask,r],μ'⟩ ∧ Kept μ μ' work

theorem meets {pMain pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pLeaf)) (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    {μ : ℕ → ℤ} {W V offset cut stage t maskBase baseL baseR work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (missing : List (Finset (Fin V))) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim P pMain d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
        Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work] μ (time W missing.length)
      (fun r μ' => r = (missing.map (term hfit Q preL preR f g stage)).sum ∧ Kept μ μ' work) := by
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have hMaskWord (S : Finset (Fin W)) : (subsetMask S : ℤ) ≤ lim.word := by
    have hp : subsetMask S ≤ (W+1)*2^(W+1) :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask S : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hLocalMaskWord (S : Finset (Fin V)) : (subsetMask S : ℤ) ≤ lim.word := by
    have hp : subsetMask S ≤ (V+1)*2^(V+1) :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask S : ℤ) ≤ (((V+1)*2^(V+1) : ℕ) : ℤ)).trans
      (LightReportingSuffixCell.small_word (by omega : V ≤ W) hword)
  have hQmask := hLocalMaskWord Q
  have hflagsL (U : Finset (Fin V)) : (preL ∪ liftSet hfit (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL)
      ((liftSet_subset hfit _ _).mpr Finset.sdiff_subset))).trans hcardL
  have hflagsR (U : Finset (Fin V)) : (preR ∪ liftSet hfit (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR)
      ((liftSet_subset hfit _ _).mpr Finset.sdiff_subset))).trans hcardR
  have htermBound : ∀ U ∈ missing, |term hfit Q preL preR f g stage U| ≤
      (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    intro U _
    exact leafWeight_abs_le hfit f g preL preR _ hstage (hflagsL U) (hflagsR U) hf hg
  have hacc (j : ℕ) : |partialSum hfit Q preL preR f g stage missing j| ≤ lim.word := by
    have hh := List.abs_sum_take_map_le missing (term hfit Q preL preR f g stage) htermBound j
    exact hh.trans (by simpa only [Nat.cast_mul] using haccWord)
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := missing.length*(LightSignedLeafGeneral.time W+90)+20)
    (Q := Inv hfit μ Q preL preR f g stage missing cut t maskBase baseL baseR work missing.length)
    (Inv hfit μ Q preL preR f g stage missing cut t maskBase baseL baseR work)
    missing.length (LightSignedLeafGeneral.time W+80) ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,0,μ,?_,SameOn.refl⟩
    simp [update_frame_setLocal,partialSum]
    change frame [(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,0,0] =
      frame ([(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,0,0] ++ [0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨mask,r,μ',rfl,hkeep⟩
    let U := missing[j]
    have hu := hvalid U (List.getElem_mem hj)
    have hstoredL' := LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro i _ hi; exact hkeep i (hi.trans_le hdataL))
    have hstoredR' := LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro i _ hi; exact hkeep i (hi.trans_le hdataR))
    have hmask : μ' (maskBase+j) = (subsetMask U : ℤ) := by
      have hr := hseg.getElem (by simpa using hj)
      simp only [List.getElem_map] at hr
      exact (hkeep _ (by omega)).trans hr
    have hcard : (Q \ U).card = Q.card-t := by rw [Finset.card_sdiff_of_subset hu.1,hu.2]
    have hmaskSub := MaskDifference.subsetMask_sdiff_int Q U hu.1
    have hcardInt : (Q.card : ℤ)-(t : ℤ) = ((Q \ U).card : ℤ) := by
      rw [hcard,Int.ofNat_sub (by rw [← hu.2]; exact Finset.card_le_card hu.1)]
    have hscaled : ((subsetMask Q : ℤ)-(subsetMask U : ℤ))*(2 : ℤ)^offset =
        (subsetMask (liftSet hfit (Q \ U)) : ℤ) := by
      rw [hmaskSub,liftSet_mask_int]
      push_cast
      ring
    have hlocalWord := hLocalMaskWord (Q \ U)
    have hScaledBounds : -lim.word ≤
        ((subsetMask Q : ℤ)-(subsetMask U : ℤ))*(2 : ℤ)^offset ∧
        ((subsetMask Q : ℤ)-(subsetMask U : ℤ))*(2 : ℤ)^offset ≤ lim.word := by
      rw [hscaled]
      have := hMaskWord (liftSet hfit (Q \ U))
      have := Int.natCast_nonneg (subsetMask (liftSet hfit (Q \ U)))
      omega
    unfold roundBody
    light_set (subsetMask (liftSet hfit (Q \ U)) : ℕ) using hmask,hscaled,LightSignedLeafGeneral.time
    have hc := LightSignedLeafGeneral.meets (d := d+1)
      C.leaf C.union C.lookup C.sign C.size C.address C.setup C.offset C.erase
      preL preR (liftSet hfit (Q \ U)) f g hw hcut hstage hdataL hdataR hspace hword hproductWord
      (hflagsL U) (hflagsR U) hf hg hstoredL' hstoredR' (by omega)
    rw [liftSet_card] at hc
    light_call hc using hcardInt,LightSignedLeafGeneral.time with res μ₁ ⟨hres,hnewKeep⟩
    have hnext := abs_le.mp (hacc (j+1))
    have hsum : partialSum hfit Q preL preR f g stage missing j+term hfit Q preL preR f g stage U =
        partialSum hfit Q preL preR f g stage missing (j+1) :=
      (partialSum_succ hfit Q preL preR f g stage missing hj).symm
    have hres' : res = term hfit Q preL preR f g stage U := hres
    light_set (partialSum hfit Q preL preR f g stage missing (j+1)) using hres',hsum,LightSignedLeafGeneral.time
    refine ⟨by simp,(subsetMask (liftSet hfit (Q \ U)) : ℤ),res,μ₁,?_,hkeep.trans hnewKeep⟩
    simp [update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨mask,r,μ',rfl,_⟩
    light_side
  case after =>
    rintro _ ⟨mask,r,μ',rfl,hkeep⟩
    have ha := abs_le.mp (hacc missing.length)
    light_set ((missing.map (term hfit Q preL preR f g stage)).sum) using partialSum_length
    exact ⟨by simp,hkeep⟩

theorem time_bound (W n : ℕ) : time W n ≤ 8000*(W+1)^2*(n+1) := by
  have ht := LightSignedLeafGeneral.time_bound W
  have hp : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixSum
