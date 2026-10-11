import Submission.ThreeSum.LightSignedLeaf

/-!
# Summing a cardinality layer of explicit signed leaves

Missing masks are read from actual memory. Each complementary leaf is
formed by exact subtraction and evaluated from the two stored source
transforms. The source cutoff is independent of the smaller box cutoff.
-/

namespace ThreeSum.LightLeafSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def term {W : ℕ} (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (U : Finset (Fin W)) : ℤ := SignedLeaf.value f g stage preL preR (Q \ U)

def partialSum {W : ℕ} (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin W))) (j : ℕ) : ℤ :=
  ((missing.map (term Q preL preR f g stage)).take j).sum

theorem partialSum_succ {W : ℕ} (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (stage : ℕ) (missing : List (Finset (Fin W))) {j : ℕ} (hj : j < missing.length) :
    partialSum Q preL preR f g stage missing (j+1) =
      partialSum Q preL preR f g stage missing j+term Q preL preR f g stage missing[j] := by
  unfold partialSum
  rw [List.sum_take_succ _ _ (by simpa using hj),List.getElem_map]

@[simp] theorem partialSum_length {W : ℕ} (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (missing : List (Finset (Fin W))) :
    partialSum Q preL preR f g stage missing missing.length =
      (missing.map (term Q preL preR f g stage)).sum := by
  unfold partialSum
  have he : missing.length = (missing.map (term Q preL preR f g stage)).length :=
    (List.length_map _).symm
  rw [he,List.take_length]

def roundBody (pLeaf : ℕ) : Stmt :=
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7 -' v 9,
    v 8 -' M (v 11 +' v 16),v 12,v 13,v 14] 17 ;;
  .set 15 (v 15 +' v 17)

/-- Width, source cutoff, suffix stage, two prefixes (cardinality and mask),
query cardinality and mask, missing cardinality, mask count, mask buffer,
two source-stage bases and scratch. -/
def body (pLeaf : ℕ) : Stmt :=
  .set 15 (k 0) ;;
  .for 16 (v 10) (roundBody pLeaf) ;;
  .set 0 (v 15)

def time (W n : ℕ) : ℕ := n*(LightSignedLeaf.time W+60)+40

def Inv {W : ℕ} (μ : ℕ → ℤ) (Q preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ) (stage : ℕ) (missing : List (Finset (Fin W)))
    (cut t maskBase baseL baseR work j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,
      partialSum Q preL preR f g stage missing j,j,r],μ'⟩ ∧ Kept μ μ' work

theorem meets {pMain pLeaf pLookup pSign pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pLeaf))
    (hLeaf : P[pLeaf]? = some (LightSignedLeaf.body pLookup pSign))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSign : P[pSign]? = some LightSign.body)
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (missing : List (Finset (Fin W)))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim P pMain d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,missing.length,maskBase,baseL,baseR,work] μ (time W missing.length)
      (fun r μ' => r = (missing.map (term Q preL preR f g stage)).sum ∧ Kept μ μ' work) := by
  have hQcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hQmask : (subsetMask Q : ℤ) ≤ lim.word := by
    have hp : subsetMask Q ≤ (W+1)*2^(W+1) :=
      (Nat.le_of_lt (subsetMask_isMask Q).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask Q : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hflagsL (U : Finset (Fin W)) : (preL ∪ (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preL) Finset.sdiff_subset)).trans hcardL
  have hflagsR (U : Finset (Fin W)) : (preR ∪ (Q \ U)).card ≤ cut :=
    (Finset.card_le_card (Finset.union_subset_union (Finset.Subset.refl preR) Finset.sdiff_subset)).trans hcardR
  have htermBound : ∀ U ∈ missing, |term Q preL preR f g stage U| ≤
      (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    intro U _
    exact SignedLeaf.abs_value_le f g stage preL preR (Q \ U) hstage (hflagsL U) (hflagsR U) hf hg
  have hacc (j : ℕ) : |partialSum Q preL preR f g stage missing j| ≤ lim.word := by
    have hh := List.abs_sum_take_map_le missing (term Q preL preR f g stage) htermBound j
    exact hh.trans (by simpa only [Nat.cast_mul] using haccWord)
  have haddr {base : ℕ} (hdata : base+(W+1)*downsetCap W cut ≤ work)
      (j : ℕ) (hj : j ≤ W) (S : Finset (Fin W)) (hS : S.card ≤ cut) :
      LightZetaStages.stageBase base (downsetCap W cut) j+subsetRank S < work := by
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
    unfold LightZetaStages.stageBase
    simp only [Nat.succ_mul] at hm hdata
    omega
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := missing.length*(LightSignedLeaf.time W+50)+20)
    (Q := Inv μ Q preL preR f g stage missing cut t maskBase baseL baseR work missing.length)
    (Inv μ Q preL preR f g stage missing cut t maskBase baseL baseR work)
    missing.length (LightSignedLeaf.time W+40) ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,μ,?_,SameOn.refl⟩
    simp [update_frame_setLocal,partialSum]
    change frame [(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,0,0] =
      frame ([(W : ℤ),cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      Q.card,subsetMask Q,t,missing.length,maskBase,baseL,baseR,work,0,0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hkeep⟩
    let U := missing[j]
    have hu := hvalid U (List.getElem_mem hj)
    have hstoredL' : LightZetaStages.StoredThrough μ' baseL cut f W := by
      intro i hi S hS
      exact (hkeep _ (haddr hdataL i hi S hS)).trans (hstoredL i hi S hS)
    have hstoredR' : LightZetaStages.StoredThrough μ' baseR cut g W := by
      intro i hi S hS
      exact (hkeep _ (haddr hdataR i hi S hS)).trans (hstoredR i hi S hS)
    have hmask : μ' (maskBase+j) = (subsetMask U : ℤ) := by
      have hr := hseg.getElem (by simpa using hj)
      simp only [List.getElem_map] at hr
      exact (hkeep _ (by omega)).trans hr
    have hcard : (Q \ U).card = Q.card-t := by rw [Finset.card_sdiff_of_subset hu.1,hu.2]
    have hmaskSub := MaskDifference.subsetMask_sdiff_int Q U hu.1
    have hcardInt : (Q.card : ℤ)-(t : ℤ) = ((Q \ U).card : ℤ) := by
      rw [hcard,Int.ofNat_sub (by rw [← hu.2]; exact Finset.card_le_card hu.1)]
    have hc := LightSignedLeaf.meets (d := d+1) hLeaf hLookup hSign hSize hAddress C hOffset
      preL preR (Q \ U) f g hw hcut hstage hdataL hdataR hspace hword hproductWord
      (hdisjL.mono_right Finset.sdiff_subset) (hdisjR.mono_right Finset.sdiff_subset)
      (hflagsL U) (hflagsR U) hf hg hstoredL' hstoredR' (by omega)
    unfold roundBody
    light_call hc using hmask,hmaskSub,hcardInt,LightSignedLeaf.time with res μ₁ ⟨hres,hnewKeep⟩
    have hnext := abs_le.mp (hacc (j+1))
    have hsum : partialSum Q preL preR f g stage missing j+term Q preL preR f g stage U =
        partialSum Q preL preR f g stage missing (j+1) :=
      (partialSum_succ Q preL preR f g stage missing hj).symm
    have hres' : res = term Q preL preR f g stage U := hres
    light_set (partialSum Q preL preR f g stage missing (j+1)) using hres',hsum,LightSignedLeaf.time
    refine ⟨by simp,res,μ₁,?_,hkeep.trans hnewKeep⟩
    simp [update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_⟩
    light_side
  case after =>
    rintro _ ⟨r,μ',rfl,hkeep⟩
    have ha := abs_le.mp (hacc missing.length)
    light_set ((missing.map (term Q preL preR f g stage)).sum) using partialSum_length
    exact ⟨by simp,hkeep⟩

def program : Program :=
  [body 1,LightSignedLeaf.body 2 13,LightStageLookup.body 3 4,
    LightDownsetSize.body 5 12,LightDownsetAddress.body 5 12,
    LightSubsetSetup.body 6 10 11,buildBody 7 8,fillBody,rowBody 9,
    LightArray.linearBody,powTableBody,rankBody 11,LightSubsetOffset.body,LightSign.body]

theorem program_procs : LightSubsetSetup.Procs program 5 6 7 8 9 10 11 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {W cut stage t maskBase baseL baseR work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (missing : List (Finset (Fin W)))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,missing.length,maskBase,baseL,baseR,work] μ (time W missing.length)
      (fun r μ' => r = (missing.map (term Q preL preR f g stage)).sum ∧ Kept μ μ' work) :=
  meets rfl rfl rfl rfl rfl rfl program_procs rfl Q preL preR missing f g hw hcut hstage
    hdataL hdataR hmasks hspace hword hproductWord haccWord hdisjL hdisjR hcardL hcardR hf hg
    hvalid hstoredL hstoredR hseg hd

theorem time_bound (W n : ℕ) : time W n ≤ 5900*(W+1)^2*(n+1) := by
  have ht := LightSignedLeaf.time_bound W
  have hp : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  unfold time
  nlinarith

end ThreeSum.LightLeafSum
