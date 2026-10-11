import Submission.ThreeSum.SignedLeaf
import Submission.ThreeSum.LightStageLookup
import Submission.ThreeSum.LightSign

/-!
# Evaluating one signed leaf by actual stored suffix-stage reads

The program forms the two disjoint prefix unions by integer addition,
computes both compact addresses, reads both stored transform cells, takes
their product, and applies the exact alternating sign. All arithmetic
bounds follow from the original histogram bounds.
-/

namespace ThreeSum.LightSignedLeaf

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Width, source cutoff, suffix stage, left prefix cardinality and mask,
right prefix cardinality and mask, leaf cardinality and mask, two source
stage-array bases, polynomial scratch. -/
def body (pLookup pSign : ℕ) : Stmt :=
  .call pLookup [v 0,v 1,v 3 +' v 7,v 4 +' v 8,v 2,v 9,v 11] 12 ;;
  .call pLookup [v 0,v 1,v 5 +' v 7,v 6 +' v 8,v 2,v 10,v 11] 13 ;;
  .set 14 (v 12 *' v 13) ;;
  .call pSign [v 14,v 7] 0

def time (W : ℕ) : ℕ := 2*LightStageLookup.time W+LightSign.time W+80

theorem meets {pMain pLookup pSign pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset : ℕ}
    (hmain : P[pMain]? = some (body pLookup pSign))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSign : P[pSign]? = some LightSign.body)
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    {μ : ℕ → ℤ} {W cut stage baseL baseR work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hdisjL : Disjoint preL S) (hdisjR : Disjoint preR S)
    (hcardL : (preL ∪ S).card ≤ cut) (hcardR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+6 ≤ lim.depth) :
    Meets lim P pMain d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        S.card,subsetMask S,baseL,baseR,work] μ (time W)
      (fun r μ' => r = SignedLeaf.value f g stage preL preR S ∧ Kept μ μ' work) := by
  have hScard : S.card ≤ W := by simpa using Finset.card_le_univ S
  have hCL : preL.card+S.card = (preL ∪ S).card := (Finset.card_union_of_disjoint hdisjL).symm
  have hCR : preR.card+S.card = (preR ∪ S).card := (Finset.card_union_of_disjoint hdisjR).symm
  have hML : subsetMask preL+subsetMask S = subsetMask (preL ∪ S) :=
    (SignedLeaf.subsetMask_disjoint_union preL S hdisjL).symm
  have hMR : subsetMask preR+subsetMask S = subsetMask (preR ∪ S) :=
    (SignedLeaf.subsetMask_disjoint_union preR S hdisjR).symm
  have hmaskWord (T : Finset (Fin W)) : (subsetMask T : ℤ) ≤ lim.word := by
    have hp : subsetMask T ≤ (W+1)*2^(W+1) :=
      (Nat.le_of_lt (subsetMask_isMask T).1).trans
        ((Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hp : (subsetMask T : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have haddrR : LightStageLookup.readAddr cut baseR stage (preR ∪ S) < work := by
    have hr := subsetRank_lt hcardR
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hstage)
    unfold LightStageLookup.readAddr
    simp only [Nat.succ_mul] at hm hdataR
    omega
  have hreadL : μ (LightStageLookup.readAddr cut baseL stage (preL ∪ S)) =
      SubsetStages.stageValue f stage (preL ∪ S) := by
    simpa only [LightStageLookup.readAddr,LightZetaStages.stageBase] using hstoredL stage hstage _ hcardL
  have hreadR : μ (LightStageLookup.readAddr cut baseR stage (preR ∪ S)) =
      SubsetStages.stageValue g stage (preR ∪ S) := by
    simpa only [LightStageLookup.readAddr,LightZetaStages.stageBase] using hstoredR stage hstage _ hcardR
  have hproduct : |SubsetStages.stageValue f stage (preL ∪ S)*
      SubsetStages.stageValue g stage (preR ∪ S)| ≤ lim.word := by
    rw [abs_mul]
    have h₁ := SubsetStages.stageValue_abs_le f hf stage hstage (preL ∪ S) hcardL
    have h₂ := SubsetStages.stageValue_abs_le g hg stage hstage (preR ∪ S) hcardR
    have hh := mul_le_mul h₁ h₂ (abs_nonneg _) (Int.natCast_nonneg _)
    exact hh.trans (by simpa only [Nat.cast_mul] using hproductWord)
  have hmaskLWord := hmaskWord (preL ∪ S)
  have hmaskRWord := hmaskWord (preR ∪ S)
  apply Meets.of_body hmain
  unfold body time
  have hcL := LightStageLookup.meets (d := d+1) (μ := μ)
    hLookup hSize hAddress C hOffset (preL ∪ S) _ hw hcut hdataL hspace hword hcardL hstage hreadL (by omega)
  light_call hcL using hCL,hML,LightStageLookup.time,LightSign.time
    with left μ₁ ⟨hleft,hkeepL⟩
  have hreadR₁ : μ₁ (LightStageLookup.readAddr cut baseR stage (preR ∪ S)) =
      SubsetStages.stageValue g stage (preR ∪ S) := (hkeepL _ haddrR).trans hreadR
  have hcR := LightStageLookup.meets (d := d+1) (μ := μ₁)
    hLookup hSize hAddress C hOffset (preR ∪ S) _ hw hcut hdataR hspace hword hcardR hstage hreadR₁ (by omega)
  light_call hcR using hCR,hMR,LightStageLookup.time,LightSign.time
    with right μ₂ ⟨hright,hkeepR⟩
  have hpBound := abs_le.mp hproduct
  light_set (SubsetStages.stageValue f stage (preL ∪ S)*SubsetStages.stageValue g stage (preR ∪ S))
    using hleft,hright,LightStageLookup.time,LightSign.time
  have hsign := LightSign.meets (d := d+1) (μ := μ₂) (e := S.card) hSign hw (by omega) hproduct
  light_call hsign using LightStageLookup.time,LightSign.time with res μ₃ ⟨hres,hmem⟩
  subst μ₃
  exact ⟨hres,hkeepL.trans hkeepR⟩

def program : Program :=
  [body 1 12,LightStageLookup.body 2 3,LightDownsetSize.body 4 11,
    LightDownsetAddress.body 4 11,LightSubsetSetup.body 5 9 10,
    buildBody 6 7,fillBody,rowBody 8,LightArray.linearBody,powTableBody,
    rankBody 10,LightSubsetOffset.body,LightSign.body]

theorem program_procs : LightSubsetSetup.Procs program 4 5 6 7 8 9 10 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {W cut stage baseL baseR work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hdisjL : Disjoint preL S) (hdisjR : Disjoint preR S)
    (hcardL : (preL ∪ S).card ≤ cut) (hcardR : (preR ∪ S).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hd : d+W+6 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        S.card,subsetMask S,baseL,baseR,work] μ (time W)
      (fun r μ' => r = SignedLeaf.value f g stage preL preR S ∧ Kept μ μ' work) :=
  meets rfl rfl rfl rfl rfl program_procs rfl preL preR S f g hw hcut hstage
    hdataL hdataR hspace hword hproductWord hdisjL hdisjR hcardL hcardR hf hg hstoredL hstoredR hd

theorem time_bound (W : ℕ) : time W ≤ 5800*(W+1)^2 := by
  have ht := LightStageLookup.time_bound W
  unfold time LightSign.time
  nlinarith

end ThreeSum.LightSignedLeaf
