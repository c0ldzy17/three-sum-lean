import Submission.ThreeSum.LightSignedLeaf
import Submission.ThreeSum.LightMaskUnion

/-!
# Signed leaves with arbitrary prefix overlap

Two bounded width scans construct the actual prefix unions and their
cardinalities. The compact source-table reads and signed multiplication
then give the same leaf function used by the sparse query theorem.
-/

namespace ThreeSum.LightSignedLeafGeneral

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- The arguments agree with `LightSignedLeaf`; no disjointness is required.
One extra scratch cell receives each actual union cardinality. -/
def body (pUnion pLookup pSign : ℕ) : Stmt :=
  .call pUnion [v 0,v 3,v 4,v 8,v 11,v 11 +' k 1] 12 ;;
  .set 13 (M (v 11)) ;;
  .call pLookup [v 0,v 1,v 13,v 12,v 2,v 9,v 11 +' k 1] 14 ;;
  .call pUnion [v 0,v 5,v 6,v 8,v 11,v 11 +' k 1] 15 ;;
  .set 16 (M (v 11)) ;;
  .call pLookup [v 0,v 1,v 16,v 15,v 2,v 10,v 11 +' k 1] 17 ;;
  .set 18 (v 14 *' v 17) ;;
  .call pSign [v 18,v 7] 0

def time (W : ℕ) : ℕ :=
  2*LightMaskUnion.time W+2*LightStageLookup.time W+LightSign.time W+160

theorem meets {pMain pUnion pLookup pSign pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pUnion pLookup pSign))
    (hUnion : P[pUnion]? = some (LightMaskUnion.body pPowers pErase))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSign : P[pSign]? = some LightSign.body)
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W cut stage baseL baseR work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
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
  have hCL : (preL ∪ S).card ≤ W := hcardL.trans hcut
  have hCR : (preR ∪ S).card ≤ W := hcardR.trans hcut
  have hpowWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(W+1) ≤ (W+1)*2^(W+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(W+1) : ℕ) : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have haddrL : LightStageLookup.readAddr cut baseL stage (preL ∪ S) < work := by
    have hr := subsetRank_lt hcardL
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hstage)
    unfold LightStageLookup.readAddr
    simp only [Nat.succ_mul] at hm hdataL
    omega
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
  apply Meets.of_body hmain
  unfold body time
  have huL := LightMaskUnion.meets (d := d+1) (μ := μ) (dst := work) (work := work+1)
    hUnion C.powers hErase preL S hw (by omega) (by omega) hpowWord (by omega)
  light_call huL using LightMaskUnion.time,LightStageLookup.time,LightSign.time
    with maskL μ₁ ⟨hmaskL,hcardReadL,hpowersL,hkeepUL⟩
  have hkeepL₁ : Kept μ μ₁ work := by
    intro i hi
    exact hkeepUL i ⟨by omega,Or.inl hi⟩
  light_set ((preL ∪ S).card : ℕ) using hcardReadL,LightMaskUnion.time,LightStageLookup.time,LightSign.time
  have hreadL₁ : μ₁ (LightStageLookup.readAddr cut baseL stage (preL ∪ S)) =
      SubsetStages.stageValue f stage (preL ∪ S) := (hkeepL₁ _ haddrL).trans hreadL
  have hcL := LightStageLookup.meets (d := d+1) (μ := μ₁) (work := work+1)
    hLookup hSize hAddress C hOffset (preL ∪ S) _ hw hcut (by omega) hspace hword hcardL hstage hreadL₁ (by omega)
  light_call hcL using hmaskL,LightMaskUnion.time,LightStageLookup.time,LightSign.time
    with left μ₂ ⟨hleft,hkeepLR⟩
  have hkeepL₂ : Kept μ μ₂ work := by
    intro i hi
    exact (hkeepLR i (by omega)).trans (hkeepL₁ i hi)
  have huR := LightMaskUnion.meets (d := d+1) (μ := μ₂) (dst := work) (work := work+1)
    hUnion C.powers hErase preR S hw (by omega) (by omega) hpowWord (by omega)
  light_call huR using LightMaskUnion.time,LightStageLookup.time,LightSign.time
    with maskR μ₃ ⟨hmaskR,hcardReadR,hpowersR,hkeepUR⟩
  have hkeepR₁ : Kept μ μ₃ work := by
    intro i hi
    exact (hkeepUR i ⟨by omega,Or.inl hi⟩).trans (hkeepL₂ i hi)
  light_set ((preR ∪ S).card : ℕ) using hcardReadR,LightMaskUnion.time,LightStageLookup.time,LightSign.time
  have hreadR₁ : μ₃ (LightStageLookup.readAddr cut baseR stage (preR ∪ S)) =
      SubsetStages.stageValue g stage (preR ∪ S) := (hkeepR₁ _ haddrR).trans hreadR
  have hcR := LightStageLookup.meets (d := d+1) (μ := μ₃) (work := work+1)
    hLookup hSize hAddress C hOffset (preR ∪ S) _ hw hcut (by omega) hspace hword hcardR hstage hreadR₁ (by omega)
  light_call hcR using hmaskR,LightMaskUnion.time,LightStageLookup.time,LightSign.time
    with right μ₄ ⟨hright,hkeepRR⟩
  have hkeepR₂ : Kept μ μ₄ work := by
    intro i hi
    exact (hkeepRR i (by omega)).trans (hkeepR₁ i hi)
  have hpBound := abs_le.mp hproduct
  light_set (SubsetStages.stageValue f stage (preL ∪ S)*SubsetStages.stageValue g stage (preR ∪ S))
    using hleft,hright,LightMaskUnion.time,LightStageLookup.time,LightSign.time
  have hsign := LightSign.meets (d := d+1) (μ := μ₄) (e := S.card) hSign hw (by omega) hproduct
  light_call hsign using LightMaskUnion.time,LightStageLookup.time,LightSign.time
    with res μ₅ ⟨hres,hmem⟩
  subst μ₅
  exact ⟨hres,hkeepR₂⟩

def program : Program :=
  [body 1 2 14,LightMaskUnion.body 10 13,LightStageLookup.body 3 4,
    LightDownsetSize.body 5 12,LightDownsetAddress.body 5 12,
    LightSubsetSetup.body 6 10 11,buildBody 7 8,fillBody,rowBody 9,
    LightArray.linearBody,powTableBody,rankBody 11,LightSubsetOffset.body,
    LightMaskErase.body 13,LightSign.body]

theorem program_procs : LightSubsetSetup.Procs program 5 6 7 8 9 10 11 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {W cut stage baseL baseR work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
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
  meets rfl rfl rfl rfl rfl rfl program_procs rfl rfl preL preR S f g hw hcut hstage
    hdataL hdataR hspace hword hproductWord hcardL hcardR hf hg hstoredL hstoredR hd

theorem time_bound (W : ℕ) : time W ≤ 7800*(W+1)^2 := by
  have hu := LightMaskUnion.time_bound W
  have ht := LightStageLookup.time_bound W
  unfold time LightSign.time
  nlinarith

end ThreeSum.LightSignedLeafGeneral
