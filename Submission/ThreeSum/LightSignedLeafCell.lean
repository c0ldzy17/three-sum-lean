import Submission.ThreeSum.LightSignedLeafGeneral

/-! # Writing one initial signed-product cell at its compact address -/

namespace ThreeSum.LightSignedLeafCell

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell

variable {lim : Limits} {P : Program}

/-- The actual leaf and address subprograms, with all of their dependencies. -/
structure Procs (P : Program) (pLeaf pAddress : ℕ) where
  (pUnion pLookup pSign pSize pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ)
  leaf : P[pLeaf]? = some (LightSignedLeafGeneral.body pUnion pLookup pSign)
  union : P[pUnion]? = some (LightMaskUnion.body pPowers pErase)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  sign : P[pSign]? = some LightSign.body
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body
  erase : P[pErase]? = some (LightMaskErase.body pErase)

/-- Width, source cutoff, suffix stage, both prefix cardinalities and masks,
leaf cardinality and mask, source bases, destination, polynomial scratch. -/
def body (pLeaf pAddress : ℕ) : Stmt :=
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 12] 13 ;;
  .call pAddress [v 0,v 7,v 8,v 12] 14 ;;
  .store (v 11 +' v 14) (v 13)

def time (W : ℕ) : ℕ := LightSignedLeafGeneral.time W+LightDownsetAddress.time W+70

theorem meets {pMain pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pLeaf pAddress)) (C : Procs P pLeaf pAddress)
    {μ : ℕ → ℤ} {W sourceCut boxCut stage baseL baseR dst work B D d : ℕ}
    (preL preR S : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ work)
    (hdst : dst+downsetCap W boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ boxCut)
    (hcardL : (preL ∪ S).card ≤ sourceCut) (hcardR : (preR ∪ S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        S.card,subsetMask S,baseL,baseR,dst,work] μ (time W)
      (fun _ μ' => μ' (dst+subsetRank S) = SignedLeaf.value f g stage preL preR S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) := by
  have hr := subsetRank_lt hS
  have hv : |SignedLeaf.value f g stage preL preR S| ≤ lim.word :=
    (SignedLeaf.abs_value_le f g stage preL preR S hstage hcardL hcardR hf hg).trans hproductWord
  have hvBounds := abs_le.mp hv
  apply Meets.of_body hmain
  unfold body time
  have hl := LightSignedLeafGeneral.meets (d := d+1) (μ := μ)
    C.leaf C.union C.lookup C.sign C.size C.address C.setup C.offset C.erase
    preL preR S f g hw hcut hstage hdataL hdataR hspace hword hproductWord
    hcardL hcardR hf hg hstoredL hstoredR (by omega)
  light_call hl using LightSignedLeafGeneral.time,LightDownsetAddress.time
    with value μ₁ ⟨hvalue,hkeep₁⟩
  have ha := LightDownsetAddress.meets (d := d+1) (μ := μ₁) (work := work)
    C.address C.setup C.offset hw (by omega) hword (subsetMask_isMask S) (by omega)
  light_call ha using LightSignedLeafGeneral.time,LightDownsetAddress.time
    with rank μ₂ ⟨hrank,hkeep₂⟩
  have hrankS : rank = (subsetRank S : ℤ) := hrank
  light_store (dst+subsetRank S) (SignedLeaf.value f g stage preL preR S)
    using hrankS,hvalue,LightSignedLeafGeneral.time,LightDownsetAddress.time
  refine ⟨by simp,?_⟩
  intro i hi hne
  change Function.update μ₂ (dst+subsetRank S) (SignedLeaf.value f g stage preL preR S) i = _
  rw [Function.update_of_ne hne]
  exact (hkeep₂ i hi).trans (hkeep₁ i hi)

def program : Program :=
  [body 1 5,LightSignedLeafGeneral.body 2 3 15,LightMaskUnion.body 11 14,
    LightStageLookup.body 4 5,LightDownsetSize.body 6 13,LightDownsetAddress.body 6 13,
    LightSubsetSetup.body 7 11 12,buildBody 8 9,fillBody,rowBody 10,
    LightArray.linearBody,powTableBody,rankBody 12,LightSubsetOffset.body,
    LightMaskErase.body 14,LightSign.body]

def procs : Procs program 1 5 where
  pUnion := 2
  pLookup := 3
  pSign := 15
  pSize := 4
  pSetup := 6
  pBuild := 7
  pFill := 8
  pRow := 9
  pLinear := 10
  pPowers := 11
  pRank := 12
  pOffset := 13
  pErase := 14
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl

theorem time_bound (W : ℕ) : time W ≤ 9300*(W+1)^2 := by
  have hl := LightSignedLeafGeneral.time_bound W
  have ha := LightDownsetAddress.time_bound W
  have hp : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  unfold time
  omega

end ThreeSum.LightSignedLeafCell
