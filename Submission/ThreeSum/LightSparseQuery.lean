import Submission.ThreeSum.LightExplicitSum
import Submission.ThreeSum.LightCanonicalBoxSum

/-!
# A complete sparse Möbius query in the benchmark language

The fixed program constructs every missing-mask layer it uses, evaluates
explicit leaves through source-stage reads, evaluates canonical boxes
through their compact stored stages, adds both contributions, and applies
the outer sign. The exact partition identity proves the resulting Möbius
value. No enumeration, leaf-value, or query-value oracle is assumed.
-/

namespace ThreeSum.LightSparseQuery

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open scoped BigOperators

variable {lim : Limits} {P : Program}

def queryItems (c t : ℕ) : ℕ := layerOffset c t+c.choose t

def magnitudeBound (W stage c t B D : ℕ) : ℕ :=
  (queryItems c t+1)*(2^W*((2^stage*B)*(2^stage*D)))

/-- Width, source cutoff, suffix stage, two prefixes, query cardinality and
mask, missing threshold, two source bases, box cutoff and base, mask buffer,
and polynomial scratch. -/
def body (pExplicit pBoxes pSign : ℕ) : Stmt :=
  .call pExplicit [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 14,v 15] 16 ;;
  .call pBoxes [v 0,v 12,v 7,v 8,v 9,v 13,v 14,v 15] 17 ;;
  .set 18 (v 16 +' v 17) ;;
  .call pSign [v 18,v 7] 0

def time (W c t : ℕ) : ℕ :=
  LightExplicitSum.time W c t+LightCanonicalBoxSum.time W c t+LightSign.time W+80

theorem meets {pMain pExplicit pBoxes pSign pEnum pLeafSum pBoxSum : ℕ}
    (hmain : P[pMain]? = some (body pExplicit pBoxes pSign))
    (hExplicit : P[pExplicit]? = some (LightExplicitSum.body pEnum pLeafSum))
    (hBoxes : P[pBoxes]? = some (LightCanonicalBoxSum.body pEnum pBoxSum))
    (hSign : P[pSign]? = some LightSign.body)
    (CE : LightExplicitSum.Procs P pEnum pLeafSum)
    (CB : LightCanonicalBoxSum.Procs P pEnum pBoxSum)
    {μ : ℕ → ℤ} {W cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(W+1)*downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+queryItems Q.card t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (magnitudeBound W stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (SignedLeaf.value f g stage preL preR) W)
    (hd : d+W+9 ≤ lim.depth) :
    Meets lim P pMain d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,baseL,baseR,boxCut,boxBase,maskBase,work] μ (time W Q.card t)
      (fun r μ' =>
        r = Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
          SubsetStages.stageValue g stage (preR ∪ S)) Q ∧
        KeptBut μ μ' work maskBase (queryItems Q.card t)) := by
  have hQcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hboxW : boxCut ≤ W := hboxCut.trans hQcard
  have hoff : layerOffset Q.card t ≤ queryItems Q.card t := by unfold queryItems; omega
  have hchoose : Q.card.choose t ≤ queryItems Q.card t := by unfold queryItems; omega
  have hpow : 1 ≤ (2^W : ℕ) := Nat.one_le_pow' W 1
  have hproduct : (2^stage*B)*(2^stage*D) ≤ 2^W*((2^stage*B)*(2^stage*D)) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos W)
  have hfullBound : 2^W*((2^stage*B)*(2^stage*D)) ≤ magnitudeBound W stage Q.card t B D :=
    Nat.le_mul_of_pos_left _ (by unfold queryItems; omega)
  have heBound : (layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) ≤
      magnitudeBound W stage Q.card t B D :=
    Nat.mul_le_mul (Nat.succ_le_succ hoff) hproduct
  have hbBound : Q.card.choose t*(2^W*((2^stage*B)*(2^stage*D))) ≤
      magnitudeBound W stage Q.card t B D :=
    Nat.mul_le_mul_right _ (hchoose.trans (Nat.le_succ _))
  have hExplicitWord : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast heBound : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
      (magnitudeBound W stage Q.card t B D : ℤ)).trans hvalueWord
  have hBoxWord : ((Q.card.choose t*(2^W*((2^stage*B)*(2^stage*D))) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbBound : ((Q.card.choose t*(2^W*((2^stage*B)*(2^stage*D))) : ℕ) : ℤ) ≤
      (magnitudeBound W stage Q.card t B D : ℤ)).trans hvalueWord
  have hCL : preL.card+Q.card ≤ cut := by rwa [Finset.card_union_of_disjoint hdisjL] at hcardL
  have hCR : preR.card+Q.card ≤ cut := by rwa [Finset.card_union_of_disjoint hdisjR] at hcardR
  have hweight (S : Finset (Fin W)) (hS : S.card ≤ Q.card) :
      |SignedLeaf.value f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    apply SignedLeaf.abs_value_le (cut := cut) f g stage preL preR S hstage
    · exact (Finset.card_union_le preL S).trans (by omega)
    · exact (Finset.card_union_le preR S).trans (by omega)
    · exact hf
    · exact hg
  have htotal : |∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S| ≤ lim.word := by
    have hs : |∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S| ≤
        ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by
      calc
        _ ≤ ∑ S ∈ Q.powerset, |SignedLeaf.value f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _S ∈ Q.powerset, (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
          Finset.sum_le_sum fun S hS => hweight S (Finset.card_le_card (Finset.mem_powerset.mp hS))
        _ = _ := by simp [Nat.cast_mul]
    have hn : 2^Q.card*((2^stage*B)*(2^stage*D)) ≤ magnitudeBound W stage Q.card t B D :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hQcard)).trans hfullBound
    have hz : ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
        (magnitudeBound W stage Q.card t B D : ℤ) := by exact_mod_cast hn
    exact hs.trans (hz.trans hvalueWord)
  apply Meets.of_body hmain
  unfold body time
  have he := LightExplicitSum.meets (d := d+1) (μ := μ) (t := t)
    (baseL := baseL) (baseR := baseR) (maskBase := maskBase) (work := work)
    hExplicit CE Q preL preR f g hw hcut hstage hdataL hdataR (by omega) hspace hword hExplicitWord ht
    hdisjL hdisjR hcardL hcardR hf hg hstoredL hstoredR (by omega)
  light_call he with explicit μ₁ ⟨heValue,hkeepE⟩
  have hstoredBox₁ : LightBoxStages.StoredThrough μ₁ boxBase boxCut
      (SignedLeaf.value f g stage preL preR) W := by
    intro j hj S hS
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap W boxCut) (Nat.succ_le_succ hj)
    have ha : LightBoxStages.stageBase boxBase (downsetCap W boxCut) j+subsetRank S < maskBase := by
      unfold LightBoxStages.stageBase
      simp only [Nat.succ_mul] at hm hdataBox
      omega
    exact (hkeepE _ ⟨by omega,Or.inl ha⟩).trans (hstoredBox j hj S hS)
  have hb := LightCanonicalBoxSum.meets (d := d+1) (μ := μ₁) (t := t)
    (base := boxBase) (maskBase := maskBase) (work := work)
    hBoxes CB Q (SignedLeaf.value f g stage preL preR) hw hboxW hdataBox (by omega) hspace hword hBoxWord
    ht hflags (fun S hS => hweight S (hS.trans hboxCut)) hstoredBox₁ (by omega)
  light_call hb with boxes μ₂ ⟨hbValue,hkeepB⟩
  have hsum : explicit+boxes = ∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S := by
    rw [heValue,hbValue]
    exact (ExplicitLayers.sparse_identity Q (SignedLeaf.value f g stage preL preR) t).symm
  have htotalSides := abs_le.mp htotal
  light_set (∑ S ∈ Q.powerset, SignedLeaf.value f g stage preL preR S) using hsum
  have hs := LightSign.meets (d := d+1) (μ := μ₂) (e := Q.card) hSign hw (by omega) htotal
  light_call hs using LightSign.time with res μ₃ ⟨hres,hmem⟩
  subst μ₃
  refine ⟨hres.trans (SignedLeaf.mobius_eq_signed_sum f g stage preL preR Q).symm,?_⟩
  intro i hi
  exact (hkeepB i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩).trans
    (hkeepE i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩)

def program : Program :=
  [body 1 2 22,LightExplicitSum.body 3 6,LightCanonicalBoxSum.body 3 7,
    LightQueryEnumeration.body 4 5,LightQueryWeights.body 17 20,LightSubsetEnumeration.body 5,
    LightLeafSum.body 8,LightBoxSum.body 9,LightSignedLeaf.body 10 22,
    LightQueryBox.body 11 10,LightStageLookup.body 12 13,LightMaskMinimum.body 17 20,
    LightDownsetSize.body 14 19,LightDownsetAddress.body 14 19,LightSubsetSetup.body 15 17 18,
    buildBody 16 21,fillBody,powTableBody,rankBody 18,LightSubsetOffset.body,
    LightMaskErase.body 20,rowBody 23,LightSign.body,LightArray.linearBody]

def explicitProcs : LightExplicitSum.Procs program 3 6 where
  pWeights := 4
  pPowers := 17
  pErase := 20
  pCore := 5
  pLeaf := 8
  pLookup := 10
  pSign := 22
  pSize := 12
  pAddress := 13
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pRank := 18
  pOffset := 19
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

def boxProcs : LightCanonicalBoxSum.Procs program 3 7 where
  pWeights := 4
  pPowers := 17
  pErase := 20
  pCore := 5
  pBox := 9
  pMinimum := 11
  pLookup := 10
  pSize := 12
  pAddress := 13
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pRank := 18
  pOffset := 19
  enumerate := rfl
  weights := rfl
  erase := rfl
  core := rfl
  sum := rfl
  box := rfl
  minimum := rfl
  lookup := rfl
  size := rfl
  address := rfl
  table := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl

theorem program_meets    {μ : ℕ → ℤ} {W cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (Q preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(W+1)*downsetCap W boxCut ≤ maskBase)
    (hmasks : maskBase+queryItems Q.card t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (magnitudeBound W stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL Q) (hdisjR : Disjoint preR Q)
    (hcardL : (preL ∪ Q).card ≤ cut) (hcardR : (preR ∪ Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (SignedLeaf.value f g stage preL preR) W)
    (hd : d+W+9 ≤ lim.depth) :
    Meets lim program 0 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,Q.card,subsetMask Q,
        t,baseL,baseR,boxCut,boxBase,maskBase,work] μ (time W Q.card t)
      (fun r μ' =>
        r = Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
          SubsetStages.stageValue g stage (preR ∪ S)) Q ∧
        KeptBut μ μ' work maskBase (queryItems Q.card t)) :=
  meets rfl rfl rfl rfl explicitProcs boxProcs Q preL preR f g hw hcut hstage
    hdataL hdataR hdataBox hmasks hspace hword hvalueWord ht hboxCut hflags hdisjL hdisjR
    hcardL hcardR hf hg hstoredL hstoredR hstoredBox hd

theorem time_bound {W c t : ℕ} (hc : c ≤ W) (ht : t ≤ c+1) :
    time W c t ≤ 14000*(W+1)^3*(queryItems c t+1) := by
  have he := LightExplicitSum.time_bound (c := c) (by omega : t ≤ W+1)
  have hb := LightCanonicalBoxSum.time_bound (t := t) hc
  have ho : layerOffset c t+1 ≤ queryItems c t+1 := by unfold queryItems; omega
  have hh : c.choose t+1 ≤ queryItems c t+1 := by unfold queryItems; omega
  have hp : (W+1)^2 ≤ (W+1)^3 := by nlinarith
  have he' := he.trans (Nat.mul_le_mul_left (8200*(W+1)^3) ho)
  have hb' := hb.trans (Nat.mul_le_mul (Nat.mul_le_mul_left 5200 hp) hh)
  have hpos : 1 ≤ queryItems c t+1 := by omega
  unfold time LightSign.time
  nlinarith

end ThreeSum.LightSparseQuery
