import Submission.ThreeSum.LightReportingSuffixExplicit
import Submission.ThreeSum.ReportingHostQueryBounds

/-!
# The complete sparse query consumes suffix-local box tables

Explicit leaves use local output-sensitive enumeration and global source
reads; canonical boxes use only local-width compact addresses. The exact
finite partition yields the same global source Möbius value.
-/

namespace ThreeSum.LightReportingSuffixQuery

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix
open scoped BigOperators

variable {lim : Limits}

def body (pExplicit pBoxes pSign : ℕ) : Stmt :=
  .call pExplicit [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 16,v 17] 18 ;;
  .call pBoxes [v 7,v 14,v 9,v 10,v 11,v 15,v 16,v 17] 19 ;;
  .set 20 (v 18 +' v 19) ;;
  .call pSign [v 20,v 9] 0

def program : Program := LightSparseQuery.program ++
  [LightMaskUnion.body 17 20,LightSignedLeafGeneral.body 24 10 22,
    LightReportingSuffixSum.body 25,LightReportingSuffixExplicit.body 3 26,body 27 2 22]

def leafProcs : LightSignedLeafCell.Procs program 25 13 where
  pUnion := 24
  pLookup := 10
  pSign := 22
  pSize := 12
  pSetup := 14
  pBuild := 15
  pFill := 16
  pRow := 21
  pLinear := 23
  pPowers := 17
  pRank := 18
  pOffset := 19
  pErase := 20
  leaf := rfl
  union := rfl
  lookup := rfl
  sign := rfl
  size := rfl
  address := rfl
  setup := ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  offset := rfl
  erase := rfl

def explicitProcs : LightReportingSuffixExplicit.Procs program 3 26 :=
  ⟨4,5,25,13,leafProcs,rfl,rfl,rfl,rfl⟩

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

def time (W V c t : ℕ) : ℕ :=
  LightReportingSuffixExplicit.time W c t+LightCanonicalBoxSum.time V c t+LightSign.time V+90

theorem program_meets
    {μ : ℕ → ℤ} {W V offset cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(V+1)*downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems Q.card t ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL (liftSet hfit Q)) (hdisjR : Disjoint preR (liftSet hfit Q))
    (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (leafWeight hfit f g stage preL preR) V)
    (hd : d+W+9 ≤ lim.depth) :
    Meets lim program 28 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,2^offset,
        Q.card,subsetMask Q,t,baseL,baseR,boxCut,boxBase,maskBase,work] μ (time W V Q.card t)
      (fun r μ' =>
        r = Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
          SubsetStages.stageValue g stage (preR ∪ S)) (liftSet hfit Q) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems Q.card t)) := by
  have hV : V ≤ W := by omega
  have hQcard : Q.card ≤ V := by simpa using Finset.card_le_univ Q
  have hboxV : boxCut ≤ V := hboxCut.trans hQcard
  have hoff : layerOffset Q.card t ≤ LightSparseQuery.queryItems Q.card t := by
    unfold LightSparseQuery.queryItems; omega
  have hchoose : Q.card.choose t ≤ LightSparseQuery.queryItems Q.card t := by
    unfold LightSparseQuery.queryItems; omega
  have hproduct : (2^stage*B)*(2^stage*D) ≤ 2^V*((2^stage*B)*(2^stage*D)) :=
    Nat.le_mul_of_pos_left _ (Nat.two_pow_pos V)
  have hfullBound : 2^V*((2^stage*B)*(2^stage*D)) ≤ LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.le_mul_of_pos_left _ (by unfold LightSparseQuery.queryItems; omega)
  have heBound : (layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) ≤
      LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.mul_le_mul (Nat.succ_le_succ hoff) hproduct
  have hbBound : Q.card.choose t*(2^V*((2^stage*B)*(2^stage*D))) ≤
      LightSparseQuery.magnitudeBound V stage Q.card t B D :=
    Nat.mul_le_mul_right _ (hchoose.trans (Nat.le_succ _))
  have hExplicitWord : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast heBound : (((layerOffset Q.card t+1)*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
      (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ)).trans hvalueWord
  have hBoxWord : ((Q.card.choose t*(2^V*((2^stage*B)*(2^stage*D))) : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbBound : ((Q.card.choose t*(2^V*((2^stage*B)*(2^stage*D))) : ℕ) : ℤ) ≤
      (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ)).trans hvalueWord
  have hCL : preL.card+Q.card ≤ cut := by
    simpa only [Finset.card_union_of_disjoint hdisjL,liftSet_card] using hcardL
  have hCR : preR.card+Q.card ≤ cut := by
    simpa only [Finset.card_union_of_disjoint hdisjR,liftSet_card] using hcardR
  have hweight (S : Finset (Fin V)) (hS : S.card ≤ Q.card) :
      |leafWeight hfit f g stage preL preR S| ≤ (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) := by
    apply leafWeight_abs_le (sourceCut := cut) hfit f g preL preR S hstage
    · have he := Finset.card_union_le preL (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans (by omega)
    · have he := Finset.card_union_le preR (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans (by omega)
    · exact hf
    · exact hg
  have htotal : |∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S| ≤ lim.word := by
    have hs : |∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S| ≤
        ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) := by
      calc
        _ ≤ ∑ S ∈ Q.powerset, |leafWeight hfit f g stage preL preR S| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _S ∈ Q.powerset, (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) :=
          Finset.sum_le_sum fun S hS => hweight S (Finset.card_le_card (Finset.mem_powerset.mp hS))
        _ = _ := by simp [Nat.cast_mul]
    have hn : 2^Q.card*((2^stage*B)*(2^stage*D)) ≤ LightSparseQuery.magnitudeBound V stage Q.card t B D :=
      (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hQcard)).trans hfullBound
    have hz : ((2^Q.card*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤
        (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) := by exact_mod_cast hn
    exact hs.trans (hz.trans hvalueWord)
  apply Meets.of_body (p := 28) (by rfl : program[28]? = some (body 27 2 22))
  unfold body time
  have he := LightReportingSuffixExplicit.meets (P := program) (pMain := 27) (d := d+1) (μ := μ) (t := t)
    (baseL := baseL) (baseR := baseR) (maskBase := maskBase) (work := work)
    rfl explicitProcs hfit Q preL preR f g hw hcut hstage hdataL hdataR (by omega) hspace hword
    hExplicitWord ht hcardL hcardR hf hg hstoredL hstoredR (by omega)
  light_call he with explicit μ₁ ⟨heValue,hkeepE⟩
  have hstoredBox₁ := ReportingHostQueryBounds.boxStored_of_on hstoredBox (by
    intro i _ hi
    have ha := hi.trans_le hdataBox
    exact hkeepE i ⟨by omega,Or.inl ha⟩)
  have hb := LightCanonicalBoxSum.meets (P := program) (pMain := 2) (d := d+1) (μ := μ₁) (t := t)
    (base := boxBase) (maskBase := maskBase) (work := work)
    rfl boxProcs Q (leafWeight hfit f g stage preL preR) hw hboxV hdataBox (by omega)
    (LightReportingSuffixCell.small_space hV hspace) (LightReportingSuffixCell.small_word hV hword)
    hBoxWord ht hflags (fun S hS => hweight S (hS.trans hboxCut)) hstoredBox₁ (by omega)
  light_call hb with boxes μ₂ ⟨hbValue,hkeepB⟩
  have hsum : explicit+boxes = ∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S := by
    rw [heValue,hbValue]
    exact (ExplicitLayers.sparse_identity Q (leafWeight hfit f g stage preL preR) t).symm
  have htotalSides := abs_le.mp htotal
  light_set (∑ S ∈ Q.powerset, leafWeight hfit f g stage preL preR S) using hsum
  have hs := LightSign.meets (P := program) (pMain := 22) (d := d+1) (μ := μ₂)
    (e := Q.card) rfl hw (by omega) htotal
  light_call hs using LightSign.time with res μ₃ ⟨hres,hmem⟩
  subst μ₃
  refine ⟨hres.trans (query_eq_local_signed_sum hfit f g stage preL preR Q).symm,?_⟩
  intro i hi
  exact (hkeepB i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩).trans
    (hkeepE i ⟨hi.1,by rcases hi.2 with h | h <;> omega⟩)

theorem time_bound {W V c t : ℕ} (hV : V ≤ W) (hc : c ≤ V) (ht : t ≤ c+1) :
    time W V c t ≤ 17000*(W+1)^3*(LightSparseQuery.queryItems c t+1) := by
  have he := LightReportingSuffixExplicit.time_bound (c := c) (by omega : t ≤ W+1)
  have hb := LightCanonicalBoxSum.time_bound (t := t) hc
  have h₂₃ : (V+1)^2 ≤ (W+1)^3 :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2).trans
      (Nat.pow_le_pow_right (by omega) (by omega))
  have ho : layerOffset c t+1 ≤ LightSparseQuery.queryItems c t+1 := by unfold LightSparseQuery.queryItems; omega
  have hh : c.choose t+1 ≤ LightSparseQuery.queryItems c t+1 := by unfold LightSparseQuery.queryItems; omega
  have he' := Nat.mul_le_mul_left (11000*(W+1)^3) ho
  have hb' := Nat.mul_le_mul (Nat.mul_le_mul_left 5200 h₂₃) hh
  have hpos : 1 ≤ (W+1)^3*(LightSparseQuery.queryItems c t+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hlin : V+1 ≤ (W+1)^3 := (Nat.succ_le_succ hV).trans
    (by simpa using (Nat.pow_le_pow_right (by omega : 1 ≤ W+1) (by decide : 1 ≤ 3)))
  have hm := Nat.le_mul_of_pos_right ((W+1)^3) (by omega : 0 < LightSparseQuery.queryItems c t+1)
  unfold time LightSign.time
  nlinarith

end ThreeSum.LightReportingSuffixQuery
