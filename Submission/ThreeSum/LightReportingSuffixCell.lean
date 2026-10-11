import Submission.ThreeSum.ReportingHostSuffix

/-!
# A concrete box-leaf cell with global source and local box addresses

Multiplication lifts the local mask into the global suffix. The actual source
reader uses width W; a second actual compact-address computation uses width V.
Only the local compact box cell and polynomial scratch are modified.
-/

namespace ThreeSum.LightReportingSuffixCell

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open LightZetaCell ReportingHostSuffix

variable {lim : Limits} {P : Program}

def body (pLeaf pAddress : ℕ) : Stmt :=
  .set 15 (v 9 *' v 10) ;;
  .call pLeaf [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 8,v 15,v 11,v 12,v 14] 16 ;;
  .call pAddress [v 7,v 8,v 9,v 14] 17 ;;
  .store (v 13 +' v 17) (v 16)

def time (W V : ℕ) : ℕ := LightSignedLeafGeneral.time W+LightDownsetAddress.time V+90

theorem small_word {W V : ℕ} (hV : V ≤ W)
    (hw : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word) :
    (((V+1)*2^(V+1) : ℕ) : ℤ) ≤ lim.word := by
  have hm := Nat.mul_le_mul (Nat.succ_le_succ hV)
    (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.succ_le_succ hV))
  exact (by exact_mod_cast hm : (((V+1)*2^(V+1) : ℕ) : ℤ) ≤
    (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hw

theorem small_space {W V work : ℕ} (hV : V ≤ W)
    (hs : work+1+tableSize W+(W+1) ≤ lim.space) :
    work+tableSize V+(V+1) ≤ lim.space := by
  have hp := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
  change (V+1)^2 ≤ (W+1)^2 at hp
  unfold tableSize at *
  omega

theorem meets {pMain pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pLeaf pAddress)) (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage baseL baseR dst work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : Finset (Fin W)) (S : Finset (Fin V))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ work)
    (hdst : dst+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hS : S.card ≤ boxCut)
    (hcardL : (preL ∪ liftSet hfit S).card ≤ sourceCut)
    (hcardR : (preR ∪ liftSet hfit S).card ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hd : d+W+7 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,S.card,subsetMask S,2^offset,baseL,baseR,dst,work] μ (time W V)
      (fun _ μ' => μ' (dst+subsetRank S) = leafWeight hfit f g stage preL preR S ∧
        KeptExcept μ μ' work (dst+subsetRank S)) := by
  have hV : V ≤ W := by omega
  have hr := subsetRank_lt hS
  have hv : |leafWeight hfit f g stage preL preR S| ≤ lim.word :=
    (leafWeight_abs_le hfit f g preL preR S hstage hcardL hcardR hf hg).trans hproductWord
  have hvBounds := abs_le.mp hv
  have hmaskWord : ((subsetMask (liftSet hfit S) : ℕ) : ℤ) ≤ lim.word := by
    have hm : subsetMask (liftSet hfit S) ≤ (W+1)*2^(W+1) :=
      (Nat.le_of_lt (subsetMask_isMask _).1).trans
        ((Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (by omega)).trans
          (Nat.le_mul_of_pos_left _ (by omega)))
    exact (by exact_mod_cast hm : (subsetMask (liftSet hfit S) : ℤ) ≤
      (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hmaskInt : (subsetMask S : ℤ)*(2^offset : ℕ) = (subsetMask (liftSet hfit S) : ℤ) := by
    rw [liftSet_mask_int,mul_comm]
  have hmaskInt' := hmaskInt
  push_cast at hmaskInt'
  have hprodBounds : -lim.word ≤ (subsetMask S : ℤ)*(2 : ℤ)^offset ∧
      (subsetMask S : ℤ)*(2 : ℤ)^offset ≤ lim.word := by
    rw [hmaskInt']
    have hn := Int.natCast_nonneg (subsetMask (liftSet hfit S))
    omega
  apply Meets.of_body hmain
  unfold body time
  light_set (subsetMask (liftSet hfit S) : ℕ) using hmaskInt,hmaskInt',LightSignedLeafGeneral.time,LightDownsetAddress.time
  have hl := LightSignedLeafGeneral.meets (d := d+1) (μ := μ)
    C.leaf C.union C.lookup C.sign C.size C.address C.setup C.offset C.erase
    preL preR (liftSet hfit S) f g hw hcut hstage hdataL hdataR hspace hword hproductWord
    hcardL hcardR hf hg hstoredL hstoredR (by omega)
  rw [liftSet_card] at hl
  light_call hl using LightSignedLeafGeneral.time,LightDownsetAddress.time
    with value μ₁ ⟨hvalue,hkeep₁⟩
  have ha := LightDownsetAddress.meets (d := d+1) (μ := μ₁) (work := work)
    C.address C.setup C.offset hw (small_space hV hspace) (small_word hV hword)
    (subsetMask_isMask S) (by omega)
  light_call ha using LightSignedLeafGeneral.time,LightDownsetAddress.time
    with rank μ₂ ⟨hrank,hkeep₂⟩
  have hrankS : rank = (subsetRank S : ℤ) := hrank
  have hvalue' : value = leafWeight hfit f g stage preL preR S := hvalue
  light_store (dst+subsetRank S) (leafWeight hfit f g stage preL preR S)
    using hrankS,hvalue',LightSignedLeafGeneral.time,LightDownsetAddress.time
  refine ⟨by simp,?_⟩
  intro i hi hne
  change Function.update μ₂ (dst+subsetRank S) (leafWeight hfit f g stage preL preR S) i = _
  rw [Function.update_of_ne hne]
  exact (hkeep₂ i hi).trans (hkeep₁ i hi)

def program : Program := LightSignedLeafCell.program ++ [body 1 5]

def procs : LightSignedLeafCell.Procs program 1 5 where
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

theorem time_bound {W V : ℕ} (hV : V ≤ W) : time W V ≤ 9300*(W+1)^2 := by
  have hl := LightSignedLeafGeneral.time_bound W
  have ha := LightDownsetAddress.time_bound V
  have hp := Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2
  have hpos : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixCell
