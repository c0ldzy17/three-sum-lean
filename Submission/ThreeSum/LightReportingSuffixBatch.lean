import Submission.ThreeSum.LightReportingSuffixCell

/-! # Evaluating one locally enumerated suffix layer against global source tables -/

namespace ThreeSum.LightReportingSuffixBatch

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell ThreeSum.MaskDecode
open ReportingHostSuffix

variable {lim : Limits} {P : Program}

def body (pCell : ℕ) : Stmt :=
  .for 16 (v 10)
    (.call pCell [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 9,M (v 11 +' v 16),
      v 8,v 12,v 13,v 14,v 15] 17)

def time (W V n : ℕ) : ℕ := n*(LightReportingSuffixCell.time W V+65)+20

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (μ : ℕ → ℤ)
    (sourceCut boxCut stage cardinal maskBase baseL baseR dst work : ℕ)
    (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
      V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work,j,r],μ'⟩ ∧
    KeptBut μ μ' work dst (downsetCap V boxCut) ∧
    TableAt μ' dst boxCut
      (LightSignedLeafBatch.values μ dst (masks.take j) (leafWeight hfit f g stage preL preR))

theorem meets {pMain pCell pLeaf pAddress : ℕ}
    (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightReportingSuffixCell.body pLeaf pAddress))
    (C : LightSignedLeafCell.Procs P pLeaf pAddress)
    {μ : ℕ → ℤ} {W V offset sourceCut boxCut stage cardinal maskBase baseL baseR dst work B D d : ℕ}
    (hfit : offset+V ≤ W) (masks : List ℕ) (preL preR : Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : sourceCut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W sourceCut ≤ work)
    (hdataR : baseR+(W+1)*downsetCap W sourceCut ≤ work)
    (hdst : dst+downsetCap V boxCut ≤ work) (hmasks : maskBase+masks.length ≤ work)
    (hsepL : Apart baseL ((W+1)*downsetCap W sourceCut) dst (downsetCap V boxCut))
    (hsepR : Apart baseR ((W+1)*downsetCap W sourceCut) dst (downsetCap V boxCut))
    (hsepMasks : Apart maskBase masks.length dst (downsetCap V boxCut))
    (hspace : work+1+LightPascal.tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hproductWord : (((2^stage*B)*(2^stage*D) : ℕ) : ℤ) ≤ lim.word)
    (hpreL : preL.card+boxCut ≤ sourceCut) (hpreR : preR.card+boxCut ≤ sourceCut)
    (hf : ∀ T, T.card ≤ sourceCut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ sourceCut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL sourceCut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR sourceCut g W)
    (hseg : SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, IsMask V cardinal m) (hcardinal : cardinal ≤ boxCut)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim P pMain d
      [W,sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work] μ (time W V masks.length)
      (fun _ μ' => TableAt μ' dst boxCut
        (LightSignedLeafBatch.values μ dst masks (leafWeight hfit f g stage preL preR)) ∧
        KeptBut μ μ' work dst (downsetCap V boxCut)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv hfit μ sourceCut boxCut stage cardinal maskBase baseL baseR dst work masks preL preR f g)
    masks.length (LightReportingSuffixCell.time W V+50) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(W : ℤ),sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
        V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work,0] =
        frame ([(W : ℤ),sourceCut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,
          V,2^offset,cardinal,masks.length,maskBase,baseL,baseR,dst,work,0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro S hS
      simp [LightSignedLeafBatch.values]
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hkept,hout⟩
    let m := masks[j]
    have hm : IsMask V cardinal m := hvalid m (List.getElem_mem hj)
    let S := decode V m
    have hScard : S.card = cardinal := by
      dsimp only [S]
      rw [decode_card hm.1,hm.2]
    have hSmask : subsetMask S = m := subsetMask_decode hm.1
    have hS : S.card ≤ boxCut := hScard.trans_le hcardinal
    have hrS := subsetRank_lt hS
    have hL : (preL ∪ liftSet hfit S).card ≤ sourceCut := by
      have he := Finset.card_union_le preL (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreL)
    have hR : (preR ∪ liftSet hfit S).card ≤ sourceCut := by
      have he := Finset.card_union_le preR (liftSet hfit S)
      rw [liftSet_card] at he
      exact he.trans ((Nat.add_le_add_left hS _).trans hpreR)
    have hsourceL : LightZetaStages.StoredThrough μ' baseL sourceCut f W :=
      LightSignedLeafBatch.storedThrough_of_on hstoredL (by
        intro i hi₀ hi₁
        exact hkept i ⟨by omega,by omega⟩)
    have hsourceR : LightZetaStages.StoredThrough μ' baseR sourceCut g W :=
      LightSignedLeafBatch.storedThrough_of_on hstoredR (by
        intro i hi₀ hi₁
        exact hkept i ⟨by omega,by omega⟩)
    have hmaskread : μ' (maskBase+j) = (m : ℤ) :=
      (hkept _ ⟨by omega,by omega⟩).trans (hseg.getElem hj)
    have hc := LightReportingSuffixCell.meets (d := d+1) hcell C hfit preL preR S f g
      hw hcut hstage hdataL hdataR hdst hspace hword hproductWord hS hL hR
      hf hg hsourceL hsourceR (by omega)
    rw [hScard,hSmask] at hc
    light_call hc using hmaskread,LightReportingSuffixCell.time with res μ'' ⟨hnew,hkeep⟩
    refine ⟨by simp,res,μ'',?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hkeep i hi.1 (by omega)).trans (hkept i hi)
    · intro T hT
      have hrT := subsetRank_lt hT
      have htake : masks.take (j+1) = masks.take j ++ [m] := by
        simpa only [m] using List.take_succ_eq_append_getElem (l := masks) hj
      by_cases heq : T = S
      · subst T
        rw [hnew]
        simp [LightSignedLeafBatch.values,htake,hSmask]
      · have hrne : dst+subsetRank T ≠ dst+subsetRank S := by
          intro hh
          exact heq (subsetRank_injective V (Nat.add_left_cancel hh))
        have hmne : subsetMask T ≠ m := by
          intro hh
          exact heq (subsetMask_injective V (hh.trans hSmask.symm))
        rw [hkeep _ (by omega) hrne,hout T hT]
        simp only [LightSignedLeafBatch.values,htake,List.mem_append,List.mem_singleton,hmne,or_false]
  case done =>
    rintro _ _ ⟨r,μ',rfl,hkept,hout⟩
    exact ⟨by simpa only [List.take_length] using hout,hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_,_⟩
    light_side

theorem time_bound {W V : ℕ} (hV : V ≤ W) (n : ℕ) :
    time W V n ≤ 9400*(W+1)^2*(n+1) := by
  have h := LightReportingSuffixCell.time_bound hV
  have hmul := Nat.mul_le_mul_left n h
  have hpoly : 1 ≤ (W+1)^2 := Nat.one_le_pow' 2 W
  have hsmall := Nat.mul_le_mul_left n (show 65 ≤ 100*(W+1)^2 by omega)
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixBatch
