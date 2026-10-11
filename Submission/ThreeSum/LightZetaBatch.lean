import Submission.ThreeSum.LightZetaCell
import Submission.ThreeSum.MaskDecode

/-!
# A compact layer pass of zeta updates

The input masks occupy an actual memory segment. Each loop iteration
loads one mask and invokes the verified compact-cell routine. The source
and mask segments are preserved, and all destination entries omitted
from the mask list retain their previous values. There is no scan of
the ambient cube in this procedure.
-/

namespace ThreeSum.LightZetaBatch

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.MaskDecode

variable {lim : Limits} {P : Program}

/-- Arguments: width, cardinality, number of masks, mask base,
coordinate, source, destination, scratch. -/
def body (pCell : ℕ) : Stmt :=
  .for 8 (v 2)
    (.call pCell [v 0,v 1,M (v 3 +' v 8),v 4,v 5,v 6,v 7] 9)

def time (L n : ℕ) : ℕ := n*(LightZetaCell.time L+40)+10

def values {L : ℕ} (μ : ℕ → ℤ) (dst : ℕ) (masks : List ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) : ℤ :=
  if subsetMask S ∈ masks then Subset.zetaStep a f S else μ (dst+subsetRank S)

def Inv {L : ℕ} (μ : ℕ → ℤ) (cut cardinal maskBase src dst work : ℕ)
    (masks : List ℕ) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cardinal,masks.length,maskBase,a.val,src,dst,work,j,r],μ'⟩ ∧
    KeptBut μ μ' work dst (downsetCap L cut) ∧
    TableAt μ' dst cut (values μ dst (masks.take j) a f)

theorem meets {pMain pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut cardinal maskBase src dst work U d : ℕ}
    (masks : List ℕ) (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+downsetCap L cut ≤ work) (hdst : dst+downsetCap L cut ≤ work)
    (hmasks : maskBase+masks.length ≤ work)
    (hsepSrc : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hsepMasks : Apart maskBase masks.length dst (downsetCap L cut))
    (hspace : work+LightPascal.tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hseg : SegN μ maskBase masks)
    (hvalid : ∀ m ∈ masks, IsMask L cardinal m) (hcardinal : cardinal ≤ cut)
    (hd : d+L+5 ≤ lim.depth) :
    Meets lim P pMain d [L,cardinal,masks.length,maskBase,a.val,src,dst,work]
      μ (time L masks.length)
      (fun _ μ' => TableAt μ' dst cut (values μ dst masks a f) ∧
        KeptBut μ μ' work dst (downsetCap L cut)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ cut cardinal maskBase src dst work masks a f)
    masks.length (LightZetaCell.time L+25) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(L : ℤ),cardinal,masks.length,maskBase,a.val,src,dst,work,0] =
        frame ([(L : ℤ),cardinal,masks.length,maskBase,a.val,src,dst,work,0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro S hS
      simp [values]
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hkept,hout⟩
    let m := masks[j]
    have hm : IsMask L cardinal m := hvalid m (List.getElem_mem hj)
    let S := decode L m
    have hScard : S.card = cardinal := by
      dsimp only [S]
      rw [decode_card hm.1,hm.2]
    have hSmask : subsetMask S = m := subsetMask_decode hm.1
    have hS : S.card ≤ cut := hScard.trans_le hcardinal
    have hrS := subsetRank_lt hS
    have hsource : TableAt μ' src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (hkept _ ⟨by omega,by omega⟩).trans (hread T hT)
    have hmaskread : μ' (maskBase+j) = (m : ℤ) := by
      exact (hkept _ ⟨by omega,by omega⟩).trans (hseg.getElem hj)
    have hcall := LightZetaCell.meets (d := d+1) hcell C hOffset hErase S a f
      hw hsrc hdst hspace hword hvalueWord hsource hvalues hS (by omega)
    rw [hScard,hSmask] at hcall
    light_call hcall using hmaskread,LightZetaCell.time with res μ'' ⟨hnew,hkeep⟩
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
        simp [values,htake,hSmask]
      · have hrne : dst+subsetRank T ≠ dst+subsetRank S := by
          intro hh
          apply heq
          exact subsetRank_injective L (Nat.add_left_cancel hh)
        have hmne : subsetMask T ≠ m := by
          intro hh
          apply heq
          exact subsetMask_injective L (hh.trans hSmask.symm)
        rw [hkeep _ (by omega) hrne,hout T hT]
        simp only [values,htake,List.mem_append,List.mem_singleton,hmne,or_false]
  case done =>
    rintro _ _ ⟨r,μ',rfl,hkept,hout⟩
    exact ⟨by simpa only [List.take_length] using hout,hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_,_⟩
    light_side

theorem values_layer {L cardinal : ℕ} (μ : ℕ → ℤ) (dst : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) :
    values μ dst (enumerateLayer L cardinal) a f S =
      if S.card = cardinal then Subset.zetaStep a f S else μ (dst+subsetRank S) := by
  have hm := subsetMask_isMask S
  simp only [values,mem_enumerateLayer,IsMask,hm.1,true_and,hm.2]

theorem time_bound (L n : ℕ) : time L n ≤ 2100*(L+1)^2*(n+1) := by
  have h := LightZetaCell.time_bound L
  have hmul := Nat.mul_le_mul_left n h
  have hpoly : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  have hsmall := Nat.mul_le_mul_left n (show 40 ≤ 100*(L+1)^2 by omega)
  unfold time
  nlinarith

end ThreeSum.LightZetaBatch
