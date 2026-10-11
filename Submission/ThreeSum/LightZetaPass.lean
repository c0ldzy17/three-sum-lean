import Submission.ThreeSum.LightZetaBatch
import Submission.ThreeSum.LightSubsetEnumerationSetup

/-!
# A complete coordinate pass over a compact downset

For each stored cardinality the fixed procedure constructs its layer of
masks, then runs the compact-cell update on that layer. Only the compact
downset and polynomial workspace are allocated; the program never visits
all integers below `2^L`. The source table remains unchanged throughout
the pass.
-/

namespace ThreeSum.LightZetaPass

open Light ThreeSum.SubsetAddress ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def enumBudget (L cut : ℕ) : ℕ := 800*(L+1)*(downsetCap L cut+1)
def batchBudget (L cut : ℕ) : ℕ := 2100*(L+1)^2*(downsetCap L cut+1)
def roundBudget (L cut : ℕ) : ℕ := enumBudget L cut+batchBudget L cut+60

theorem choose_le_cap {L cut j : ℕ} (hcut : cut ≤ L) (hj : j ≤ cut) :
    L.choose j ≤ downsetCap L cut := by
  have ho := layerOffset_mono L (show j+1 ≤ min cut L+1 by omega)
  rw [layerOffset_succ] at ho
  unfold downsetCap
  omega

def roundBody (pEnumSetup pBatch : ℕ) : Stmt :=
  .call pEnumSetup [v 0,v 7,v 5,v 6] 8 ;;
  .call pBatch [v 0,v 7,v 8,v 5,v 2,v 3,v 4,v 6] 9

/-- Arguments: width, cutoff, coordinate, source, destination,
mask workspace, polynomial workspace. -/
def body (pEnumSetup pBatch : ℕ) : Stmt :=
  .for 7 (v 1 +' k 1) (roundBody pEnumSetup pBatch)

def time (L cut : ℕ) : ℕ := (cut+1)*(roundBudget L cut+20)+20

def stageValues {L : ℕ} (μ : ℕ → ℤ) (dst j : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (S : Finset (Fin L)) : ℤ :=
  if S.card < j then Subset.zetaStep a f S else μ (dst+subsetRank S)

def Inv {L : ℕ} (μ : ℕ → ℤ) (cut src dst maskBase work : ℕ)
    (a : Fin L) (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (n r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,a.val,src,dst,maskBase,work,j,n,r],μ'⟩ ∧
    KeptBut μ μ' maskBase dst (downsetCap L cut) ∧
    TableAt μ' dst cut (stageValues μ dst j a f)

theorem meets
    {pMain pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ}
    (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hcut : cut ≤ L)
    (hsrc : src+downsetCap L cut ≤ maskBase) (hdst : dst+downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hsep : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,a.val,src,dst,maskBase,work] μ (time L cut)
      (fun _ μ' => TableAt μ' dst cut (Subset.zetaStep a f) ∧
        KeptBut μ μ' maskBase dst (downsetCap L cut)) := by
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ cut src dst maskBase work a f)
    (cut+1) (roundBudget L cut) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0,0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(L : ℤ),cut,a.val,src,dst,maskBase,work,0] =
        frame ([(L : ℤ),cut,a.val,src,dst,maskBase,work,0] ++ [0,0])
      exact (frame_append_zeros _ 2).symm
    · intro S hS
      simp [stageValues]
  case round =>
    rintro j _ hj _ ⟨n,r,μ',rfl,hkept,hout⟩
    have hjcut : j ≤ cut := by omega
    have hchoose := choose_le_cap hcut hjcut
    have hsource : TableAt μ' src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (hkept _ ⟨by omega,by omega⟩).trans (hread T hT)
    have hen := LightSubsetEnumerationSetup.meets (d := d+1) hEnumSetup C.powers hEnum
      (μ := μ') (L := L) (k := j) (dst := maskBase) (work := work)
      hw (by omega) hword₀ (by omega) (by omega) (by omega)
    have hentime : LightSubsetEnumerationSetup.time L j ≤ enumBudget L cut := by
      exact (LightSubsetEnumerationSetup.time_bound L j).trans
        (Nat.mul_le_mul_left (800*(L+1)) (Nat.succ_le_succ hchoose))
    unfold roundBody roundBudget
    light_call (hen.mono_time hentime) using enumBudget,batchBudget
      with count μ₁ ⟨hcount,hseg,hpowers,henkept⟩
    have hsource₁ : TableAt μ₁ src cut f := by
      intro T hT
      have hr := subsetRank_lt hT
      exact (henkept _ ⟨by omega,Or.inl (by omega)⟩).trans (hsource T hT)
    have hb := LightZetaBatch.meets (d := d+1) hBatch hCell C hOffset hErase
      (enumerateLayer L j) a f hw (by omega) (by omega)
      (by rw [enumerateLayer_length]; omega) hsep
      (Or.inr hdst) hspace hword hvalueWord hsource₁ hvalues hseg
      (fun m hm => (mem_enumerateLayer L j m).mp hm) hjcut (by omega)
    have hbtime : LightZetaBatch.time L (enumerateLayer L j).length ≤ batchBudget L cut := by
      rw [enumerateLayer_length]
      exact (LightZetaBatch.time_bound L (L.choose j)).trans
        (Nat.mul_le_mul_left (2100*(L+1)^2) (Nat.succ_le_succ hchoose))
    light_call (hb.mono_time hbtime) using hcount,enumerateLayer_length,enumBudget,batchBudget
      with res μ₂ ⟨hnew,hbkept⟩
    refine ⟨by simp,count,res,μ₂,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      exact (hbkept i ⟨by omega,hi.2⟩).trans
        ((henkept i ⟨by omega,Or.inl hi.1⟩).trans (hkept i hi))
    · intro T hT
      have hr := subsetRank_lt hT
      have hn := hnew T hT
      rw [LightZetaBatch.values_layer] at hn
      have hbefore : μ₁ (dst+subsetRank T) = μ' (dst+subsetRank T) :=
        henkept _ ⟨by omega,Or.inl (by omega)⟩
      by_cases heq : T.card = j
      · have hlt : T.card < j+1 := by omega
        simpa only [stageValues,heq,ite_true,show j < j+1 by omega] using hn
      · rw [if_neg heq,hbefore,hout T hT] at hn
        have hlt : T.card < j+1 ↔ T.card < j := by omega
        simpa only [stageValues,hlt] using hn
  case done =>
    rintro _ _ ⟨n,r,μ',rfl,hkept,hout⟩
    refine ⟨?_,hkept⟩
    intro T hT
    simpa only [stageValues,show T.card < cut+1 by omega,ite_true] using hout T hT
  case bound =>
    rintro j _ hj _ ⟨n,r,μ',rfl,_,_⟩
    light_side

def program : Program :=
  [body 1 2,LightSubsetEnumerationSetup.body 9 13,LightZetaBatch.body 3,
    LightZetaCell.body 4 11 12 10,LightSubsetSetup.body 5 9 10,
    buildBody 6 7,fillBody,rowBody 8,LightArray.linearBody,powTableBody,
    rankBody 10,LightSubsetOffset.body,LightMaskErase.body 12,LightSubsetEnumeration.body 13]

theorem program_procs : LightSubsetSetup.Procs program 4 5 6 7 8 9 10 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut src dst maskBase work U d : ℕ}
    (a : Fin L) (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hsrc : src+downsetCap L cut ≤ maskBase) (hdst : dst+downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hsep : Apart src (downsetCap L cut) dst (downsetCap L cut))
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : 2*(U : ℤ) ≤ lim.word)
    (hread : TableAt μ src cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,a.val,src,dst,maskBase,work] μ (time L cut)
      (fun _ μ' => TableAt μ' dst cut (Subset.zetaStep a f) ∧
        KeptBut μ μ' maskBase dst (downsetCap L cut)) :=
  meets rfl rfl rfl rfl rfl program_procs rfl rfl a f hw hcut hsrc hdst hmasks hsep
    hspace hword hvalueWord hread hvalues hd

theorem time_bound {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 4000*(L+1)^3*(downsetCap L cut+1) := by
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) := by
    have hh : 0 < (L+1)^2*(downsetCap L cut+1) := by positivity
    omega
  have hlin : L+1 ≤ (L+1)^2 := by nlinarith
  have hsmall := Nat.mul_le_mul_right (downsetCap L cut+1) hlin
  have hb : roundBudget L cut+20 ≤ 3000*((L+1)^2*(downsetCap L cut+1)) := by
    unfold roundBudget enumBudget batchBudget
    nlinarith
  have hm := Nat.mul_le_mul_left (cut+1) hb
  have hc := Nat.mul_le_mul_right (3000*((L+1)^2*(downsetCap L cut+1)))
    (Nat.succ_le_succ hcut)
  have hp₃ : 1 ≤ (L+1)^3*(downsetCap L cut+1) := by
    have hh : 0 < (L+1)^3*(downsetCap L cut+1) := by positivity
    omega
  unfold time
  calc
    _ ≤ (L+1)*(3000*((L+1)^2*(downsetCap L cut+1)))+20 :=
      Nat.add_le_add_right (hm.trans hc) 20
    _ = 3000*((L+1)^3*(downsetCap L cut+1))+20 := by ring
    _ ≤ 4000*((L+1)^3*(downsetCap L cut+1)) := by omega
    _ = _ := by ring

end ThreeSum.LightZetaPass
