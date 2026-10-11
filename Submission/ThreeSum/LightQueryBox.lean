import Submission.ThreeSum.LightStageLookup
import Submission.ThreeSum.LightMaskMinimum
import Submission.ThreeSum.MaskDifference

/-!
# Executing a canonical sparse-query box

Given valid masks `U ⊆ Q`, the program subtracts their masks and
cardinalities, computes the least missing coordinate itself, computes
the compact stage address, and reads the signed box sum. The empty
missing set uses the final prefix stage. No address or minimum is
provided as advice.
-/

namespace ThreeSum.LightQueryBox

open Light ThreeSum.SubsetAddress ThreeSum.MaskDifference
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: width, cutoff, Q cardinality and mask, U cardinality and
mask, box-table base, polynomial scratch base. -/
def body (pMinimum pLookup : ℕ) : Stmt :=
  .set 8 (v 2 -' v 4) ;;
  .set 9 (v 3 -' v 5) ;;
  .ite (v 5 =' k 0) (.set 10 (v 0))
    (.call pMinimum [v 0,v 5,v 7] 10) ;;
  .call pLookup [v 0,v 1,v 8,v 9,v 10,v 6,v 7] 0

def time (L : ℕ) : ℕ := LightMaskMinimum.time L+LightStageLookup.time L+120

theorem meets
    {pMain pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pMinimum pLookup))
    (hMinimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base work d : ℕ}
    (Q U : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hU : U ⊆ Q) (hflags : (Q \ U).card ≤ cut)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,Q.card,subsetMask Q,U.card,subsetMask U,base,work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        Kept μ μ' work) := by
  have hword₀ : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^(L+1) : ℕ) ≤ (L+1)*2^(L+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤
      (((L+1)*2^(L+1) : ℕ) : ℤ)).trans hword
  have hpow : (2^L : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpowZ : ((2^L : ℕ) : ℤ) ≤ lim.word :=
    (by exact_mod_cast hpow : ((2^L : ℕ) : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hword₀
  have hcardle := Finset.card_le_card hU
  have hcardDiff := Finset.card_sdiff_of_subset hU
  have hcard : (Q.card : ℤ)-(U.card : ℤ) = ((Q \ U).card : ℤ) := by omega
  have hmask := subsetMask_sdiff_int Q U hU
  have hmaskBound : (subsetMask (Q \ U) : ℤ) < ((2^L : ℕ) : ℤ) := by
    exact_mod_cast (subsetMask_isMask (Q \ U)).1
  have hmaskNonneg : (0 : ℤ) ≤ subsetMask (Q \ U) := Int.natCast_nonneg _
  have hr := subsetRank_lt hflags
  have haddr (j : ℕ) (hj : j ≤ L) : LightStageLookup.readAddr cut base j (Q \ U) < work := by
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hj)
    unfold LightStageLookup.readAddr
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
    omega
  apply Meets.of_body hmain
  unfold body time
  light_set ((Q \ U).card : ℕ) using hcard,LightMaskMinimum.time,LightStageLookup.time
  light_set (subsetMask (Q \ U) : ℕ) using hmask,LightMaskMinimum.time,LightStageLookup.time
  refine Ends.pieceThen (Ends.iteLast
    (T := LightMaskMinimum.time L+20)
    (Q := fun σ => ∃ (j : ℕ), j ≤ L ∧
      σ.loc = frame (setLocal (setLocal (setLocal
        [L,cut,Q.card,subsetMask Q,U.card,subsetMask U,base,work]
        8 ((Q \ U).card : ℤ)) 9 (subsetMask (Q \ U) : ℤ)) 10 (j : ℤ)) ∧
      Kept μ σ.mem work ∧
      σ.mem (LightStageLookup.readAddr cut base j (Q \ U)) =
        SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight)
    ?zero ?nonzero (by light_side) (hT := by light_time [LightMaskMinimum.time]))
    ?after (hT := by light_time [LightMaskMinimum.time,LightStageLookup.time])
  case zero =>
    intro hz
    have hz' : subsetMask U = 0 := by exact_mod_cast (by simpa using hz : (subsetMask U : ℤ) = 0)
    have hUempty := (subsetMask_eq_zero_iff U).mp hz'
    have hread : μ (LightStageLookup.readAddr cut base L (Q \ U)) =
        SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight := by
      have hh := LightBoxStages.stored_box_lookup hstored le_rfl (Q \ U) hflags
      simpa [LightStageLookup.readAddr,LightBoxStages.stageBase,SparseBoxes.queryFree,hUempty] using hh
    light_set (L : ℕ) using LightMaskMinimum.time,LightStageLookup.time
    exact ⟨L,le_rfl,rfl,SameOn.refl,hread⟩
  case nonzero =>
    intro hz
    have hUpos : U.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      apply hz
      simp [he,subsetMask_empty]
    have hm := LightMaskMinimum.meets (d := d+1) (μ := μ) (work := work)
      hMinimum C.powers hErase U hUpos
      hw (by omega) hword₀ (by omega)
    light_call hm using LightMaskMinimum.time,LightStageLookup.time
      with smallest μ₁ ⟨hsmallest,hminKept⟩
    refine ⟨(U.min' hUpos).val,Nat.le_of_lt (U.min' hUpos).isLt,?_,hminKept,?_⟩
    · simp only [hsmallest]
    · have hh := LightBoxStages.stored_query_box hstored Q U hUpos hflags
      exact (hminKept _ (haddr _ (Nat.le_of_lt (U.min' hUpos).isLt))).trans hh
  case after =>
    rintro σ ⟨j,hj,hloc,hkept,hread⟩
    rcases σ with ⟨loc,μ'⟩
    simp only at hloc hkept hread
    subst loc
    have hc := LightStageLookup.meets (d := d+1) hLookup hSize hAddress C hOffset
      (Q \ U) (SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight)
      hw hcut hdata hspace hword hflags hj hread (by omega)
    light_call hc using LightMaskMinimum.time,LightStageLookup.time
      with res μ₁ ⟨hres,hnewKept⟩
    exact ⟨hres,hkept.trans hnewKept⟩

def program : Program :=
  [body 1 2,LightMaskMinimum.body 8 11,LightStageLookup.body 3 4,
    LightDownsetSize.body 5 10,LightDownsetAddress.body 5 10,
    LightSubsetSetup.body 6 8 9,buildBody 7 12,fillBody,powTableBody,
    rankBody 9,LightSubsetOffset.body,LightMaskErase.body 11,rowBody 13,LightArray.linearBody]

theorem program_procs : LightSubsetSetup.Procs program 5 6 7 12 13 8 9 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut base work d : ℕ}
    (Q U : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hU : U ⊆ Q) (hflags : (Q \ U).card ≤ cut)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hd : d+L+6 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,Q.card,subsetMask Q,U.card,subsetMask U,base,work] μ (time L)
      (fun r μ' => r = SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        Kept μ μ' work) :=
  meets rfl rfl rfl rfl rfl program_procs rfl rfl Q U weight hw hcut hdata hspace hword
    hU hflags hstored hd

theorem time_bound (L : ℕ) : time L ≤ 3500*(L+1)^2 := by
  have hm := LightMaskMinimum.time_bound L
  have hl := LightStageLookup.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  unfold time
  omega

end ThreeSum.LightQueryBox
