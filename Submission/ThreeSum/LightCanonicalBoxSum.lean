import Submission.ThreeSum.LightQueryEnumeration
import Submission.ThreeSum.LightBoxSum

/-!
# Complete execution of the canonical box part of a sparse query

The query builds its own missing-subset array inside the actual query mask,
then evaluates every canonical box. Enumeration completeness and uniqueness
are discharged by the verified query-coordinate construction.
-/

namespace ThreeSum.LightCanonicalBoxSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}

/-- Procedure layout shared by complete sparse queries. -/
structure Procs (P : Program) (pEnum pSum : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pCore : ℕ
  pBox : ℕ
  pMinimum : ℕ
  pLookup : ℕ
  pSize : ℕ
  pAddress : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pRank : ℕ
  pOffset : ℕ
  enumerate : P[pEnum]? = some (LightQueryEnumeration.body pWeights pCore)
  weights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  erase : P[pErase]? = some (LightMaskErase.body pErase)
  core : P[pCore]? = some (LightSubsetEnumeration.body pCore)
  sum : P[pSum]? = some (LightBoxSum.body pBox)
  box : P[pBox]? = some (LightQueryBox.body pMinimum pLookup)
  minimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase)
  lookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress)
  size : P[pSize]? = some (LightDownsetSize.body pSetup pOffset)
  address : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset)
  table : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]? = some LightSubsetOffset.body

/-- Width, cutoff, query cardinality and mask, missing cardinality,
box-table base, output-mask buffer, polynomial scratch. -/
def body (pEnum pSum : ℕ) : Stmt :=
  .call pEnum [v 0,v 3,v 4,v 6,v 7] 8 ;;
  .call pSum [v 0,v 1,v 2,v 3,v 4,v 8,v 6,v 5,v 7] 0

def time (W c t : ℕ) : ℕ :=
  LightQueryEnumeration.time W c t+LightBoxSum.time W (c.choose t)+50

theorem meets {pMain pEnum pSum : ℕ}
    (hmain : P[pMain]? = some (body pEnum pSum))
    (C : Procs P pEnum pSum)
    {μ : ℕ → ℤ} {W cut t base maskBase work B d : ℕ}
    (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W)
    (hdata : base+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+Q.card.choose t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((Q.card.choose t*(2^W*B) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hflags : Q.card-t ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim P pMain d [W,cut,Q.card,subsetMask Q,t,base,maskBase,work] μ (time W Q.card t)
      (fun r μ' =>
        r = ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        KeptBut μ μ' work maskBase (Q.card.choose t)) := by
  have henumSpace : work+(2*W+2) ≤ lim.space := by
    unfold tableSize at hspace
    nlinarith
  have henumWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hm : (2^(W+1) : ℕ) ≤ (W+1)*2^(W+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hm : ((2^(W+1) : ℕ) : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have he := LightQueryEnumeration.meets (d := d+1) (μ := μ) C.enumerate C.weights C.table.powers C.erase C.core
    Q hw henumSpace henumWord ht hmasks (by omega)
  light_call he using LightQueryEnumeration.time,LightBoxSum.time
    with count μ₁ ⟨hcount,hmaskSeg,_,hkeepEnum⟩
  have hstored₁ : LightBoxStages.StoredThrough μ₁ base cut weight W := by
    intro j hj S hS
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap W cut) (Nat.succ_le_succ hj)
    have ha : LightBoxStages.stageBase base (downsetCap W cut) j+subsetRank S < maskBase := by
      unfold LightBoxStages.stageBase
      simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
      omega
    exact (hkeepEnum _ ⟨by omega,Or.inl ha⟩).trans (hstored j hj S hS)
  have hvalid : ∀ U ∈ missingSets Q t, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut := by
    intro U hU
    have hu := (missingSets_mem Q U t).mp hU
    refine ⟨hu.1,hu.2,?_⟩
    rw [Finset.card_sdiff_of_subset hu.1,hu.2]
    exact hflags
  have hs := LightBoxSum.meets (d := d+1) (μ := μ₁) C.sum C.box C.minimum C.lookup C.size C.address
    C.table C.offset C.erase Q (missingSets Q t) weight hw hcut (by omega)
    (by simpa using hmasks) hspace hword (by simpa using haccWord)
    hvalid hweight hstored₁ hmaskSeg (by omega)
  light_call hs using LightQueryEnumeration.time,LightBoxSum.time,hcount,missingSets_length
    with res μ₂ ⟨hres,hkeepSum⟩
  refine ⟨?_,?_⟩
  · exact hres.trans (LightBoxSum.sum_eq_canonical Q weight (missingSets Q t)
      (missingSets_nodup Q t) (fun U => by simp only [missingSets_mem,Finset.mem_powersetCard]))
  · intro i hi
    exact (hkeepSum i hi.1).trans (hkeepEnum i hi)

def program : Program :=
  [body 1 3,LightQueryEnumeration.body 2 4,LightQueryWeights.body 10 13,
    LightBoxSum.body 5,LightSubsetEnumeration.body 4,LightQueryBox.body 6 7,
    LightMaskMinimum.body 10 13,LightStageLookup.body 8 9,
    LightDownsetSize.body 11 15,LightDownsetAddress.body 11 15,powTableBody,
    LightSubsetSetup.body 12 10 14,buildBody 16 17,LightMaskErase.body 13,
    rankBody 14,LightSubsetOffset.body,fillBody,rowBody 18,LightArray.linearBody]

def program_procs : Procs program 1 3 where
  pWeights := 2
  pPowers := 10
  pErase := 13
  pCore := 4
  pBox := 5
  pMinimum := 6
  pLookup := 7
  pSize := 8
  pAddress := 9
  pSetup := 11
  pBuild := 12
  pFill := 16
  pRow := 17
  pLinear := 18
  pRank := 14
  pOffset := 15
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

theorem program_meets {μ : ℕ → ℤ} {W cut t base maskBase work B d : ℕ}
    (Q : Finset (Fin W)) (weight : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W)
    (hdata : base+(W+1)*downsetCap W cut ≤ maskBase)
    (hmasks : maskBase+Q.card.choose t ≤ work)
    (hspace : work+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((Q.card.choose t*(2^W*B) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hflags : Q.card-t ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight W)
    (hd : d+W+8 ≤ lim.depth) :
    Meets lim program 0 d [W,cut,Q.card,subsetMask Q,t,base,maskBase,work] μ (time W Q.card t)
      (fun r μ' =>
        r = ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight ∧
        KeptBut μ μ' work maskBase (Q.card.choose t)) :=
  meets rfl program_procs Q weight hw hcut hdata hmasks hspace hword haccWord ht hflags hweight hstored hd

theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 5200*(W+1)^2*(c.choose t+1) := by
  have he := LightQueryEnumeration.time_bound (t := t) hc
  have hs := LightBoxSum.time_bound W (c.choose t)
  have hp : 1 ≤ (W+1)^2*(c.choose t+1) := Nat.mul_pos (by positivity) (by omega)
  unfold time
  nlinarith

end ThreeSum.LightCanonicalBoxSum
