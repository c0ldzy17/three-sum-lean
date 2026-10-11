import Submission.ThreeSum.LightQueryBox
import Submission.ThreeSum.BoxBounds

/-!
# Summing the canonical boxes of a sparse query

The missing-subset masks are loaded from an actual array, and every
summand is produced by the verified box-query procedure. Signed
accumulator bounds follow from bounds on the original leaf weights.
The final theorem identifies the sum with the canonical powerset-card
sum whenever the mask array is an exact enumeration of that family.
-/

namespace ThreeSum.LightBoxSum

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def boxValue {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (U : Finset (Fin L)) : ℤ := SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight

def partialSum {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (j : ℕ) : ℤ :=
  ((missing.map (boxValue Q weight)).take j).sum

theorem partialSum_succ {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) {j : ℕ} (hj : j < missing.length) :
    partialSum Q weight missing (j+1) = partialSum Q weight missing j+boxValue Q weight missing[j] := by
  unfold partialSum
  rw [List.sum_take_succ _ _ (by simpa using hj),List.getElem_map]

@[simp] theorem partialSum_length {L : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) :
    partialSum Q weight missing missing.length = (missing.map (boxValue Q weight)).sum := by
  unfold partialSum
  have he : missing.length = (missing.map (boxValue Q weight)).length := (List.length_map _).symm
  rw [he,List.take_length]

def roundBody (pBox : ℕ) : Stmt :=
  .call pBox [v 0,v 1,v 2,v 3,v 4,M (v 6 +' v 10),v 7,v 8] 11 ;;
  .set 9 (v 9 +' v 11)

/-- Arguments: width, cutoff, Q cardinality and mask, missing cardinality,
number of masks, mask base, box-table base, polynomial scratch base. -/
def body (pBox : ℕ) : Stmt :=
  .set 9 (k 0) ;;
  .for 10 (v 5) (roundBody pBox) ;;
  .set 0 (v 9)

def time (L n : ℕ) : ℕ := n*(LightQueryBox.time L+60)+40

def Inv {L : ℕ} (μ : ℕ → ℤ) (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (cut t maskBase base work j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work,
      partialSum Q weight missing j,j,r],μ'⟩ ∧ Kept μ μ' work

theorem meets
    {pMain pBox pMinimum pLookup pSize pAddress pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pBox))
    (hBox : P[pBox]? = some (LightQueryBox.body pMinimum pLookup))
    (hMinimum : P[pMinimum]? = some (LightMaskMinimum.body pPowers pErase))
    (hLookup : P[pLookup]? = some (LightStageLookup.body pSize pAddress))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hAddress : P[pAddress]? = some (LightDownsetAddress.body pSetup pOffset))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut t maskBase base work B d : ℕ}
    (Q : Finset (Fin L)) (missing : List (Finset (Fin L))) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work)
    (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*(2^L*B) : ℕ) : ℤ) ≤ lim.word)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work]
      μ (time L missing.length)
      (fun r μ' => r = (missing.map (boxValue Q weight)).sum ∧ Kept μ μ' work) := by
  have hboxBound : ∀ U ∈ missing, |boxValue Q weight U| ≤ ((2^L*B : ℕ) : ℤ) := by
    intro U hU
    exact BoxBounds.boxSum_abs_le (Q \ U) (SparseBoxes.queryFree Q U) weight
      (hvalid U hU).2.2 hweight
  have hacc (j : ℕ) : |partialSum Q weight missing j| ≤ lim.word := by
    have hh := List.abs_sum_take_map_le missing (boxValue Q weight) hboxBound j
    have hb : (missing.length : ℤ)*((2^L*B : ℕ) : ℤ) ≤ lim.word := by
      simpa only [Nat.cast_mul] using haccWord
    exact hh.trans hb
  have haddr (j : ℕ) (hj : j ≤ L) (S : Finset (Fin L)) (hS : S.card ≤ cut) :
      LightBoxStages.stageBase base (downsetCap L cut) j+subsetRank S < work := by
    have hr := subsetRank_lt hS
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hj)
    unfold LightBoxStages.stageBase
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
    omega
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := missing.length*(LightQueryBox.time L+50)+20)
    (Q := Inv μ Q weight missing cut t maskBase base work missing.length)
    (Inv μ Q weight missing cut t maskBase base work)
    missing.length (LightQueryBox.time L+40) ?start ?round ?done ?bound
    (hT := by light_time)) ?after
  case start =>
    refine ⟨0,μ,?_,SameOn.refl⟩
    simp [update_frame_setLocal,partialSum]
    change frame [(L : ℤ),cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work,0,0] =
      frame ([(L : ℤ),cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work,0,0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hkept⟩
    let U := missing[j]
    have hU := hvalid U (List.getElem_mem hj)
    have hstored' : LightBoxStages.StoredThrough μ' base cut weight L := by
      intro i hi S hS
      exact (hkept _ (haddr i hi S hS)).trans (hstored i hi S hS)
    have hmask : μ' (maskBase+j) = (subsetMask U : ℤ) := by
      have hr := hseg.getElem (by simpa using hj)
      simp only [List.getElem_map] at hr
      exact (hkept _ (by omega)).trans hr
    have hc := LightQueryBox.meets (d := d+1) hBox hMinimum hLookup hSize hAddress C hOffset hErase
      Q U weight hw hcut hdata hspace hword hU.1 hU.2.2 hstored' (by omega)
    rw [hU.2.1] at hc
    unfold roundBody
    light_call hc using hmask,LightQueryBox.time with res μ₁ ⟨hres,hnewKept⟩
    have hnext := abs_le.mp (hacc (j+1))
    have hsum : partialSum Q weight missing j+boxValue Q weight U =
        partialSum Q weight missing (j+1) := (partialSum_succ Q weight missing hj).symm
    have hres' : res = boxValue Q weight U := hres
    light_set (partialSum Q weight missing (j+1)) using hres',hsum,LightQueryBox.time
    refine ⟨by simp,res,μ₁,?_,hkept.trans hnewKept⟩
    simp [update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_⟩
    light_side
  case after =>
    rintro _ ⟨r,μ',rfl,hkept⟩
    have ha := abs_le.mp (hacc missing.length)
    light_set ((missing.map (boxValue Q weight)).sum) using partialSum_length
    exact ⟨by simp,hkept⟩

def program : Program :=
  [body 1,LightQueryBox.body 2 3,LightMaskMinimum.body 9 12,LightStageLookup.body 4 5,
    LightDownsetSize.body 6 11,LightDownsetAddress.body 6 11,
    LightSubsetSetup.body 7 9 10,buildBody 8 13,fillBody,powTableBody,
    rankBody 10,LightSubsetOffset.body,LightMaskErase.body 12,rowBody 14,LightArray.linearBody]

theorem program_procs : LightSubsetSetup.Procs program 6 7 8 13 14 9 10 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut t maskBase base work B d : ℕ}
    (Q : Finset (Fin L)) (missing : List (Finset (Fin L))) (weight : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ work) (hmasks : maskBase+missing.length ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (haccWord : ((missing.length*(2^L*B) : ℕ) : ℤ) ≤ lim.word)
    (hvalid : ∀ U ∈ missing, U ⊆ Q ∧ U.card = t ∧ (Q \ U).card ≤ cut)
    (hweight : ∀ S, S.card ≤ cut → |weight S| ≤ B)
    (hstored : LightBoxStages.StoredThrough μ base cut weight L)
    (hseg : SegN μ maskBase (missing.map subsetMask))
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,Q.card,subsetMask Q,t,missing.length,maskBase,base,work]
      μ (time L missing.length)
      (fun r μ' => r = (missing.map (boxValue Q weight)).sum ∧ Kept μ μ' work) :=
  meets rfl rfl rfl rfl rfl rfl program_procs rfl rfl Q missing weight hw hcut hdata hmasks
    hspace hword haccWord hvalid hweight hstored hseg hd

theorem sum_eq_canonical {L t : ℕ} (Q : Finset (Fin L)) (weight : Finset (Fin L) → ℤ)
    (missing : List (Finset (Fin L))) (hn : missing.Nodup)
    (hmem : ∀ U, U ∈ missing ↔ U ∈ Q.powersetCard t) :
    (missing.map (boxValue Q weight)).sum =
      ∑ U ∈ Q.powersetCard t, SparseBoxes.boxSum (Q \ U) (SparseBoxes.queryFree Q U) weight := by
  have he : missing.toFinset = Q.powersetCard t := by
    ext U
    simpa using hmem U
  rw [← List.sum_toFinset (boxValue Q weight) hn,he]
  rfl

theorem time_bound (L n : ℕ) : time L n ≤ 3600*(L+1)^2*(n+1) := by
  have h := LightQueryBox.time_bound L
  have hp : 1 ≤ (L+1)^2 := Nat.one_le_pow' 2 L
  have hb : LightQueryBox.time L+60 ≤ 3600*(L+1)^2 := by omega
  have hm := Nat.mul_le_mul_left n hb
  unfold time
  nlinarith

end ThreeSum.LightBoxSum
