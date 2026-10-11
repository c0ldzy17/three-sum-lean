import Submission.ThreeSum.LightZetaPass
import Submission.ThreeSum.LightDownsetSize
import Submission.ThreeSum.SubsetStages

/-!
# Building and retaining every compact suffix-zeta stage

The fixed program computes the compact table stride, then makes one
coordinate pass per bit. All earlier stages remain available for forced
prefix queries. Its workspace is `(L+2)*downsetCap + O(L^2)`, and its
time is a polynomial in `L` times `downsetCap`. Intermediate word bounds
are derived from the original table values.
-/

namespace ThreeSum.LightZetaStages

open Light ThreeSum.SubsetAddress ThreeSum.SubsetStages ThreeSum.LightZetaCell
open ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def stageBase (base cap j : ℕ) : ℕ := base+j*cap

def StoredThrough {L : ℕ} (μ : ℕ → ℤ) (base cut : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) : Prop :=
  ∀ i ≤ j, TableAt μ (stageBase base (downsetCap L cut) i) cut (stageValue f i)

def roundBody (pPass : ℕ) : Stmt :=
  .call pPass [v 0,v 1,v 0 -' k 1 -' v 6,
    v 2 +' v 6 *' v 5,v 2 +' (v 6 +' k 1) *' v 5,v 3,v 4] 7

/-- Arguments: width, cutoff, base of all stage tables,
mask workspace, polynomial workspace. Stage zero initially holds `f`. -/
def body (pSize pPass : ℕ) : Stmt :=
  .call pSize [v 0,v 1,v 4] 5 ;;
  .for 6 (v 0) (roundBody pPass)

def time (L cut : ℕ) : ℕ :=
  LightDownsetSize.time L+L*(LightZetaPass.time L cut+80)+80

def Inv {L : ℕ} (μ : ℕ → ℤ) (cut base maskBase work : ℕ)
    (f : Finset (Fin L) → ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [L,cut,base,maskBase,work,downsetCap L cut,j,r],μ'⟩ ∧
    StoredThrough μ' base cut f j ∧
    KeptBut μ μ' maskBase base ((L+1)*downsetCap L cut)

theorem meets
    {pMain pSize pPass pEnumSetup pEnum pBatch pCell pSetup pBuild pFill pRow pLinear pPowers pRank pOffset pErase : ℕ}
    (hmain : P[pMain]? = some (body pSize pPass))
    (hSize : P[pSize]? = some (LightDownsetSize.body pSetup pOffset))
    (hPass : P[pPass]? = some (LightZetaPass.body pEnumSetup pBatch))
    (hEnumSetup : P[pEnumSetup]? = some (LightSubsetEnumerationSetup.body pPowers pEnum))
    (hEnum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    (hBatch : P[pBatch]? = some (LightZetaBatch.body pCell))
    (hCell : P[pCell]? = some (LightZetaCell.body pSetup pOffset pErase pRank))
    (C : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank)
    (hOffset : P[pOffset]? = some LightSubsetOffset.body)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L cut base maskBase work U d : ℕ}
    (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,base,maskBase,work] μ (time L cut)
      (fun _ μ' => StoredThrough μ' base cut f L ∧
        KeptBut μ μ' maskBase base ((L+1)*downsetCap L cut)) := by
  have hstage (i : ℕ) (hi : i ≤ L) :
      stageBase base (downsetCap L cut) i+downsetCap L cut ≤ maskBase := by
    have hm := Nat.mul_le_mul_right (downsetCap L cut) (Nat.succ_le_succ hi)
    unfold stageBase
    simp only [Nat.succ_mul,Nat.add_mul,Nat.one_mul] at hm hdata
    omega
  have hfirst := hstage 0 (by omega)
  simp only [stageBase,Nat.zero_mul,Nat.add_zero] at hfirst
  apply Meets.of_body hmain
  unfold body time
  have hs := LightDownsetSize.meets (d := d+1) (μ := μ)
    hSize C hOffset hw hspace hword hcut (by omega)
  light_call hs using LightDownsetSize.time with cap μ₁ ⟨hcap,hsizeKept⟩
  subst cap
  refine Ends.for (Inv μ cut base maskBase work f) L
    (LightZetaPass.time L cut+50) ?start ?round ?done ?bound
    (hT := by light_time [LightDownsetSize.time])
  case start =>
    refine ⟨0,μ₁,?_,?_,?_⟩
    · simp [update_frame_setLocal]
      change frame [(L : ℤ),cut,base,maskBase,work,downsetCap L cut,0] =
        frame ([(L : ℤ),cut,base,maskBase,work,downsetCap L cut,0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro i hi
      have he : i = 0 := by omega
      subst i
      intro S hS
      have hr := subsetRank_lt hS
      simpa only [stageBase,Nat.zero_mul,Nat.add_zero,stageValue_zero] using
        (hsizeKept _ (by omega)).trans (hread S hS)
    · intro i hi
      exact hsizeKept i (by omega)
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hstored,hkept⟩
    have hsource := hstored j le_rfl
    have hsrc := hstage j (by omega)
    have hdst := hstage (j+1) (by omega)
    have hsep : Apart (stageBase base (downsetCap L cut) j) (downsetCap L cut)
        (stageBase base (downsetCap L cut) (j+1)) (downsetCap L cut) := by
      left
      simp [stageBase,Nat.add_mul,Nat.add_assoc]
    have hcurrentValues := stageValue_abs_le f hvalues j (Nat.le_of_lt hj)
    have hvalue : 2*(((2^j*U : ℕ) : ℤ)) ≤ lim.word := by
      have hp : (2^(j+1) : ℕ) ≤ 2^L := Nat.pow_le_pow_right (by decide) (by omega)
      have hu := Nat.mul_le_mul_right U hp
      have he : 2*(2^j*U) = 2^(j+1)*U := by rw [pow_succ]; ring
      have hh : (2*(2^j*U) : ℕ) ≤ 2^L*U := by rw [he]; exact hu
      exact (by exact_mod_cast hh : 2*(((2^j*U : ℕ) : ℤ)) ≤ ((2^L*U : ℕ) : ℤ)).trans hvalueWord
    have hc := LightZetaPass.meets (d := d+1) hPass hEnumSetup hEnum hBatch hCell
      C hOffset hErase (nextCoord j hj) (stageValue f j)
      hw hcut hsrc hdst hmasks hsep hspace hword hvalue hsource hcurrentValues (by omega)
    have hcoord : (L : ℤ)-1-(j : ℤ) = ((nextCoord j hj).val : ℤ) := by
      simp only [nextCoord]
      omega
    have hsrcCast : (base : ℤ)+(j : ℤ)*(downsetCap L cut : ℤ) =
        (stageBase base (downsetCap L cut) j : ℤ) := by
      simp [stageBase]
    have hdstCast : (base : ℤ)+((j : ℤ)+1)*(downsetCap L cut : ℤ) =
        (stageBase base (downsetCap L cut) (j+1) : ℤ) := by
      simp [stageBase]
    unfold roundBody
    light_call hc using hcoord,hsrcCast,hdstCast with res μ₂ ⟨hnew,hpassKept⟩
    refine ⟨by simp,res,μ₂,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro i hi
      by_cases heq : i = j+1
      · subst i
        simpa only [stageValue_succ f hj] using hnew
      · have hij : i ≤ j := by omega
        have himul := Nat.mul_le_mul_right (downsetCap L cut) hij
        intro S hS
        have hr := subsetRank_lt hS
        have hbefore : stageBase base (downsetCap L cut) i+subsetRank S <
            stageBase base (downsetCap L cut) (j+1) := by
          unfold stageBase
          simp only [Nat.add_mul,Nat.one_mul]
          omega
        have hiend := hstage i (by omega)
        exact (hpassKept _ ⟨by omega,Or.inl hbefore⟩).trans (hstored i hij S hS)
    · intro i hi
      have hnextLow : base ≤ stageBase base (downsetCap L cut) (j+1) := by
        unfold stageBase
        omega
      have hnextHigh := hstage (j+1) (by omega)
      have hmul := Nat.mul_le_mul_right (downsetCap L cut) (show j+2 ≤ L+1 by omega)
      have hnextEnd : stageBase base (downsetCap L cut) (j+1)+downsetCap L cut ≤
          base+(L+1)*downsetCap L cut := by
        unfold stageBase
        simp only [Nat.add_mul,Nat.one_mul] at hmul ⊢
        omega
      exact (hpassKept i ⟨hi.1,by omega⟩).trans (hkept i hi)
  case done =>
    rintro _ _ ⟨r,μ',rfl,hstored,hkept⟩
    exact ⟨hstored,hkept⟩
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,_,_⟩
    light_side

def program : Program :=
  [body 1 2,LightDownsetSize.body 6 13,LightZetaPass.body 3 4,
    LightSubsetEnumerationSetup.body 11 15,LightZetaBatch.body 5,
    LightZetaCell.body 6 13 14 12,LightSubsetSetup.body 7 11 12,
    buildBody 8 9,fillBody,rowBody 10,LightArray.linearBody,powTableBody,
    rankBody 12,LightSubsetOffset.body,LightMaskErase.body 14,LightSubsetEnumeration.body 15]

theorem program_procs : LightSubsetSetup.Procs program 6 7 8 9 10 11 12 :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {L cut base maskBase work U d : ℕ}
    (f : Finset (Fin L) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ L)
    (hdata : base+(L+1)*downsetCap L cut ≤ maskBase)
    (hmasks : maskBase+downsetCap L cut ≤ work)
    (hspace : work+tableSize L+(L+1) ≤ lim.space)
    (hword : (((L+1)*2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^L*U : ℕ) : ℤ) ≤ lim.word)
    (hread : TableAt μ base cut f) (hvalues : ∀ T, T.card ≤ cut → |f T| ≤ U)
    (hd : d+L+7 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,base,maskBase,work] μ (time L cut)
      (fun _ μ' => StoredThrough μ' base cut f L ∧
        KeptBut μ μ' maskBase base ((L+1)*downsetCap L cut)) :=
  meets rfl rfl rfl rfl rfl rfl rfl program_procs rfl rfl f hw hcut hdata hmasks
    hspace hword hvalueWord hread hvalues hd

theorem stored_zeta {μ : ℕ → ℤ} {L cut base : ℕ} {f : Finset (Fin L) → ℤ}
    (h : StoredThrough μ base cut f L) :
    TableAt μ (stageBase base (downsetCap L cut) L) cut (Subset.zeta f) := by
  simpa only [stageValue_all] using h L le_rfl

theorem stored_forced_lookup {μ : ℕ → ℤ} {L cut base j : ℕ}
    {f : Finset (Fin L) → ℤ} (h : StoredThrough μ base cut f L) (hj : j ≤ L)
    (pre tail : Finset (Fin L)) (hp : Disjoint pre (suffix L j)) (ht : tail ⊆ suffix L j)
    (hcut : (pre ∪ tail).card ≤ cut) :
    μ (stageBase base (downsetCap L cut) j+subsetRank (pre ∪ tail)) =
      ∑ x ∈ tail.powerset, f (pre ∪ x) := by
  rw [h j hj (pre ∪ tail) hcut]
  exact stageValue_forced_prefix f j pre tail hp ht

theorem time_bound {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 6000*(L+1)^4*(downsetCap L cut+1) := by
  have hc := LightZetaPass.time_bound hcut
  have hs := LightDownsetSize.time_bound L
  have hmul := Nat.mul_le_mul_left L hc
  have hpow₂ : (L+1)^2 ≤ (L+1)^4 := Nat.pow_le_pow_right (by omega) (by omega)
  have hpow₄ : 1 ≤ (L+1)^4 := Nat.one_le_pow' 4 L
  have hlarge : (L+1)^4 ≤ (L+1)^4*(downsetCap L cut+1) := by
    exact Nat.le_mul_of_pos_right _ (by omega)
  have hlin : L+1 ≤ (L+1)^4 := by
    have hh := Nat.pow_le_pow_right (show 1 ≤ L+1 by omega) (show 1 ≤ 4 by omega)
    simpa using hh
  have hlarge : (L+1)*((L+1)^3*(downsetCap L cut+1)) = (L+1)^4*(downsetCap L cut+1) := by ring
  have htrans : L*(4000*(L+1)^3*(downsetCap L cut+1)) ≤
      4000*((L+1)^4*(downsetCap L cut+1)) := by
    have hh := Nat.mul_le_mul_right (4000*(L+1)^3*(downsetCap L cut+1))
      (show L ≤ L+1 by omega)
    nlinarith [hlarge]
  unfold time
  nlinarith

end ThreeSum.LightZetaStages
