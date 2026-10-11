import Submission.ThreeSum.LightMaskErase
import Mathlib.Data.Finset.Max

/-!
# Computing the least coordinate of a nonempty mask

The program constructs its own powers table, scans the bit positions,
and uses the verified mask-deletion test. Its work is quadratic in the
width and its scratch is linear. It never scans mask values.
-/

namespace ThreeSum.LightMaskMinimum

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def best {L : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty) (j : ℕ) : ℕ :=
  if (S.min' hS).val < j then (S.min' hS).val else L

def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 5,v 1,v 0,v 2] 6 ;;
  .ite (v 6 <' v 1) (.ite (v 5 <' v 4) (.set 4 (v 5)) .skip) .skip

/-- Arguments: width, nonempty mask, scratch base. -/
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 2,v 0 +' k 1,k 2] 3 ;;
  .set 4 (v 0) ;;
  .for 5 (v 0) (roundBody pErase) ;;
  .set 0 (v 4)

def time (L : ℕ) : ℕ := powTableTime (L+1)+L*(LightMaskErase.time L+100)+100

def Inv {L : ℕ} (μ : ℕ → ℤ) (S : Finset (Fin L)) (hS : S.Nonempty)
    (work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [L,subsetMask S,work,powRet,best S hS j,j,r],μ⟩

theorem meets {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L work d : ℕ} (S : Finset (Fin L)) (hS : S.Nonempty)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [L,subsetMask S,work] μ (time L)
      (fun r μ' => r = ((S.min' hS).val : ℤ) ∧ Kept μ μ' work) := by
  have hmin : (S.min' hS).val < L := (S.min' hS).isLt
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := L+1) (b := 2) hPowers hw hspace (by
      intro i hi
      have hh : (2^i : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) hi
      exact (by exact_mod_cast hh : ((2^i : ℕ) : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hword)
  light_call hp using powTableTime,LightMaskErase.time with powRet μ₁ ⟨hpow,hkept⟩
  have hpowers := powers_of_segment hpow
  light_set (L : ℕ) using powTableTime,LightMaskErase.time
  refine Ends.pieceThen (Ends.for
    (T := L*(LightMaskErase.time L+80)+20)
    (Q := Inv μ₁ S hS work powRet L)
    (Inv μ₁ S hS work powRet) L (LightMaskErase.time L+60)
    ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,?_⟩
    simp [Inv,best,update_frame_setLocal]
    change frame [(L : ℤ),subsetMask S,work,powRet,L,0] =
      frame ([(L : ℤ),subsetMask S,work,powRet,L,0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r,rfl⟩
    have hb : best S hS j ≤ L := by unfold best; split <;> omega
    have hc := LightMaskErase.meets hErase μ₁ hw hspace hword hpowers
      L j (subsetMask S) le_rfl (Nat.le_of_lt hj) (subsetMask_isMask S).1
      (d+1) (by omega)
    unfold roundBody
    light_call hc using LightMaskErase.time with erased μ₂ ⟨herased,hmem⟩
    subst μ₂
    light_if hbit hnbit : (eraseMask L j (subsetMask S) : ℤ) < (subsetMask S : ℤ)
      using herased,LightMaskErase.time
    · have ha : (⟨j,hj⟩ : Fin L) ∈ S :=
        (eraseMask_lt_iff S ⟨j,hj⟩).mp (by exact_mod_cast hbit)
      have hminle : (S.min' hS).val ≤ j := Finset.min'_le S ⟨j,hj⟩ ha
      light_if hless hnless : (j : ℤ) < (best S hS j : ℤ) using LightMaskErase.time
      · have hbestgt : j < best S hS j := by exact_mod_cast hless
        have heq : (S.min' hS).val = j := by
          unfold best at hbestgt
          split at hbestgt <;> omega
        have hnext : best S hS (j+1) = j := by simp [best,heq]
        light_set (j : ℕ) using LightMaskErase.time
        refine ⟨by simp,erased,?_⟩
        simp [Inv,update_frame_setLocal,hnext]
      · have hbestle : best S hS j ≤ j := by
          have hh : ¬j < best S hS j := by exact_mod_cast hnless
          omega
        have hlt : (S.min' hS).val < j := by
          unfold best at hbestle
          split at hbestle <;> omega
        have heq : best S hS j = best S hS (j+1) := by
          simp [best,hlt,show (S.min' hS).val < j+1 by omega]
        apply Ends.skip
        refine ⟨by simp,erased,?_⟩
        simp [Inv,update_frame_setLocal,heq]
    · have ha : (⟨j,hj⟩ : Fin L) ∉ S := by
        intro hh
        exact hnbit (by exact_mod_cast (eraseMask_lt_iff S ⟨j,hj⟩).mpr hh)
      have hne : (S.min' hS).val ≠ j := by
        intro hh
        have he : S.min' hS = (⟨j,hj⟩ : Fin L) := Fin.ext hh
        exact ha (he ▸ Finset.min'_mem S hS)
      have heq : best S hS j = best S hS (j+1) := by
        unfold best
        have hh : (S.min' hS).val < j ↔ (S.min' hS).val < j+1 := by omega
        simp only [hh]
      apply Ends.skip
      refine ⟨by simp,erased,?_⟩
      simp [Inv,update_frame_setLocal,heq]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r,rfl⟩
    light_side
  case after =>
    rintro _ ⟨r,rfl⟩
    light_set ((S.min' hS).val : ℕ) using best,hmin
    exact ⟨by simp,fun i hi => hkept i (Or.inl hi)⟩

def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]

theorem program_meets {μ : ℕ → ℤ} {L work d : ℕ}
    (S : Finset (Fin L)) (hS : S.Nonempty)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,subsetMask S,work] μ (time L)
      (fun r μ' => r = ((S.min' hS).val : ℤ) ∧ Kept μ μ' work) :=
  meets rfl rfl rfl S hS hw hspace hword hd

theorem time_bound (L : ℕ) : time L ≤ 500*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskMinimum
