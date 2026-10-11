import Submission.ThreeSum.MaskUnion
import Submission.ThreeSum.LightMaskErase

/-!
# General mask union and its cardinality on the bounded-word machine

The program tests each coordinate using the checked bit-deletion routine.
It constructs its own powers table, adds each new bit once, and writes the
union cardinality to one output cell. It never visits an ambient cube.
-/

namespace ThreeSum.LightMaskUnion

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open MaskUnion

variable {lim : Limits} {P : Program}

def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 9,v 3,v 0,v 5] 10 ;;
  .call pErase [v 0,v 9,v 2,v 0,v 5] 11 ;;
  .ite (v 10 <' v 3)
    (.ite (v 11 <' v 2) .skip
      (.set 7 (v 7 +' k 1) ;; .set 8 (v 8 +' M (v 5 +' v 9))))
    .skip

/-- Width, first cardinality and mask, second mask, cardinality output,
power-table scratch. The return value is the union mask. -/
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 5,v 0 +' k 1,k 2] 6 ;;
  .set 7 (v 1) ;;
  .set 8 (v 2) ;;
  .for 9 (v 0) (roundBody pErase) ;;
  .store (v 4) (v 7) ;;
  .set 0 (v 8)

def time (W : ℕ) : ℕ :=
  powTableTime (W+1)+W*(2*LightMaskErase.time W+180)+200

def Inv {W : ℕ} (μ : ℕ → ℤ) (A B : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ eB eA : ℤ,
    σ = ⟨frame [W,A.card,subsetMask A,subsetMask B,dst,work,powRet,
      (scanSet A B j).card,subsetMask (scanSet A B j),j,eB,eA],μ⟩

theorem meets {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W dst work d : ℕ} (A B : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+1 ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,A.card,subsetMask A,subsetMask B,dst,work] μ (time W)
      (fun r μ' => r = (subsetMask (A ∪ B) : ℤ) ∧
        μ' dst = ((A ∪ B).card : ℤ) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst 1) := by
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  have hcard (S : Finset (Fin W)) : S.card ≤ W := by
    simpa using Finset.card_le_univ S
  have hmask (S : Finset (Fin W)) : (subsetMask S : ℤ) ≤ lim.word := by
    have hn := (Nat.le_of_lt (subsetMask_isMask S).1).trans
      (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) (Nat.le_succ W))
    exact (by exact_mod_cast hn : (subsetMask S : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  have hAcard := hcard A
  have hAmask := hmask A
  have hBmask := hmask B
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := W+1) (b := 2) hPowers hw hspace (by
      intro i hi
      have hh : (2^i : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) hi
      exact (by exact_mod_cast hh : ((2^i : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword)
  light_call hp using powTableTime,LightMaskErase.time with powRet μ₁ ⟨hpow,hkept⟩
  have hpowers := powers_of_segment hpow
  light_set (A.card : ℕ) using powTableTime,LightMaskErase.time
  light_set (subsetMask A : ℕ) using powTableTime,LightMaskErase.time
  refine Ends.pieceThen (Ends.for
    (T := W*(2*LightMaskErase.time W+160)+20)
    (Q := Inv μ₁ A B dst work powRet W)
    (Inv μ₁ A B dst work powRet) W (2*LightMaskErase.time W+140)
    ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,0,?_⟩
    simp [update_frame_setLocal]
    change frame [(W : ℤ),A.card,subsetMask A,subsetMask B,dst,work,powRet,A.card,subsetMask A,0] =
      frame ([(W : ℤ),A.card,subsetMask A,subsetMask B,dst,work,powRet,A.card,subsetMask A,0] ++ [0,0])
    exact (frame_append_zeros _ 2).symm
  case round =>
    rintro j _ hj _ ⟨eB,eA,rfl⟩
    have hcurrentCard := hcard (scanSet A B j)
    have hcurrentMask := hmask (scanSet A B j)
    have hnextCard := hcard (scanSet A B (j+1))
    have hnextMask := hmask (scanSet A B (j+1))
    have hcB := LightMaskErase.meets hErase μ₁ hw hspace hword hpowers
      W j (subsetMask B) le_rfl (Nat.le_of_lt hj) (subsetMask_isMask B).1
      (d+1) (by omega)
    unfold roundBody
    light_call hcB using LightMaskErase.time with erasedB μ₂ ⟨herasedB,hmemB⟩
    subst μ₂
    have hcA := LightMaskErase.meets hErase μ₁ hw hspace hword hpowers
      W j (subsetMask A) le_rfl (Nat.le_of_lt hj) (subsetMask_isMask A).1
      (d+1) (by omega)
    light_call hcA using LightMaskErase.time with erasedA μ₂ ⟨herasedA,hmemA⟩
    subst μ₂
    light_if hbitB hnbitB : (eraseMask W j (subsetMask B) : ℤ) < (subsetMask B : ℤ)
      using herasedB,LightMaskErase.time
    · have hb : (⟨j,hj⟩ : Fin W) ∈ B :=
        (eraseMask_lt_iff B ⟨j,hj⟩).mp (by exact_mod_cast hbitB)
      light_if hbitA hnbitA : (eraseMask W j (subsetMask A) : ℤ) < (subsetMask A : ℤ)
        using herasedA,LightMaskErase.time
      · have ha : (⟨j,hj⟩ : Fin W) ∈ A :=
          (eraseMask_lt_iff A ⟨j,hj⟩).mp (by exact_mod_cast hbitA)
        have he := scanSet_succ_already A B hj hb ha
        apply Ends.skip
        exact ⟨by simp,erasedB,erasedA,by simp [update_frame_setLocal,he]⟩
      · have ha : (⟨j,hj⟩ : Fin W) ∉ A := by
          intro hh
          exact hnbitA (by exact_mod_cast (eraseMask_lt_iff A ⟨j,hj⟩).mpr hh)
        have hc := scanSet_card_succ_new A B hj hb ha
        have hm := scanSet_mask_succ_new A B hj hb ha
        have hread := hpowers j (Nat.le_of_lt hj)
        have hsum : (subsetMask (scanSet A B j) : ℤ)+μ₁ (work+j) =
            (subsetMask (scanSet A B (j+1)) : ℤ) := by
          rw [hread,hm]
          simp only [Nat.cast_add]
        light_set ((scanSet A B (j+1)).card : ℕ) using hc,LightMaskErase.time
        light_set (subsetMask (scanSet A B (j+1)) : ℕ) using hsum,LightMaskErase.time
        exact ⟨by simp,erasedB,erasedA,by simp [update_frame_setLocal]⟩
    · have hb : (⟨j,hj⟩ : Fin W) ∉ B := by
        intro hh
        exact hnbitB (by exact_mod_cast (eraseMask_lt_iff B ⟨j,hj⟩).mpr hh)
      have he := scanSet_succ_notMem A B hj hb
      apply Ends.skip
      exact ⟨by simp,erasedB,erasedA,by simp [update_frame_setLocal,he]⟩
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨eB,eA,rfl⟩
    light_side
  case after =>
    rintro _ ⟨eB,eA,rfl⟩
    have hc := hcard (A ∪ B)
    have hm := hmask (A ∪ B)
    light_store dst ((A ∪ B).card : ℕ)
    light_set (subsetMask (A ∪ B) : ℕ)
    refine ⟨by simp,by simp,?_,?_⟩
    · intro i hi
      change Function.update μ₁ dst ((A ∪ B).card : ℤ) (work+i) = _
      rw [Function.update_of_ne (by omega)]
      exact hpowers i hi
    · intro i hi
      change Function.update μ₁ dst ((A ∪ B).card : ℤ) i = _
      rw [Function.update_of_ne (by omega)]
      exact hkept i (Or.inl hi.1)

def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]

theorem program_meets {μ : ℕ → ℤ} {W dst work d : ℕ} (A B : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+1 ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,A.card,subsetMask A,subsetMask B,dst,work] μ (time W)
      (fun r μ' => r = (subsetMask (A ∪ B) : ℤ) ∧
        μ' dst = ((A ∪ B).card : ℤ) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst 1) :=
  meets rfl rfl rfl A B hw hdst hspace hword hd

theorem time_bound (W : ℕ) : time W ≤ 800*(W+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskUnion
