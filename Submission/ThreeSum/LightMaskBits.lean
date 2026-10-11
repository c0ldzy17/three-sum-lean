import Submission.ThreeSum.LightMaskErase
import Submission.ThreeSum.MaskDecode

/-! # A literal Boolean coordinate row for a subset mask -/

namespace ThreeSum.LightMaskBits

open Light LightSubsetAddress MaskErase

def bit (L m j : ℕ) : ℕ := if eraseMask L j m = m then 0 else 1

theorem bit_le (L m j : ℕ) : bit L m j ≤ 1 := by unfold bit; split <;> omega

theorem bit_subsetMask {L : ℕ} (s : Finset (Fin L)) (j : Fin L) :
    bit L (SubsetAddress.subsetMask s) j.val = if j ∈ s then 1 else 0 := by
  have h := eraseMask_ne_iff s j
  unfold bit
  split <;> split <;> simp_all

theorem bit_decode {L m : ℕ} (hm : m < 2^L) (j : Fin L) :
    bit L m j.val = if j ∈ MaskDecode.decode L m then 1 else 0 := by
  simpa only [MaskDecode.subsetMask_decode hm] using bit_subsetMask (MaskDecode.decode L m) j

def loopBody (pErase : ℕ) : Stmt :=
  .for 4 (v 0) (
    .call pErase [v 0,v 4,v 1,v 0,v 3] 5 ;;
    .ite (v 5 =' v 1) (.store (v 2 +' v 4) (k 0)) (.store (v 2 +' v 4) (k 1)))

def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 5 ;;
  loopBody pErase

def time (L : ℕ) : ℕ := powTableTime (L+1)+L*(LightMaskErase.time L+80)+50

def Inv (μ : ℕ → ℤ) (L m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [L,m,dst,work,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (bit L m j : ℤ)) ∧ Powers μ' work L ∧
    KeptBut μ μ' work dst L

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {L m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space) (hdst : dst+L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) (hm : m < 2^L) :
    Meets lim P pMain d [L,m,dst,work] μ (time L)
      (fun _ μ' => (∀ j < L, μ' (dst+j) = (bit L m j : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst L) := by
  have hpL : ((2^L : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (Nat.le_succ L))).trans hword
  have hmZ : (m : ℤ) < lim.word := (Int.ofNat_lt.mpr hm).trans_le hpL
  have htwo : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (d := d+1) (μ := μ) (dst := work) (L := L+1) (b := 2)
    hpowers hw hspace (by
      intro j hj
      exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))).trans hword)
  light_call hp using LightMaskErase.time with r μ₁ ⟨hpow,hkept⟩
  have hpow' : Powers μ₁ work L := powers_of_segment hpow
  unfold loopBody
  refine Ends.for (Inv μ L m dst work) L (LightMaskErase.time L+72) ?_ ?_ ?_ ?_
  · refine ⟨r,μ₁,?_,?_,hpow',?_⟩
    · simp [update_frame_setLocal]
    · intro j hj; omega
    · intro a ⟨ha,hout⟩; exact hkept a (Or.inl ha)
  · rintro j _ hj _ ⟨r,μ',rfl,written,pows,kept⟩
    have hc := LightMaskErase.meets (W := L) (powers := work) herase μ' hw hspace hword pows
      L j m le_rfl (by omega) hm (d+1) (by omega)
    light_call hc using LightMaskErase.time with v μ₂ ⟨hv,hmem⟩
    subst μ₂
    light_if heZ hnZ : (v : ℤ) = (m : ℤ) using LightMaskErase.time
    · have he : eraseMask L j m = m := by exact_mod_cast hv.symm.trans heZ
      light_store (dst+j) (0 : ℕ) using LightMaskErase.time
      refine ⟨by simp,v,Function.update μ' (dst+j) 0,by simp [update_frame_setLocal],?_,?_,?_⟩
      · intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
        · rw [Function.update_of_ne (by omega)]
          exact written a ha
        · simp [bit,he]
      · intro a ha
        rw [Function.update_of_ne (by omega)]
        exact pows a ha
      · intro a ⟨ha,hout⟩
        rw [Function.update_of_ne (by omega)]
        exact kept a ⟨ha,hout⟩
    · have he : eraseMask L j m ≠ m := by
        intro hh
        apply hnZ
        simpa [hh] using hv
      light_store (dst+j) (1 : ℕ) using LightMaskErase.time
      refine ⟨by simp,v,Function.update μ' (dst+j) 1,by simp [update_frame_setLocal],?_,?_,?_⟩
      · intro a ha
        rcases Nat.lt_succ_iff_lt_or_eq.mp ha with ha | rfl
        · rw [Function.update_of_ne (by omega)]
          exact written a ha
        · simp [bit,he]
      · intro a ha
        rw [Function.update_of_ne (by omega)]
        exact pows a ha
      · intro a ⟨ha,hout⟩
        rw [Function.update_of_ne (by omega)]
        exact kept a ⟨ha,hout⟩
  · rintro _ _ ⟨r,μ',rfl,written,pows,kept⟩
    exact ⟨written,pows,kept⟩
  · rintro i _ _ _ ⟨r,μ',rfl,_,_,_⟩
    simp

def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]

theorem program_meets
    {μ : ℕ → ℤ} {L m dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+1 ≤ lim.depth)
    (hspace : work+(L+1) ≤ lim.space) (hdst : dst+L ≤ work)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) (hm : m < 2^L) :
    Meets lim program 0 d [L,m,dst,work] μ (time L)
      (fun _ μ' => (∀ j < L, μ' (dst+j) = (bit L m j : ℤ)) ∧
        Powers μ' work L ∧ KeptBut μ μ' work dst L) :=
  meets rfl rfl rfl hw hd hspace hdst hword hm

theorem time_bound (L : ℕ) : time L ≤ 300*(L+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightMaskBits
