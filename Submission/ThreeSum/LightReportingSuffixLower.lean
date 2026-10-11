import Submission.ThreeSum.LightReportingSuffixCell

/-!
# Actual global-to-local suffix-mask conversion

The program constructs powers once, tests each suffix coordinate using the
verified mask-bit procedure, and accumulates its local power. Runtime is
quadratic in the width, independent of the numeric mask value.
-/

namespace ThreeSum.LightReportingSuffixLower

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open ReportingHostSuffix MaskErase

variable {lim : Limits} {P : Program}

def scanMask {V : ℕ} (S : Finset (Fin V)) (j : ℕ) : ℕ :=
  subsetMask (S.filter fun i => i.val < j)

@[simp] theorem scanMask_zero {V : ℕ} (S : Finset (Fin V)) : scanMask S 0 = 0 := by
  simp [scanMask]

@[simp] theorem scanMask_all {V : ℕ} (S : Finset (Fin V)) : scanMask S V = subsetMask S := by
  have he : S.filter (fun i => i.val < V) = S := Finset.filter_true_of_mem (fun i _ => i.isLt)
  rw [scanMask,he]

theorem scanMask_succ {V j : ℕ} (S : Finset (Fin V)) (hj : j < V) :
    scanMask S (j+1) = scanMask S j+if (⟨j,hj⟩ : Fin V) ∈ S then 2^j else 0 := by
  let i : Fin V := ⟨j,hj⟩
  have hf : S.filter (fun x => x.val < j+1) =
      if i ∈ S then insert i (S.filter fun x => x.val < j) else S.filter fun x => x.val < j := by
    ext x
    by_cases he : x = i
    · subst x
      by_cases hs : i ∈ S <;> simp [hs,i]
    · have hx : x.val ≠ j := by intro hv; apply he; exact Fin.ext hv
      by_cases hs : i ∈ S <;> simp only [hs,ite_true,ite_false,Finset.mem_filter,Finset.mem_insert,he,false_or]
      <;> constructor <;> rintro ⟨hxs,hxj⟩ <;> exact ⟨hxs,by omega⟩
  unfold scanMask
  rw [hf]
  by_cases hs : i ∈ S
  · rw [if_pos hs]
    rw [MaskDifference.subsetMask_sum,Finset.sum_insert (by simp [i])]
    rw [MaskDifference.subsetMask_sum]
    simp only [i,hs,ite_true]
    omega
  · simp only [hs,ite_false,i,Nat.add_zero]

def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 2 +' v 7,v 3,v 0,v 4] 8 ;;
  .ite (v 8 =' v 3) .skip (.set 6 (v 6 +' M (v 4 +' v 7)))

def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 4,v 0 +' k 1,k 2] 5 ;;
  .set 6 (k 0) ;;
  .for 7 (v 1) (roundBody pErase) ;;
  .set 0 (v 6)

def time (W V : ℕ) : ℕ := powTableTime (W+1)+V*(LightMaskErase.time W+100)+100

def Inv {W V offset : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V))
    (μ : ℕ → ℤ) (powers : ℕ) (ret : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [W,V,offset,subsetMask (liftSet hfit S),powers,ret,scanMask S j,j,r],μ⟩

theorem meets {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W V offset powers d : ℕ} (hfit : offset+V ≤ W) (S : Finset (Fin V))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,V,offset,subsetMask (liftSet hfit S),powers] μ (time W V)
      (fun r μ' => r = (subsetMask S : ℤ) ∧ Powers μ' powers W ∧ Kept μ μ' powers) := by
  have hV : V ≤ W := by omega
  have htwo : (2 : ℤ) ≤ lim.word := by
    have hp : (2^1 : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hp : (2 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  have hpartWord (j : ℕ) : (scanMask S j : ℤ) ≤ lim.word := by
    have hp : scanMask S j ≤ 2^(W+1) :=
      (Nat.le_of_lt (subsetMask_isMask (S.filter fun i => i.val < j)).1).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hp : (scanMask S j : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (P := P) (d := d+1) (μ := μ) (dst := powers) (L := W+1) (b := 2)
    hpowers hw hspace (by
      intro j hj
      exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hword)
  light_call hp using powTableTime,LightMaskErase.time with ret μ₁ ⟨hpows,hkeepPowers⟩
  have hPowers : Powers μ₁ powers W := powers_of_segment hpows
  light_set (0 : ℕ) using LightMaskErase.time
  refine Ends.pieceThen (Ends.for
    (T := V*(LightMaskErase.time W+90)+20)
    (Q := Inv hfit S μ₁ powers ret V) (Inv hfit S μ₁ powers ret)
    V (LightMaskErase.time W+80) ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,?_⟩
    simp [update_frame_setLocal]
    change frame [(W : ℤ),V,offset,subsetMask (liftSet hfit S),powers,ret,0,0] =
      frame ([(W : ℤ),V,offset,subsetMask (liftSet hfit S),powers,ret,0,0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r,rfl⟩
    have he := LightMaskErase.meets herase μ₁ hw hspace hword hPowers
      W (offset+j) (subsetMask (liftSet hfit S)) le_rfl (by omega)
      (subsetMask_isMask _).1 (d+1) (by omega)
    have hbit : eraseMask W (offset+j) (subsetMask (liftSet hfit S)) ≠ subsetMask (liftSet hfit S) ↔
        (⟨j,hj⟩ : Fin V) ∈ S := by
      simpa [liftSet] using eraseMask_ne_iff (liftSet hfit S) (shiftEmbedding offset hfit ⟨j,hj⟩)
    unfold roundBody
    light_call he using LightMaskErase.time with found μ₂ ⟨hfound,hmem⟩
    subst μ₂
    light_if heq hne : found = (subsetMask (liftSet hfit S) : ℤ) using LightMaskErase.time
    · have hs : (⟨j,hj⟩ : Fin V) ∉ S := by
        intro hs
        exact (hbit.mpr hs) (by exact_mod_cast hfound.symm.trans heq)
      light_skip
      refine ⟨by simp,found,?_⟩
      simp [update_frame_setLocal,scanMask_succ S hj,hs]
    · have hs : (⟨j,hj⟩ : Fin V) ∈ S := by
        apply hbit.mp
        intro heq
        apply hne
        rw [hfound,heq]
      have hpj := hPowers j (by omega)
      have hsum : (scanMask S j : ℤ)+μ₁ (powers+j) = (scanMask S (j+1) : ℤ) := by
        rw [hpj,scanMask_succ S hj,if_pos hs]
        push_cast
        rfl
      have hbound := hpartWord (j+1)
      light_set (scanMask S (j+1) : ℕ) using hsum,LightMaskErase.time
      refine ⟨by simp,found,?_⟩
      simp [update_frame_setLocal]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r,rfl⟩
    light_side
  case after =>
    rintro _ ⟨r,rfl⟩
    have hbound := hpartWord V
    light_set (subsetMask S : ℕ) using scanMask_all
    refine ⟨by simp,hPowers,?_⟩
    intro i hi
    exact hkeepPowers i (Or.inl hi)

def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]

theorem time_bound {W V : ℕ} (hV : V ≤ W) : time W V ≤ 400*(W+1)^2 := by
  have hm := Nat.mul_le_mul_right (LightMaskErase.time W+100) hV
  unfold time powTableTime LightMaskErase.time at *
  nlinarith

end ThreeSum.LightReportingSuffixLower
