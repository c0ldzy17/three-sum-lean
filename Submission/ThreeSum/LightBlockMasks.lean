import Submission.ThreeSum.BlockMaskLayout
import Submission.ThreeSum.LightSubsetEnumerationSetup

/-!
# Packing physical block masks into global row-major coordinates

The fixed program builds a power table, scales every input row mask by its
block position, writes the global row masks, and returns their union mask.
Only linear scans and polynomial scratch are used.
-/

namespace ThreeSum.LightBlockMasks

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout

variable {lim : Limits} {P : Program}

def roundBody : Stmt :=
  .set 10 (M (v 2 +' v 9) *' v 7) ;;
  .store (v 3 +' v 9) (v 10) ;;
  .set 8 (v 8 +' v 10) ;;
  .set 7 (v 7 *' v 6)

def nonemptyBody (pPowers : ℕ) : Stmt :=
  .call pPowers [v 4,v 1 +' k 1,k 2] 5 ;;
  .set 6 (M (v 4 +' v 1)) ;;
  .set 7 (k 1) ;;
  .set 8 (k 0) ;;
  .for 9 (v 0) roundBody ;;
  .set 0 (v 8)

/-- Block count, row width, physical input masks, packed-mask output, scratch. -/
def body (pPowers : ℕ) : Stmt :=
  .ite (k 0 <' v 0) (nonemptyBody pPowers) (.set 0 (k 0))

def time (J L : ℕ) : ℕ := powTableTime (L+1)+J*150+200

def Inv {J L : ℕ} (μ : ℕ → ℤ) (rows : Fin J → Finset (Fin L))
    (src dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [J,L,src,dst,work,powRet,2^L,2^(j*L),prefixMask rows j,j,r],μ'⟩ ∧
    SegN μ' dst ((packedMasks rows).take j) ∧ Powers μ' work L ∧
    KeptBut μ μ' work dst J

theorem meets {pMain pPowers : ℕ}
    (hmain : P[pMain]? = some (body pPowers)) (hPowers : P[pPowers]? = some powTableBody)
    {μ : ℕ → ℤ} {J L src dst work d : ℕ} (rows : Fin J → Finset (Fin L))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+J ≤ work) (hdst : dst+J ≤ work) (hsep : Apart src J dst J)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(J*L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : SegN μ src (rawMasks rows)) (hd : d+1 ≤ lim.depth) :
    Meets lim P pMain d [J,L,src,dst,work] μ (time J L)
      (fun r μ' => r = (subsetMask (indexSet (flat rows)) : ℤ) ∧
        SegN μ' dst (packedMasks rows) ∧ KeptBut μ μ' work dst J) := by
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(J*L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  have hpower (a : ℕ) (ha : a ≤ J*L+1) : ((2^a : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^a : ℕ) ≤ 2^(J*L+1) := Nat.pow_le_pow_right (by decide) ha
    exact (by exact_mod_cast hh : ((2^a : ℕ) : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  have hprefix (j : ℕ) : (prefixMask rows j : ℤ) ≤ lim.word := by
    have hh : prefixMask rows j ≤ 2^(J*L+1) :=
      (Nat.le_of_lt (prefixMask_lt rows j)).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hh : (prefixMask rows j : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  have hrow (i : Fin J) : (rowMask rows i : ℤ) ≤ lim.word := by
    have hh : rowMask rows i ≤ 2^(J*L+1) :=
      (Nat.le_of_lt (rowMask_lt rows i)).trans (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hh : (rowMask rows i : ℤ) ≤ ((2^(J*L+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  light_if hJpos hJzero : (0 : ℤ) < (J : ℤ) using powTableTime
  · have hJ : 0 < J := by exact_mod_cast hJpos
    have hL : L ≤ J*L := Nat.le_mul_of_pos_left _ hJ
    have hradix := hpower L (by omega)
    unfold nonemptyBody
    have hp := powTable_meets (d := d+1) (μ := μ) (dst := work)
      (L := L+1) (b := 2) hPowers hw hspace (by intro i hi; exact hpower i (by omega))
    light_call hp using powTableTime with powRet μ₁ ⟨hpow,hkept⟩
    have hpowers := powers_of_segment hpow
    have hradixRead := hpowers L le_rfl
    light_set (2^L : ℕ) using hradixRead,powTableTime
    light_set (1 : ℕ) using powTableTime
    light_set (0 : ℕ) using powTableTime
    light_assoc
    refine Ends.pieceThen (Ends.for (lim := lim) (P := P) (d := d) (i := 9) (hi := v 0) (body := roundBody)
      (T := J*130+20) (Q := Inv μ rows src dst work powRet J)
      (Inv μ rows src dst work powRet) J 110
      ?start ?round ?done ?bound (hT := by light_time)) ?after
    case start =>
      refine ⟨0,μ₁,?_,by simp [SegN],hpowers,?_⟩
      · simp [update_frame_setLocal]
        change frame [(J : ℤ),L,src,dst,work,powRet,2^L,1,0,0] =
          frame ([(J : ℤ),L,src,dst,work,powRet,2^L,1,0,0] ++ [0])
        exact (frame_append_zeros _ 1).symm
      · intro i hi
        exact hkept i (Or.inl hi.1)
    case round =>
      rintro j _ hj _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
      have hnextPrefix := hprefix (j+1)
      have hrowWord := hrow ⟨j,hj⟩
      have hmul := Nat.mul_le_mul_right L (show j+1 ≤ J by omega)
      have hnextFactor := hpower ((j+1)*L) (by omega)
      have hnextFactorInt : (2 : ℤ)^((j+1)*L) ≤ lim.word := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hnextFactor
      have hmread : μ' (src+j) = (subsetMask (rows ⟨j,hj⟩) : ℤ) := by
        rw [hkeep _ ⟨by omega,by omega⟩]
        have hr := hread.getElem (by simpa using hj)
        simpa only [rawMasks,List.getElem_ofFn] using hr
      have hprod : (subsetMask (rows ⟨j,hj⟩) : ℤ)*((2^(j*L) : ℕ) : ℤ) =
          (rowMask rows ⟨j,hj⟩ : ℤ) := by simp [rowMask,mul_comm]
      have hprodInt : (subsetMask (rows ⟨j,hj⟩) : ℤ)*2^(j*L) =
          (rowMask rows ⟨j,hj⟩ : ℤ) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hprod
      have hsum : (prefixMask rows j : ℤ)+(rowMask rows ⟨j,hj⟩ : ℤ) =
          (prefixMask rows (j+1) : ℤ) := by exact_mod_cast (prefixMask_succ rows hj).symm
      have hfactor : ((2^(j*L) : ℕ) : ℤ)*((2^L : ℕ) : ℤ) = ((2^((j+1)*L) : ℕ) : ℤ) := by
        norm_cast
        rw [← pow_add,Nat.succ_mul]
      have hfactorInt : (2 : ℤ)^(j*L)*2^L = ((2^((j+1)*L) : ℕ) : ℤ) := by
        simpa only [Nat.cast_pow,Nat.cast_ofNat] using hfactor
      unfold roundBody
      light_set (rowMask rows ⟨j,hj⟩ : ℕ) using hprod,hprodInt,hmread
      light_store (dst+j) (rowMask rows ⟨j,hj⟩ : ℕ)
      light_set (prefixMask rows (j+1) : ℕ) using hsum
      light_set (2^((j+1)*L) : ℕ) using hfactor,hfactorInt,hnextFactorInt
      refine ⟨by simp,rowMask rows ⟨j,hj⟩,
        Function.update μ' (dst+j) (rowMask rows ⟨j,hj⟩ : ℤ),?_,?_,?_,?_⟩
      · simp [update_frame_setLocal]
      · have hlen : ((packedMasks rows).take j).length = j := by simp; omega
        rw [packedMasks_take_succ rows hj]
        simpa only [hlen] using SegN.snoc hseg (rowMask rows ⟨j,hj⟩)
      · intro i hi
        change Function.update μ' (dst+j) (rowMask rows ⟨j,hj⟩ : ℤ) (work+i) = _
        rw [Function.update_of_ne (by omega)]
        exact hpowers' i hi
      · intro i hi
        change Function.update μ' (dst+j) (rowMask rows ⟨j,hj⟩ : ℤ) i = _
        rw [Function.update_of_ne (by omega)]
        exact hkeep i hi
    case done =>
      intro σ _ h
      exact h
    case bound =>
      rintro j _ hj _ ⟨r,μ',rfl,_,_,_⟩
      light_side
    case after =>
      rintro _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
      have hb := hprefix J
      light_set (subsetMask (indexSet (flat rows)) : ℕ) using prefixMask_all
      have hfull : (packedMasks rows).take J = packedMasks rows := by
        simpa only [packedMasks_length] using (List.take_length (l := packedMasks rows))
      exact ⟨by simp,hfull ▸ hseg,hkeep⟩
  · have hJ : J = 0 := by omega
    subst J
    have hmask : subsetMask (indexSet (flat rows)) = 0 := by
      rw [← prefixMask_all]
      exact prefixMask_zero rows
    light_set (0 : ℕ) using powTableTime
    exact ⟨by simp [hmask],by simp [packedMasks,SegN],SameOn.refl⟩

def program : Program := [body 1,powTableBody]

theorem program_meets {μ : ℕ → ℤ} {J L src dst work d : ℕ} (rows : Fin J → Finset (Fin L))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+J ≤ work) (hdst : dst+J ≤ work) (hsep : Apart src J dst J)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(J*L+1) : ℕ) : ℤ) ≤ lim.word)
    (hread : SegN μ src (rawMasks rows)) (hd : d+1 ≤ lim.depth) :
    Meets lim program 0 d [J,L,src,dst,work] μ (time J L)
      (fun r μ' => r = (subsetMask (indexSet (flat rows)) : ℤ) ∧
        SegN μ' dst (packedMasks rows) ∧ KeptBut μ μ' work dst J) :=
  meets rfl rfl rows hw hsrc hdst hsep hspace hword hread hd

theorem time_bound (J L : ℕ) : time J L ≤ 300*(J+L+1) := by
  unfold time powTableTime
  omega

end ThreeSum.LightBlockMasks
