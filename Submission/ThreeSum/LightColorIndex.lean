import Submission.ThreeSum.LightMaskErase
import Submission.ThreeSum.MaskDecode
import Submission.ThreeSum.Coloring

/-!
# Actual evaluation of one member of the deterministic coloring family

Two calls to the checked mask-coordinate routine inspect the selected bits
of an original array index. Four literal color arguments determine the map
from bit patterns to the three colors. The cost is linear in the binary
width and independent of the numeric index magnitude.
-/

namespace ThreeSum.LightColorIndex

open Light LightSubsetAddress

variable {lim : Limits} {P : Program}

theorem erase_eq_iff_testBit_false {W m : ℕ} (hm : m < 2^W) (i : Fin W) :
    MaskErase.eraseMask W i.val m = m ↔ m.testBit i.val = false := by
  have h := MaskErase.eraseMask_ne_iff (MaskDecode.decode W m) i
  rw [MaskDecode.subsetMask_decode hm] at h
  simp only [MaskDecode.decode,Finset.mem_filter,Finset.mem_univ,true_and,
    Nat.mem_bitIndices] at h
  cases hb : m.testBit i.val <;> simp_all

def color {W : ℕ} (p : Coloring.Parameter W) (m : ℕ) : ℕ :=
  (p.2 (m.testBit p.1.1.val,m.testBit p.1.2.val)).val

theorem color_lt {W : ℕ} (p : Coloring.Parameter W) (m : ℕ) : color p m < 3 :=
  (p.2 _).isLt

/-- Width, index, two bit coordinates, four color-map entries, powers base. -/
def body (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 2,v 1,v 0,v 8] 9 ;;
  .call pErase [v 0,v 3,v 1,v 0,v 8] 10 ;;
  .ite (v 9 =' v 1)
    (.ite (v 10 =' v 1) (.set 0 (v 4)) (.set 0 (v 5)))
    (.ite (v 10 =' v 1) (.set 0 (v 6)) (.set 0 (v 7)))

def time (W : ℕ) : ℕ := 2*LightMaskErase.time W+150

theorem meets {pMain pErase W m powers d : ℕ}
    (hmain : P[pMain]? = some (body pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W) (hm : m < 2^W) (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,m,p.1.1.val,p.1.2.val,
      (p.2 (false,false)).val,(p.2 (false,true)).val,
      (p.2 (true,false)).val,(p.2 (true,true)).val,powers] μ (time W)
      (fun r μ' => r = (color p m : ℤ) ∧ μ' = μ) := by
  have ha := p.1.1.isLt
  have hb := p.1.2.isLt
  have h00 := (p.2 (false,false)).isLt
  have h01 := (p.2 (false,true)).isLt
  have h10 := (p.2 (true,false)).isLt
  have h11 := (p.2 (true,true)).isLt
  have htwo : (2 : ℤ) ≤ lim.word := by
    have h2 : 2^1 ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast h2 : (2 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  have hmWord : (m : ℤ) ≤ lim.word := by
    have hpow : 2^W ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (Int.ofNat_le.mpr (by omega : m ≤ 2^(W+1))).trans hword
  apply Meets.of_body hmain
  unfold body time
  light_call (LightMaskErase.meets herase μ hw hspace hword hpowers
    W p.1.1.val m le_rfl (by omega) hm (d+1) (by omega))
    using LightMaskErase.time with erasedA μ₁ ⟨hA,hmemA⟩
  subst μ₁
  light_call (LightMaskErase.meets herase μ hw hspace hword hpowers
    W p.1.2.val m le_rfl (by omega) hm (d+1) (by omega))
    using LightMaskErase.time with erasedB μ₂ ⟨hB,hmemB⟩
  subst μ₂
  light_if heA hnA : erasedA = (m : ℤ) using LightMaskErase.time
  · have hbitA := (erase_eq_iff_testBit_false hm p.1.1).mp
      (by exact_mod_cast hA.symm.trans heA)
    light_if heB hnB : erasedB = (m : ℤ) using LightMaskErase.time
    · have hbitB := (erase_eq_iff_testBit_false hm p.1.2).mp
        (by exact_mod_cast hB.symm.trans heB)
      light_set ((p.2 (false,false)).val : ℕ) using LightMaskErase.time
      exact ⟨by simp [color,hbitA,hbitB],rfl⟩
    · have hbitB : m.testBit p.1.2.val = true := by
        cases h : m.testBit p.1.2.val
        · have he := (erase_eq_iff_testBit_false hm p.1.2).mpr h
          exact False.elim (hnB (by simpa [he] using hB))
        · rfl
      light_set ((p.2 (false,true)).val : ℕ) using LightMaskErase.time
      exact ⟨by simp [color,hbitA,hbitB],rfl⟩
  · have hbitA : m.testBit p.1.1.val = true := by
      cases h : m.testBit p.1.1.val
      · have he := (erase_eq_iff_testBit_false hm p.1.1).mpr h
        exact False.elim (hnA (by simpa [he] using hA))
      · rfl
    light_if heB hnB : erasedB = (m : ℤ) using LightMaskErase.time
    · have hbitB := (erase_eq_iff_testBit_false hm p.1.2).mp
        (by exact_mod_cast hB.symm.trans heB)
      light_set ((p.2 (true,false)).val : ℕ) using LightMaskErase.time
      exact ⟨by simp [color,hbitA,hbitB],rfl⟩
    · have hbitB : m.testBit p.1.2.val = true := by
        cases h : m.testBit p.1.2.val
        · have he := (erase_eq_iff_testBit_false hm p.1.2).mpr h
          exact False.elim (hnB (by simpa [he] using hB))
        · rfl
      light_set ((p.2 (true,true)).val : ℕ) using LightMaskErase.time
      exact ⟨by simp [color,hbitA,hbitB],rfl⟩

def program : Program := [body 1,LightMaskErase.body 1]

theorem program_meets {W m powers d : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W) (hm : m < 2^W) (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,m,p.1.1.val,p.1.2.val,
      (p.2 (false,false)).val,(p.2 (false,true)).val,
      (p.2 (true,false)).val,(p.2 (true,true)).val,powers] μ (time W)
      (fun r μ' => r = (color p m : ℤ) ∧ μ' = μ) :=
  meets rfl rfl μ p hw hspace hword hpowers hm hd

theorem time_bound (W : ℕ) : time W ≤ 300*(W+1) := by
  unfold time LightMaskErase.time
  omega

end ThreeSum.LightColorIndex
