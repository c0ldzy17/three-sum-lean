import Submission.ThreeSum.LightSubsetEnumeration

/-!
# A fixed subset-layer enumerator with its own power-table construction

The main theorem has no supplied lookup-table correctness assumption. The
only auxiliary memory is a table of `L+1` powers of two, built once before
the recursive enumeration. The output has exactly `L.choose k` cells.
-/

namespace ThreeSum.LightSubsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def body (pPowers pEnum : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 4 ;;
  .call pEnum [v 0,v 1,k 0,v 2,v 3] 0

def time (L k : ℕ) : ℕ := powTableTime (L+1)+LightSubsetEnumeration.time L k+40

theorem meets {pMain pPowers pEnum : ℕ}
    (hmain : P[pMain]? = some (body pPowers pEnum))
    (hpowers : P[pPowers]? = some powTableBody)
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {L k dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hk : k ≤ L+1) (hdst : dst+L.choose k ≤ work)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [L,k,dst,work] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        SegN μ' dst (enumerateLayer L k) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (L.choose k)) := by
  have hpositive := LightSubsetEnumeration.work_pos L k
  have htime : 150 ≤ LightSubsetEnumeration.time L k :=
    Nat.mul_le_mul_left 150 hpositive
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hb : (2^1 : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : (2 : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ) := by exact_mod_cast hb
    exact hz.trans hword
  apply Meets.of_body hmain
  unfold body time
  have hpow := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := L+1) (b := 2) hpowers hw hspace (by
      intro j hj
      have hb : (2^j : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) hj
      have hz : ((2^j : ℕ) : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ) := by exact_mod_cast hb
      exact hz.trans hword)
  light_call hpow using powTableTime,LightSubsetEnumeration.time
    with _ μ₁ ⟨hpowSeg,hsame₀⟩
  have hpowSpec := powers_of_segment hpowSeg
  have hcall := LightSubsetEnumeration.meets henum hw hspace hword
    L k 0 dst μ₁ le_rfl hk (by simp) hdst hpowSpec (d+1) (by omega)
  light_call hcall using powTableTime,LightSubsetEnumeration.time
    with res μ₂ ⟨hres,hseg,hsame₁⟩
  refine ⟨by simpa using hres,?_,?_,?_⟩
  · simpa [LightSubsetEnumeration.output] using hseg
  · intro i hi
    change μ₂ (work+i) = _
    rw [hsame₁ (work+i) (Or.inr (by omega))]
    exact hpowSpec i hi
  · intro a ha
    exact (hsame₁ a ha.2).trans (hsame₀ a (Or.inl ha.1))

def program : Program := [body 1 2,powTableBody,LightSubsetEnumeration.body 2]

theorem program_meets {μ : ℕ → ℤ} {L k dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hk : k ≤ L+1) (hdst : dst+L.choose k ≤ work)
    (hd : d+L+1 ≤ lim.depth) :
    Meets lim program 0 d [L,k,dst,work] μ (time L k)
      (fun r μ' => r = (L.choose k : ℤ) ∧
        SegN μ' dst (enumerateLayer L k) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (L.choose k)) :=
  meets rfl rfl rfl hw hspace hword hk hdst hd

theorem time_bound (L k : ℕ) : time L k ≤ 800*(L+1)*(L.choose k+1) := by
  have h := LightSubsetEnumeration.time_bound L k
  unfold time powTableTime
  nlinarith

end ThreeSum.LightSubsetEnumerationSetup
