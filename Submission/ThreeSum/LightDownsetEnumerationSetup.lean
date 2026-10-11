import Submission.ThreeSum.LightDownsetEnumeration

/-!
# A complete fixed program for compact downset enumeration

The main routine builds one power table and enumerates every layer through
the given cutoff into adjacent output cells. Its specification names the
exact compact list and bounds actual benchmark-language execution time.
-/

namespace ThreeSum.LightDownsetEnumerationSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def body (pPowers pDownset : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 4 ;;
  .call pDownset [v 0,v 1,v 2,v 3] 0

def time (L cut : ℕ) : ℕ := powTableTime (L+1)+LightDownsetEnumeration.time L cut+40

theorem meets {pMain pPowers pDownset pEnum : ℕ}
    (hmain : P[pMain]? = some (body pPowers pDownset))
    (hpowers : P[pPowers]? = some powTableBody)
    (hdownset : P[pDownset]? = some (LightDownsetEnumeration.body pEnum))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {L cut dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ work)
    (hd : d+L+2 ≤ lim.depth) :
    Meets lim P pMain d [L,cut,dst,work] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (downsetCap L cut)) := by
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
  light_call hpow using powTableTime,LightDownsetEnumeration.time
    with _ μ₁ ⟨hpowSeg,hsame₀⟩
  have hpowSpec := powers_of_segment hpowSeg
  have hcall := LightDownsetEnumeration.meets (d := d+1) hdownset henum
    hw hspace hword hcut hdst hpowSpec (by omega)
  light_call hcall using powTableTime,LightDownsetEnumeration.time
    with res μ₂ ⟨hres,hseg,hsame₁⟩
  refine ⟨by simpa using hres,hseg,?_,?_⟩
  · intro i hi
    change μ₂ (work+i) = _
    rw [hsame₁ (work+i) (Or.inr (by omega))]
    exact hpowSpec i hi
  · intro a ha
    exact (hsame₁ a ha.2).trans (hsame₀ a (Or.inl ha.1))

def program : Program :=
  [body 1 2,powTableBody,LightDownsetEnumeration.body 3,LightSubsetEnumeration.body 3]

theorem program_meets {μ : ℕ → ℤ} {L cut dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : cut ≤ L) (hdst : dst+downsetCap L cut ≤ work)
    (hd : d+L+2 ≤ lim.depth) :
    Meets lim program 0 d [L,cut,dst,work] μ (time L cut)
      (fun r μ' => r = (downsetCap L cut : ℤ) ∧
        SegN μ' dst (enumerateDownset L cut) ∧ Powers μ' work L ∧
        KeptBut μ μ' work dst (downsetCap L cut)) :=
  meets rfl rfl rfl rfl hw hspace hword hcut hdst hd

theorem time_bound {L cut : ℕ} (hcut : cut ≤ L) :
    time L cut ≤ 1200*(L+1)^2*(downsetCap L cut+1) := by
  have h := LightDownsetEnumeration.time_bound hcut
  have hL : L+1 ≤ (L+1)^2*(downsetCap L cut+1) := by
    have hs : L+1 ≤ (L+1)^2 := by
      calc
        L+1 ≤ (L+1)*(L+1) := Nat.le_mul_of_pos_left _ (by omega)
        _ = (L+1)^2 := (pow_two _).symm
    exact hs.trans (Nat.le_mul_of_pos_right _ (by omega))
  have hp : 1 ≤ (L+1)^2*(downsetCap L cut+1) := by omega
  unfold time powTableTime
  have ht : LightDownsetEnumeration.time L cut ≤
      1000*((L+1)^2*(downsetCap L cut+1)) := by simpa only [Nat.mul_assoc] using h
  calc
    _ ≤ 1200*((L+1)^2*(downsetCap L cut+1)) := by omega
    _ = _ := by ring

end ThreeSum.LightDownsetEnumerationSetup
