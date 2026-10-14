import Submission.ThreeSum.LightTernaryEnumeration
import Submission.ThreeSum.TernaryBankEnumeration

/-!
# A closed machine program for compressed ternary bank enumeration

The program constructs its own power table and then invokes the verified
three-way pruned enumeration.  Its output is exactly the sorted canonical
address bank, whose length has the ternary Gibbs bound.
-/

namespace ThreeSum.LightTernaryEnumerationSetup

open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryAddresses

variable {lim : Limits} {P : Program}

def body (pPowers pEnum : ℕ) : Stmt :=
  .call pPowers [v 3,k 2 *' v 0 +' k 1,k 2] 4 ;;
  .call pEnum [v 0,v 1,k 0,v 2,v 3] 0

def time (N T : ℕ) : ℕ := powTableTime (2*N+1)+LightTernaryEnumeration.time N T+40

theorem meets {pMain pPowers pEnum : ℕ}
    (hmain : P[pMain]? = some (body pPowers pEnum))
    (hpowers : P[pPowers]? = some powTableBody)
    (henum : P[pEnum]? = some (LightTernaryEnumeration.body pEnum))
    {μ : ℕ → ℤ} {N T dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*N+1) ≤ lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : T ≤ 2*N) (hdst : dst+(codes N T).length ≤ work)
    (hd : d+N+2 ≤ lim.depth) :
    Meets lim P pMain d [N,T,dst,work] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst ((codes N T).map (fun (a : ℕ) => (a : ℤ))) ∧
        Powers μ' work (2*N) ∧ KeptBut μ μ' work dst (codes N T).length) := by
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hb : (2 : ℕ) ≤ 4^(N+1) := by
      have hp : 0 < (4 : ℕ)^N := by positivity
      rw [pow_succ]
      omega
    exact (show (2 : ℤ) ≤ ((4^(N+1) : ℕ) : ℤ) by exact_mod_cast hb).trans hword
  have hpowBound : ∀ j ≤ 2*N+1, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    have hle : (2^j : ℕ) ≤ 4^(N+1) := by
      rw [← LightTernaryEnumeration.pow_two_even]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (show ((2^j : ℕ) : ℤ) ≤ ((4^(N+1) : ℕ) : ℤ) by exact_mod_cast hle).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hpow := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := 2*N+1) (b := 2) hpowers hw hspace hpowBound
  light_call hpow using powTableTime,LightTernaryEnumeration.time
    with _ μ₁ ⟨hpowSeg,hsame₀⟩
  have hpowSpec := powers_of_segment hpowSeg
  have hcall := LightTernaryEnumeration.meets (W := N) henum hw hspace hword
    N T 0 dst μ₁ le_rfl hcut (by simp) hdst hpowSpec (d+1) (by omega)
  light_call hcall using powTableTime,LightTernaryEnumeration.time
    with res μ₂ ⟨hres,hseg,hsame₁⟩
  refine ⟨hres,?_,?_,?_⟩
  · simpa [LightTernaryEnumeration.output, List.bind_eq_flatMap,
      ← List.map_eq_flatMap] using hseg
  · intro i hi
    change μ₂ (work+i) = _
    rw [hsame₁ (work+i) (Or.inr (by omega))]
    exact hpowSpec i hi
  · intro a ha
    exact (hsame₁ a ha.2).trans (hsame₀ a (Or.inl ha.1))

def program : Program := [body 1 2,powTableBody,LightTernaryEnumeration.body 2]

theorem program_meets {μ : ℕ → ℤ} {N T dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*N+1) ≤ lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ) ≤ lim.word)
    (hcut : T ≤ 2*N) (hdst : dst+(codes N T).length ≤ work)
    (hd : d+N+2 ≤ lim.depth) :
    Meets lim program 0 d [N,T,dst,work] μ (time N T)
      (fun r μ' => r = ((codes N T).length : ℤ) ∧
        Seg μ' dst ((codes N T).map (fun (a : ℕ) => (a : ℤ))) ∧
        Powers μ' work (2*N) ∧ KeptBut μ μ' work dst (codes N T).length) :=
  meets rfl rfl rfl hw hspace hword hcut hdst hd

theorem time_bound (N T : ℕ) :
    time N T ≤ 500*(N+1)*((codes N T).length+1) := by
  have he := LightTernaryEnumeration.time_bound N T
  have hp : 0 < (codes N T).length := by
    simpa only [codes_length] using ThreeSum.TernaryEnumeration.words_nonempty N T
  unfold time powTableTime
  nlinarith

end ThreeSum.LightTernaryEnumerationSetup
