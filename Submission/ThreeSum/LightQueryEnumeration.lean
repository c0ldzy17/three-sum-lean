import Submission.ThreeSum.LightQueryWeights

/-!
# A complete output-sensitive subset enumerator inside an arbitrary query mask

The routine constructs its own compact coordinate weights, then invokes
the existing recursion on the number of selected coordinates. Every emitted
word is already a global mask; no ambient layer or Boolean cube is scanned.
-/

namespace ThreeSum.LightQueryEnumeration

open Light ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress QueryCoordinates

variable {lim : Limits} {P : Program}

/-- Arguments: ambient width, query mask, missing cardinality, output base, scratch. -/
def body (pWeights pEnum : ℕ) : Stmt :=
  .set 5 (v 4 +' v 0 +' k 1) ;;
  .call pWeights [v 0,v 1,v 4,v 5] 6 ;;
  .call pEnum [v 6,v 2,k 0,v 3,v 4] 0

def time (W c t : ℕ) : ℕ :=
  LightQueryWeights.time W+LightSubsetEnumeration.time c t+60

theorem meets {pMain pWeights pPowers pErase pEnum : ℕ}
    (hmain : P[pMain]? = some (body pWeights pEnum))
    (hweights : P[pWeights]? = some (LightQueryWeights.body pPowers pErase))
    (hpowers : P[pPowers]? = some powTableBody)
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (henum : P[pEnum]? = some (LightSubsetEnumeration.body pEnum))
    {μ : ℕ → ℤ} {W t dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdst : dst+Q.card.choose t ≤ work)
    (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pMain d [W,subsetMask Q,t,dst,work] μ (time W Q.card t)
      (fun r μ' => r = (Q.card.choose t : ℤ) ∧
        SegN μ' dst ((missingSets Q t).map subsetMask) ∧
        LightWeightedEnumeration.Weights μ' work Q.card (weights Q) ∧
        KeptBut μ μ' work dst (Q.card.choose t)) := by
  have hc : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hm : (subsetMask Q : ℤ) ≤ lim.word := by
    have hh : subsetMask Q ≤ 2^(W+1) :=
      (Nat.le_of_lt (subsetMask_isMask Q).1).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hh : (subsetMask Q : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  light_set (work+W+1 : ℕ) using LightQueryWeights.time,LightSubsetEnumeration.time
  have hbuild := LightQueryWeights.meets (d := d+1) (μ := μ)
    (dst := work) (work := work+W+1) hweights hpowers herase Q
    hw (by omega) (by omega) hword (by omega)
  light_call hbuild using LightQueryWeights.time,LightSubsetEnumeration.time
    with count μ₁ ⟨hcount,hseg,_,hkept₀⟩
  have hwtable := LightQueryWeights.weights_of_segment hseg
  have henumCall := LightWeightedEnumeration.meets (W := Q.card) (U := subsetMask Q)
    henum hw (by omega) hm Q.card t 0 dst μ₁ le_rfl ht
    (by simp) hdst hwtable (d+1) (by omega)
  light_call henumCall using LightQueryWeights.time,LightSubsetEnumeration.time,hcount
    with res μ₂ ⟨hres,hout,hkept₁⟩
  refine ⟨by simpa using hres,?_,?_,?_⟩
  · simpa only [output_missingSets] using hout
  · intro i hi
    change μ₂ (work+i) = _
    rw [hkept₁ (work+i) (Or.inr (by omega))]
    exact hwtable i hi
  · intro i hi
    exact (hkept₁ i hi.2).trans (hkept₀ i ⟨by omega,Or.inl hi.1⟩)

def program : Program :=
  [body 1 4,LightQueryWeights.body 2 3,powTableBody,
    LightMaskErase.body 3,LightSubsetEnumeration.body 4]

theorem program_meets {μ : ℕ → ℤ} {W t dst work d : ℕ}
    (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1)
    (hdst : dst+Q.card.choose t ≤ work)
    (hd : d+W+2 ≤ lim.depth) :
    Meets lim program 0 d [W,subsetMask Q,t,dst,work] μ (time W Q.card t)
      (fun r μ' => r = (Q.card.choose t : ℤ) ∧
        SegN μ' dst ((missingSets Q t).map subsetMask) ∧
        LightWeightedEnumeration.Weights μ' work Q.card (weights Q) ∧
        KeptBut μ μ' work dst (Q.card.choose t)) :=
  meets rfl rfl rfl rfl rfl Q hw hspace hword ht hdst hd

theorem time_bound {W c t : ℕ} (hc : c ≤ W) :
    time W c t ≤ 1400*(W+1)^2*(c.choose t+1) := by
  have hbuild := LightQueryWeights.time_bound W
  have he := LightSubsetEnumeration.time_bound c t
  unfold time
  have hpoly : (4*c+1)*c.choose t+1 ≤ 4*(W+1)^2*(c.choose t+1) := by
    have hW : W+1 ≤ (W+1)^2 := by nlinarith
    nlinarith
  nlinarith [Nat.one_le_pow' 2 W]

end ThreeSum.LightQueryEnumeration
