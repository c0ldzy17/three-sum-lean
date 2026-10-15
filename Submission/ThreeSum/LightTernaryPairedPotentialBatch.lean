import Submission.ThreeSum.LightTernaryPairedPotential

noncomputable section
namespace ThreeSum.LightTernaryPairedPotentialBatch
open Light LightTernaryPairedPotential
open scoped BigOperators
set_option maxHeartbeats 2000000

def body (pPotential : ℕ) : Stmt :=
  .set 5 (k 0) ;;
  .for 6 (v 2) (
    .call pPotential [v 0 +' v 6 *' (v 1 *' v 1 *' v 1 *' v 1),v 1,v 3,v 4] 7 ;;
    .set 5 (v 5 +' v 7)) ;;
  .set 0 (v 5)

def time (K Λ H : ℕ) : ℕ := H*(LightTernaryPairedPotential.time K Λ+100)+50

def term (K base Λ : ℕ) (μ : ℕ→ℤ) (i : ℕ) : ℤ :=
  LightTernaryPairedPotential.prefixSum K (base+i*Λ^4) Λ μ (Λ^TernaryPairedColumnEnumeration.width K)

def total (K base Λ : ℕ) (μ : ℕ→ℤ) (H : ℕ) : ℤ := ∑ i∈Finset.range H, term K base Λ μ i

def Inv (K base Λ H cols powers cutoff : ℕ) (μ : ℕ→ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (ret : ℤ) (ν : ℕ→ℤ),
    σ=⟨frame [base,Λ,H,cols,powers,total K base Λ μ i,i,ret],ν⟩ ∧ Kept μ ν cutoff

theorem meets {lim : Limits} {P : Program} {pMain pPotential pPowers pRow pDigit pDivide pPoly d : ℕ}
    (K base Λ H cols powers cutoff : ℕ) (μ : ℕ→ℤ)
    (hmain : P[pMain]?=some (body pPotential))
    (hPotential : P[pPotential]?=some (LightTernaryPairedPotential.body K pPowers pRow pPoly))
    (hPowers : P[pPowers]?=some powTableBody)
    (hRow : P[pRow]?=some (LightWeightRow.body pDigit))
    (hDigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hDivide : P[pDivide]?=some LightSmallDivide.body)
    (hPoly : P[pPoly]?=some (LightTernaryPairedPolynomial.body K))
    (hΛ : 1≤Λ) (hw : (lim.space : ℤ)≤lim.word) (hd : d+3<lim.depth)
    (hcut : base+H*Λ^4≤cutoff) (hcutSpace : cutoff≤lim.space)
    (hcols : cols+TernaryPairedColumnEnumeration.width K≤lim.space)
    (hpowers : powers+(TernaryPairedColumnEnumeration.width K+1)≤lim.space)
    (hcutCols : cutoff≤cols) (hcutPowers : cutoff≤powers)
    (hApart : Apart powers (TernaryPairedColumnEnumeration.width K+1) cols (TernaryPairedColumnEnumeration.width K))
    (U : ℤ) (hU : 0≤U) (hread : ∀ i<H, ∀ q<Λ^4, |μ (base+i*Λ^4+q)|≤U)
    (hKernelWord : LightTernaryPairedPotential.word K Λ U≤lim.word)
    (hPolyWord : (LightTernaryPairedPolynomial.polynomial K).coefficient*
      (U+1)^(LightTernaryPairedPolynomial.polynomial K).degree≤lim.word)
    (hSumWord : (H : ℤ)*(Λ^TernaryPairedColumnEnumeration.width K : ℕ)*
      (LightTernaryPairedPolynomial.polynomial K).bound U≤lim.word)
    (hHword : (H : ℤ)≤lim.word) :
    Meets lim P pMain d [base,Λ,H,cols,powers] μ (time K Λ H)
      (fun r ν => r=total K base Λ μ H ∧ Kept μ ν cutoff) := by
  let E : ℤ := (Λ^TernaryPairedColumnEnumeration.width K : ℕ)*
    (LightTernaryPairedPolynomial.polynomial K).bound U
  have hPolyBound : 1≤(LightTernaryPairedPolynomial.polynomial K).bound U :=
    (LightTernaryPairedPolynomial.polynomial K).bound_pos hU
  have hE : 0≤E := mul_nonneg (Int.natCast_nonneg _) (by omega)
  have hterm (i : ℕ) (hi : i<H) : |term K base Λ μ i|≤E :=
    LightTernaryPairedPotential.prefixSum_abs_le K (base+i*Λ^4) Λ μ U hU hΛ (hread i hi) _
  have htotal (i : ℕ) (hi : i≤H) : |total K base Λ μ i|≤lim.word := by
    have hh : |total K base Λ μ i|≤(i : ℤ)*E := by
      unfold total
      calc
        _ ≤ ∑ j∈Finset.range i, |term K base Λ μ j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ _j∈Finset.range i, E := Finset.sum_le_sum fun j hj => hterm j (by have := Finset.mem_range.mp hj; omega)
        _ = _ := by simp
    have hb : (i : ℤ)*E≤(H : ℤ)*E := mul_le_mul_of_nonneg_right (by exact_mod_cast hi) hE
    exact hh.trans (hb.trans (by simpa [E,mul_assoc] using hSumWord))
  have hΛword : (Λ : ℤ)≤lim.word := by
    have hp : 0≤LightTernaryPairedPotential.word K Λ U := by
      unfold LightTernaryPairedPotential.word
      have := (LightTernaryPairedPolynomial.polynomial K).bound_pos hU
      positivity
    unfold LightTernaryPairedPotential.word at hKernelWord
    have := (LightTernaryPairedPolynomial.polynomial K).bound_pos hU
    push_cast at hKernelWord
    nlinarith [Nat.zero_le (Λ^(TernaryPairedColumnEnumeration.width K+1)),Nat.zero_le (Λ^TernaryPairedColumnEnumeration.width K)]
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℤ)
  refine Ends.pieceThen (Ends.for (T := H*(LightTernaryPairedPotential.time K Λ+90)+20)
    (Q := Inv K base Λ H cols powers cutoff μ H)
    (Inv K base Λ H cols powers cutoff μ) H (LightTernaryPairedPotential.time K Λ+80)
    ?_ ?_ ?_ ?_ (hT := by light_time)) ?_ (hT := by light_time)
  · refine ⟨0,μ,?_,by intro x hx; rfl⟩
    simp [Inv,total,update_frame_setLocal]
    exact (frame_append_zeros ([base,Λ,H,cols,powers,0,0] : List ℤ) 1).symm
  · rintro i _ hi _ ⟨ret,ν,rfl,hkeep⟩
    have hiM : i*Λ^4+Λ^4≤H*Λ^4 := by nlinarith [Nat.mul_le_mul_right (Λ^4) (by omega : i+1≤H)]
    have hcurrent (q : ℕ) (hq : q<Λ^4) : ν (base+i*Λ^4+q)=μ (base+i*Λ^4+q) := hkeep _ (by omega)
    have hp := LightTernaryPairedPotential.meets K (base+i*Λ^4) Λ cols powers ν
      hPotential hPowers hRow hDigit hDivide hPoly hΛ hw (by omega) (by omega) hcols hpowers
      (Or.inl (by omega)) (Or.inl (by omega)) hApart U hU
      (by intro q hq; rw [hcurrent q hq]; exact hread i hi q hq) hKernelWord hPolyWord
    have hΛ4Nat : Λ^4≤lim.space := by
      have hh : Λ^4≤H*Λ^4 := by
        simpa only [one_mul] using Nat.mul_le_mul_right (Λ^4) (by omega : 1≤H)
      omega
    have hΛ4Word : (Λ : ℤ)^4≤lim.word := (by exact_mod_cast hΛ4Nat : (Λ : ℤ)^4≤lim.space).trans hw
    have hΛ2Word : (Λ : ℤ)^2≤lim.word := (by exact_mod_cast Nat.pow_le_pow_right hΛ (by decide : 2≤4) : (Λ : ℤ)^2≤(Λ : ℤ)^4).trans hΛ4Word
    have hΛ3Word : (Λ : ℤ)^3≤lim.word := (by exact_mod_cast Nat.pow_le_pow_right hΛ (by decide : 3≤4) : (Λ : ℤ)^3≤(Λ : ℤ)^4).trans hΛ4Word
    have hΛ2Pos : 0≤(Λ : ℤ)^2 := by positivity
    have hΛ3Pos : 0≤(Λ : ℤ)^3 := by positivity
    have hΛ4Pos : 0≤(Λ : ℤ)^4 := by positivity
    have hΛ2mul : (Λ : ℤ)*Λ≤lim.word := by simpa only [pow_two] using hΛ2Word
    have hΛ3mul : (Λ : ℤ)*Λ*Λ≤lim.word := by simpa only [pow_succ,pow_zero,one_mul] using hΛ3Word
    have hΛ4mul : (Λ : ℤ)*Λ*Λ*Λ≤lim.word := by simpa only [pow_succ,pow_zero,one_mul] using hΛ4Word
    have hΛ2mulPos : 0≤(Λ : ℤ)*Λ := by positivity
    have hΛ3mulPos : 0≤(Λ : ℤ)*Λ*Λ := by positivity
    have hΛ4mulPos : 0≤(Λ : ℤ)*Λ*Λ*Λ := by positivity
    have hProdEq : (Λ : ℤ)*Λ*Λ*Λ=(Λ : ℤ)^4 := by ring
    have hiProdPos : 0≤(i : ℤ)*((Λ : ℤ)*Λ*Λ*Λ) := by positivity
    have hiProdWord : (i : ℤ)*((Λ : ℤ)*Λ*Λ*Λ)≤lim.word := by
      rw [hProdEq]
      have hh : i*Λ^4≤lim.space := by omega
      exact (by exact_mod_cast hh : (i : ℤ)*(Λ : ℤ)^4≤lim.space).trans hw
    have haddrWord : (base : ℤ)+(i : ℤ)*((Λ : ℤ)*Λ*Λ*Λ)≤lim.word := by
      rw [hProdEq]
      have hh : base+i*Λ^4≤lim.space := by omega
      exact (by exact_mod_cast hh : (base : ℤ)+(i : ℤ)*(Λ : ℤ)^4≤lim.space).trans hw
    light_call hp using pow_succ with result ξ ⟨hresult,hTkeep,hprefix⟩
    have hkeep' : Kept μ ξ cutoff := by
      intro x hx
      exact (hprefix x (by omega)).trans (hkeep x hx)
    have he : result=term K base Λ μ i := by
      rw [hresult]
      unfold term LightTernaryPairedPotential.prefixSum
      apply Finset.sum_congr rfl
      intro j hj
      unfold LightTernaryPairedPotential.term
      congr 1
      funext q
      exact hcurrent _ (LightTernaryPairedPolynomial.tensorIndex_lt
        (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
        (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)))
    have ha := htotal i (by omega)
    have hb := hterm i hi
    have hbWord : |term K base Λ μ i|≤lim.word := by
      have hpE : E≤(H : ℤ)*E := by nlinarith
      exact hb.trans (hpE.trans (by simpa [E,mul_assoc] using hSumWord))
    have hn := htotal (i+1) (by omega)
    have ⟨haLo,haHi⟩ := abs_le.mp ha
    have ⟨hbLo,hbHi⟩ := abs_le.mp hbWord
    have ⟨hnLo,hnHi⟩ := abs_le.mp hn
    have hsucc : total K base Λ μ (i+1)=total K base Λ μ i+term K base Λ μ i := Finset.sum_range_succ _ _
    light_set (total K base Λ μ (i+1)) using he,hsucc
    refine ⟨by simp,result,ξ,?_,hkeep'⟩
    simp [update_frame_setLocal]
  · intro σ hcounter hinv
    exact hinv
  · rintro i _ hi _ ⟨ret,ν,rfl,hkeep⟩
    light_side
  · rintro σ ⟨ret,ν,rfl,hkeep⟩
    have ha := htotal H le_rfl
    have ⟨haLo,haHi⟩ := abs_le.mp ha
    light_set (total K base Λ μ H)
    exact ⟨rfl,hkeep⟩

end ThreeSum.LightTernaryPairedPotentialBatch
