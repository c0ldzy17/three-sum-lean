import Submission.ThreeSum.LightHashHistogram

/-!
# Preserving completed candidate tables during local hash construction

This proves a stronger preservation conclusion for the existing actual
hash/residue/histogram program, with its original input and resource
conditions. It lets successive local candidates retain earlier coefficient,
histogram, and cover-matrix rows above the temporary raw/code arrays.
-/

namespace ThreeSum.LightLocalCoverHashHistogram

open Light LightHashHistogram

def Preserved (μ ν : ℕ → ℤ) (work raw codes hist n p : ℕ) : Prop :=
  ∀ a, a < work → Outside raw n a → Outside codes n a → Outside hist p a → ν a = μ a

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain : ℕ} (S : LightHashHistogram.Procs P pMain)
    {μ : ℕ → ℤ} {L masks raw codes hist n src0 src1 p work U : ℕ}
    (mask w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hp : 0 < p) (hspace : space work L U ≤ lim.space)
    (hmasks : masks+n ≤ raw) (hsrc0 : src0+L ≤ raw) (hsrc1 : src1+L ≤ raw)
    (hraw : raw+n ≤ codes) (hcodes : codes+n ≤ hist) (hhist : hist+p ≤ work)
    (hword : (word L p U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L,masks,raw,codes,hist,n,src0,src1,p,work] μ (time L n p U)
      (fun _ μ' =>
        (∀ i < n, μ' (codes+i) = (code L p mask w0 w1 i : ℤ)) ∧
        (∀ r < p, μ' (hist+r) = (LightHistogram.count (code L p mask w0 w1) r n : ℤ)) ∧
        Kept μ μ' raw ∧ Preserved μ μ' work raw codes hist n p) := by
  have hspow : work+(L+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hsmod : work+(Nat.log 2 (L*U+1)+2) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hsw : work ≤ lim.space := by omega
  have hhashWord : (LightOneHot.word L U : ℤ) ≤ lim.word := by
    have hh : LightOneHot.word L U ≤ word L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hmodWord : (4*(L*U : ℕ)+4*p+16 : ℤ) ≤ lim.word := by
    have hh : 4*(L*U)+4*p+16 ≤ word L p U := by unfold word; omega
    exact (by exact_mod_cast hh : (4*(L*U : ℕ)+4*p+16 : ℤ) ≤ (word L p U : ℤ)).trans hword
  apply Meets.of_body S.main
  unfold body time
  have hh := LightMaskHashes.meets (d := d+1) (μ := μ) (L := L) (masks := masks)
    (dst := raw) (n := n) (src0 := src0) (src1 := src1) (work := work) (U := U)
    S.hashes S.powers S.onehot mask w0 w1 hw (by omega) hspow hmasks hsrc0 hsrc1
    (by omega) hhashWord hmaskRead hmaskLt hread0 hread1 hbound0 hbound1
  light_call hh using LightMaskHashes.time,LightOneHot.time,LightResidues.residuesTime,
    LightResidues.residueBudget,LightHistogram.histogramTime,LightHistogram.countTime
    with value₀ μ₁ ⟨rawValues,_,kept₁⟩
  have hrawBound : ∀ i < n, |μ₁ (raw+i)| ≤ ((L*U : ℕ) : ℤ) := by
    intro i hi
    rw [rawValues i hi,abs_of_nonneg (Int.natCast_nonneg _)]
    exact Int.ofNat_le.mpr (OneHotMask.eval_le (m := mask i) hbound0 hbound1)
  have hr := LightResidues.residues_meets (d := d+1) (μ := μ₁)
    (src := raw) (dst := codes) (n := n) (p := p) (work := work) (U := L*U) (c := 1)
    S.residues S.emod hw (by omega) hp (by omega) (by omega) hsmod (Or.inl hraw)
    (by norm_num) hmodWord hrawBound
  light_call hr using LightMaskHashes.time,LightOneHot.time,LightResidues.residuesTime,
    LightResidues.residueBudget,LightHistogram.histogramTime,LightHistogram.countTime
    with value₁ μ₂ ⟨residueValues,kept₂⟩
  have hcodeValues : ∀ i < n, μ₂ (codes+i) = (code L p mask w0 w1 i : ℤ) := by
    intro i hi
    rw [residueValues i hi,rawValues i hi]
    rfl
  have hcodeLt : ∀ i < n, code L p mask w0 w1 i < p := by
    intro i hi
    exact LightResidues.residue_lt hp 1 _
  have hh := LightHistogram.histogram_meets (d := d+1) (μ := μ₂)
    (src := codes) (dst := hist) (n := n) (p := p) S.hist S.fill
    (code L p mask w0 w1) hw (by omega) (by omega) (by omega) (Or.inl hcodes)
    hcodeValues hcodeLt
  light_call hh using LightMaskHashes.time,LightOneHot.time,LightResidues.residuesTime,
    LightResidues.residueBudget,LightHistogram.histogramTime,LightHistogram.countTime
    with value₂ μ₃ ⟨counts,kept₃⟩
  refine ⟨?_,counts,?_,?_⟩
  · intro i hi
    change μ₃ (codes+i) = _
    rw [kept₃ _ (Or.inl (by omega))]
    exact hcodeValues i hi
  · intro a ha
    change μ₃ a = μ a
    rw [kept₃ _ (Or.inl (by omega)),kept₂ _ ⟨by omega,Or.inl (by omega)⟩]
    exact kept₁ a ⟨by omega,Or.inl ha⟩
  · intro a ha hrawOut hcodeOut hhistOut
    change μ₃ a = μ a
    rw [kept₃ a hhistOut,kept₂ a ⟨ha,hcodeOut⟩]
    exact kept₁ a ⟨ha,hrawOut⟩

end ThreeSum.LightLocalCoverHashHistogram
