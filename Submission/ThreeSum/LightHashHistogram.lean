import Submission.ThreeSum.LightMaskHashes
import Submission.ThreeSum.LightResidues
import Submission.ThreeSum.LightHistogram

/-!
# One-hot mask hashes through actual residues and bucket counts

The complete wrapper constructs raw hashes, canonical residue codes, and
the histogram. Both code and histogram arrays are retained for the later
pair-trimming pass; every earlier input cell is preserved.
-/

namespace ThreeSum.LightHashHistogram

open Light

def code (L p : ℕ) (mask w0 w1 : ℕ → ℕ) (i : ℕ) : ℕ :=
  LightResidues.residue p 1 (OneHotMask.eval w0 w1 L (mask i) : ℤ)

def body (pHashes pResidues pHist : ℕ) : Stmt :=
  .call pHashes [v 0,v 1,v 2,v 5,v 6,v 7,v 9] 10 ;;
  .call pResidues [v 2,v 3,v 5,v 8,v 9,k 1] 10 ;;
  .call pHist [v 3,v 4,v 5,v 8] 10

def time (L n p U : ℕ) : ℕ := LightMaskHashes.time L n+
  LightResidues.residuesTime n (L*U)+LightHistogram.histogramTime n p+100

def word (L p U : ℕ) : ℕ := LightOneHot.word L U+4*(L*U)+4*p+16

def space (work L U : ℕ) : ℕ := work+max (L+1) (Nat.log 2 (L*U+1)+2)

structure Procs (P : Program) (pMain : ℕ) where
  pHashes : ℕ
  pPowers : ℕ
  pOneHot : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHist : ℕ
  pFill : ℕ
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pOneHot)
  powers : P[pPowers]? = some powTableBody
  onehot : P[pOneHot]? = some (LightOneHot.body pOneHot)
  residues : P[pResidues]? = some (LightResidues.residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  hist : P[pHist]? = some (LightHistogram.histogramBody pFill)
  fill : P[pFill]? = some fillBody
  main : P[pMain]? = some (body pHashes pResidues pHist)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
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
        Kept μ μ' raw) := by
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
    with v μ₁ ⟨rawValues,_,kept₁⟩
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
    with v μ₂ ⟨residueValues,kept₂⟩
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
    with v μ₃ ⟨counts,kept₃⟩
  refine ⟨?_,counts,?_⟩
  · intro i hi
    change μ₃ (codes+i) = _
    rw [kept₃ _ (Or.inl (by omega))]
    exact hcodeValues i hi
  · intro a ha
    change μ₃ a = μ a
    rw [kept₃ _ (Or.inl (by omega)),kept₂ _ ⟨by omega,Or.inl (by omega)⟩]
    exact kept₁ a ⟨by omega,Or.inl ha⟩

def program : Program :=
  [body 1 4 6,LightMaskHashes.body 2 3,powTableBody,LightOneHot.body 3,
    LightResidues.residuesBody 5,emodBody,LightHistogram.histogramBody 7,fillBody]

def programProcs : Procs program 0 := ⟨1,2,3,4,5,6,7,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

end ThreeSum.LightHashHistogram
