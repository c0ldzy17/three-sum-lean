import Submission.ThreeSum.ModuloCounts
import Submission.ThreeSum.LightLookupSum
import Submission.ThreeSum.LightCapacity
import Submission.ThreeSum.LightCyclic

/-!
# A complete modular triple-counting procedure

Starting with three arrays of original signed integers and a positive modulus,
this fixed procedure computes its own power-of-two capacity, builds two padded
histograms, multiplies them with Karatsuba, folds the product into a correlation,
and looks up the residues of the A array. The result is exactly the modular
triple count used by the prime-score construction, including all multiplicities.
-/

namespace ThreeSum.LightModuloCounts

open Light ThreeSum.LightResidues ThreeSum.LightResidueHistogram
open ThreeSum.KaratsubaInterface ThreeSum.CyclicFold

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Arguments: A, B, C, their three lengths, modulus, maximum length, scratch.
Local 9 holds the computed capacity; 10--14 are scratch-region pointers. -/
def body (pCapacity pHist pCyclic pResidues pLookup : ℕ) : Stmt :=
  .call pCapacity [v 6] 9 ;;
  .set 10 (v 8 +' v 9) ;;
  .set 11 (v 8 +' k 2 *' v 9) ;;
  .set 12 (v 8 +' k 3 *' v 9) ;;
  .set 13 (v 8 +' k 5 *' v 9) ;;
  .set 14 (v 13 +' v 7) ;;
  .call pHist [v 1, v 11, v 4, v 6, v 9, v 13, v 14, k 0 -' k 1] 15 ;;
  .call pHist [v 2, v 10, v 5, v 6, v 9, v 13, v 14, k 1] 15 ;;
  .call pCyclic [v 9, v 10, v 11, v 12, v 8, v 14, v 6] 15 ;;
  .call pResidues [v 0, v 13, v 3, v 6, v 14, k 1] 15 ;;
  .call pLookup [v 13, v 8, v 3, v 6] 0

def time (p nA nB nC U : ℕ) : ℕ :=
  LightCapacity.time p + LightResidueHistogram.time nB (capacity p) U +
    LightResidueHistogram.time nC (capacity p) U +
    LightCyclic.combinedTime (Nat.clog 2 p) p +
    residuesTime nA U + LightLookupSum.time nA + 400

def space (free p N U : ℕ) : ℕ :=
  free + 13 * capacity p + N + Nat.log 2 (U+1) + 2

def word (p N U : ℕ) : ℕ :=
  LightKaratsuba.wordBound (capacity p) N + 4*U + 4*p + 16 + N^3

theorem meets {pMain pCapacity pHist pCyclic pResidues pEmod
    pHistogram pMultiply pHalf pLinear pFill pLookup : ℕ}
    (hmain : P[pMain]? = some (body pCapacity pHist pCyclic pResidues pLookup))
    (hcap : P[pCapacity]? = some LightCapacity.body)
    (hhist : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram))
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    (hcount : P[pHistogram]? = some (LightHistogram.histogramBody pFill))
    (hcyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear))
    (K : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    (hlookup : P[pLookup]? = some LightLookupSum.body)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space)
    (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (time p nA nB nC U)
      fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free := by
  haveI : NeZero p := ⟨hp.ne'⟩
  let q := capacity p
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hpq : p ≤ q := le_capacity p
  have hspace' : free+13*q+N+Nat.log 2 (U+1)+2 ≤ lim.space := hspace
  have hkw : (LightKaratsuba.wordBound q N : ℤ) ≤ lim.word := by
    have hh : LightKaratsuba.wordBound q N ≤ word p N U := by
      dsimp [word, q]
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hew : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    have hh : 4*U+4*p+16 ≤ word p N U := by unfold word; omega
    have hhZ := (Int.ofNat_le.mpr hh).trans hword
    exact_mod_cast hhZ
  have hcw : ((2*p+1 : ℕ) : ℤ) ≤ lim.word := by
    push_cast
    omega
  have hsumword : ((nA*(nB*nC) : ℕ) : ℤ) ≤ lim.word := by
    have hprod : nA*(nB*nC) ≤ N^3 := by
      calc
        _ ≤ N*(N*N) := Nat.mul_le_mul hnA (Nat.mul_le_mul hnB hnC)
        _ = _ := by ring
    have hh : N^3 ≤ word p N U := by unfold word; omega
    exact (Int.ofNat_le.mpr (hprod.trans hh)).trans hword
  let F := signedHistogram p 1 (fun i => μ (c+i)) nC
  let H := signedHistogram p 1 (fun i => μ (b+i)) nB
  have hHneg : signedHistogram p (-1) (fun i => μ (b+i)) nB = (fun z => H (-z)) := by
    funext z
    exact signedHistogram_neg p _ _ z
  have hFbound : Karatsuba.CoeffBound (vector p F) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) 1 (fun i => μ (c+i)) nC 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    intro i
    exact (hh i).trans (by exact_mod_cast hnC)
  have hHbound : Karatsuba.CoeffBound (vector p (fun z => H (-z))) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) (-1) (fun i => μ (b+i)) nB 0
    simp only [padTo, Nat.zero_sub, List.replicate_zero, List.append_nil] at hh
    rw [hHneg] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnB)
  apply Meets.of_body hmain
  unfold body time
  light_call (LightCapacity.meets hcap μ hp hcw) using q, capacity with capVal μ₀ ⟨hcapacity, hmem⟩
  subst μ₀
  subst capVal
  light_set (free+q)
  light_set (free+2*q)
  light_set (free+3*q)
  light_set (free+5*q)
  light_set (free+5*q+N)
  light_call (LightResidueHistogram.meets (d := d+1) (src := b) (dst := free+2*q)
    (codes := free+5*q) (work := free+5*q+N) (cap := q) (c := -1)
    hhist hres hem hcount K.fill hw (by omega) hp hpq (by omega) (by omega)
    (by omega) (by omega) (by norm_num) hew hB)
    using q, capacity with _ μ₁ ⟨hBseg, hkeep₁⟩
  rw [hHneg] at hBseg
  have hCread (i : ℕ) (hi : i < nC) : μ₁ (c+i) = μ (c+i) :=
    hkeep₁ _ ⟨by omega, by left; omega⟩
  have hC₁ : ∀ i < nC, |μ₁ (c+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hCread i hi]
    exact hC i hi
  light_call (LightResidueHistogram.meets (d := d+1) (src := c) (dst := free+q)
    (codes := free+5*q) (work := free+5*q+N) (cap := q) (c := 1)
    hhist hres hem hcount K.fill hw (by omega) hp hpq (by omega) (by omega)
    (by omega) (by omega) (by norm_num) hew hC₁)
    using q, capacity with _ μ₂ ⟨hCseg, hkeep₂⟩
  have hCeq := ModuloCounts.signedHistogram_congr (p := p) (c := 1) hCread
  rw [hCeq] at hCseg
  have hBseg₂ : Seg μ₂ (free+2*q) (padTo q (vector p (fun z => H (-z)))) := by
    intro i hi
    have hlen : (padTo q (vector p (fun z => H (-z)))).length = q :=
      padTo_length _ _ (by rw [vector_length]; exact hpq)
    have hiq : i < q := by omega
    rw [hkeep₂ _ ⟨by omega, by right; omega⟩]
    exact hBseg i hi
  light_call (LightCyclic.correlation_meets (d := d+1) (k := Nat.clog 2 p)
    (a := free+q) (b := free+2*q) (prod := free+3*q) (dst := free)
    (work := free+5*q+N) hcyclic K F H hw hpq hCseg hBseg₂ hFbound hHbound
    (by change free+q+q ≤ free+5*q+N; omega)
    (by change free+2*q+q ≤ free+5*q+N; omega)
    (by change free+3*q+2*q ≤ free+5*q+N; omega)
    (by omega) (by right; change free+p ≤ free+3*q; omega)
    (by change free+5*q+N+8*q ≤ lim.space; omega) hkw (by omega))
    using q, capacity with _ μ₃ ⟨hcorr, hkeep₃⟩
  have hkeepOriginal (i : ℕ) (hi : i < free) : μ₃ i = μ i := by
    rw [hkeep₃ i (by omega) (by left; omega) (by left; omega)]
    exact (hkeep₂ i ⟨by omega, by left; omega⟩).trans
      (hkeep₁ i ⟨by omega, by left; omega⟩)
  have hAread (i : ℕ) (hi : i < nA) : μ₃ (a+i) = μ (a+i) :=
    hkeepOriginal _ (by omega)
  have hA₃ : ∀ i < nA, |μ₃ (a+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hAread i hi]
    exact hA i hi
  light_call (residues_meets (d := d+1) (src := a) (dst := free+5*q)
    (work := free+5*q+N) (c := 1) hres hem hw (by omega) hp
    (by omega) (by omega) (by omega) (by left; omega) (by norm_num) hew hA₃)
    using q, capacity with _ μ₄ ⟨hkeys, hkeep₄⟩
  have hkeys₄ (i : ℕ) (hi : i < nA) :
      μ₄ (free+5*q+i) = (residue p 1 (μ (a+i)) : ℤ) := by
    rw [hkeys i hi, hAread i hi]
  have hcorr₄ (r : ℕ) (hr : r < p) :
      μ₄ (free+r) = (Balancing.correlation F H (r : ZMod p) : ℤ) := by
    rw [hkeep₄ _ ⟨by omega, by left; omega⟩, hcorr r hr]
  light_call (LightLookupSum.meets (d := d+1) (keys := free+5*q) (table := free)
    (n := nA) (p := p) (B := nB*nC) hlookup
    (fun i => residue p 1 (μ (a+i))) (fun r => Balancing.correlation F H (r : ZMod p))
    hw (by omega) (by omega) hkeys₄ (fun i hi => residue_lt hp 1 (μ (a+i)))
    hcorr₄ (fun r hr => ModuloCounts.correlation_le nB nC _ _ _) hsumword)
    using q, capacity with result μ₅ ⟨hresult, hmem₅⟩
  subst μ₅
  refine ⟨?_, ?_⟩
  · change result = _
    rw [hresult, ModuloCounts.count_eq_correlation]
    congr 1
    unfold LightLookupSum.prefixSum
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only
    rw [residue_zmod hp]
    simp only [one_mul]
    rfl
  · intro i hi
    exact (hkeep₄ i ⟨by omega, by left; omega⟩).trans (hkeepOriginal i hi)

/-- Every procedure reference is tied to concrete syntax, including the
recursive multiplication closure. This structure contains no semantic oracle. -/
structure Procs (P : Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pCyclic : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pFill : ℕ
  pLookup : ℕ
  main : P[pMain]? = some (body pCapacity pHist pCyclic pResidues pLookup)
  capacity : P[pCapacity]? = some LightCapacity.body
  hist : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  histogram : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  cyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear)
  multiply : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  lookup : P[pLookup]? = some LightLookupSum.body

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space)
    (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,p,N,free] μ (time p nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free) :=
  LightModuloCounts.meets C.main C.capacity C.hist C.residues C.emod C.histogram
    C.cyclic C.multiply C.lookup hw hp ha hb hc hnA hnB hnC hspace hword hd hA hB hC

def program : Program :=
  [body 1 2 6 3 11, LightCapacity.body, LightResidueHistogram.body 3 5,
    residuesBody 4, emodBody, LightHistogram.histogramBody 10, LightCyclic.body 7 9,
    LightKaratsuba.body 7 8 9 10, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]

def program_procs : Procs program 0 where
  pCapacity := 1
  pHist := 2
  pCyclic := 6
  pResidues := 3
  pEmod := 4
  pHistogram := 5
  pMultiply := 7
  pHalf := 8
  pLinear := 9
  pFill := 10
  pLookup := 11
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl, rfl, rfl, rfl⟩
  lookup := rfl

theorem program_meets
    {μ : ℕ → ℤ} {a b c nA nB nC p N free U : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 0 < p)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free p N U ≤ lim.space)
    (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d + Nat.clog 2 p + 3 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [a,b,c,nA,nB,nC,p,N,free] μ (time p nA nB nC U)
      (fun r μ' =>
        r = (ModuloCounts.count p nA nB nC
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) : ℤ) ∧
          Kept μ μ' free) :=
  program_procs.meets hw hp ha hb hc hnA hnB hnC hspace hword hd hA hB hC

end ThreeSum.LightModuloCounts
