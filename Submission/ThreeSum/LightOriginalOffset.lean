import Submission.ThreeSum.LightBalancedOffset
import Submission.ThreeSum.LightModuloCounts

/-!
# An actual common offset from two original signed key arrays

The fixed program builds both padded histograms, including reversal, from
the supplied integer keys. It computes its own power-of-two capacity and
chooses the least correlation minimum with the checked fast multiplication.
Repeated keys count separately. No histogram or capacity table is supplied.
-/

namespace ThreeSum.LightOriginalOffset

open Light LightResidues LightResidueHistogram
open KaratsubaInterface CyclicFold
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def selected (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) : ℕ :=
  LightBalancedOffset.offset (signedHistogram p 1 right nRight)
    (signedHistogram p 1 left nLeft)

theorem selected_lt (p : ℕ) [NeZero p] (left right : ℕ → ℤ) (nLeft nRight : ℕ) :
    selected p left right nLeft nRight < p := LightBalancedOffset.offset_lt ..

/-- The actual selected offset satisfies the exact raw-incidence mean bound,
including duplicate keys in either original array. -/
theorem selected_pairMass_bound (p : ℕ) [NeZero p] (left right : ℕ → ℤ)
    (nLeft nRight : ℕ) :
    p * Histograms.pairMass (Finset.range nLeft) (Finset.range nRight)
      (fun i => (left i : ZMod p)) (fun i => (right i : ZMod p))
      (fun _ => 1) (fun _ => 1) (selected p left right nLeft nRight : ZMod p) ≤
        nLeft*nRight := by
  have h := LightBalancedOffset.offset_balanced (signedHistogram p 1 right nRight)
    (signedHistogram p 1 left nLeft)
  rw [sum_signedHistogram,sum_signedHistogram] at h
  change p * Balancing.correlation _ _ (selected p left right nLeft nRight : ZMod p) ≤ _ at h
  unfold signedHistogram at h
  rw [Histograms.correlation_histograms] at h
  simpa only [one_mul,Nat.mul_comm] using h

/-- Left and right signed key arrays, their lengths, modulus, maximum
length, and first free address. -/
def body (pCapacity pHist pOffset : ℕ) : Stmt :=
  .call pCapacity [v 4] 7 ;;
  .set 8 (v 6 +' v 7) ;;
  .set 9 (v 6 +' k 2 *' v 7) ;;
  .set 10 (v 6 +' k 3 *' v 7) ;;
  .set 11 (v 6 +' k 5 *' v 7) ;;
  .set 12 (v 11 +' v 5) ;;
  .call pHist [v 0,v 9,v 2,v 4,v 7,v 11,v 12,k 0 -' k 1] 13 ;;
  .call pHist [v 1,v 8,v 3,v 4,v 7,v 11,v 12,k 1] 13 ;;
  .call pOffset [v 7,v 8,v 9,v 10,v 6,v 12,v 4] 0

def time (p nLeft nRight U : ℕ) : ℕ := LightCapacity.time p+
  LightResidueHistogram.time nLeft (capacity p) U+
  LightResidueHistogram.time nRight (capacity p) U+
  LightBalancedOffset.time (Nat.clog 2 p) p+300
def space (free p N U : ℕ) : ℕ := free+13*capacity p+N+Nat.log 2 (U+1)+2
def word (p N U : ℕ) : ℕ := LightKaratsuba.wordBound (capacity p) N+4*U+4*p+16

structure Procs (P : Program) (pMain : ℕ) where
  pCapacity : ℕ
  pHist : ℕ
  pResidues : ℕ
  pEmod : ℕ
  pHistogram : ℕ
  pFill : ℕ
  pOffset : ℕ
  pCyclic : ℕ
  pMultiply : ℕ
  pHalf : ℕ
  pLinear : ℕ
  pMinimum : ℕ
  capacityProc : P[pCapacity]? = some LightCapacity.body
  histogram : P[pHist]? = some (LightResidueHistogram.body pResidues pHistogram)
  residues : P[pResidues]? = some (residuesBody pEmod)
  emod : P[pEmod]? = some emodBody
  count : P[pHistogram]? = some (LightHistogram.histogramBody pFill)
  offset : P[pOffset]? = some (LightBalancedOffset.body pCyclic pMinimum)
  cyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear)
  karatsuba : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill
  minimum : P[pMinimum]? = some LightMinimum.body
  main : P[pMain]? = some (body pCapacity pHist pOffset)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain a b nLeft nRight p N free U : ℕ} [NeZero p]
    {μ : ℕ → ℤ} (C : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : space free p N U ≤ lim.space) (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [a,b,nLeft,nRight,p,N,free] μ (time p nLeft nRight U)
      (fun r ν => r = (selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        Kept μ ν free) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  let q := capacity p
  have hq : 0 < q := Nat.pow_pos (by decide)
  have hpq : p ≤ q := le_capacity p
  have hspace' : free+13*q+N+Nat.log 2 (U+1)+2 ≤ lim.space := hspace
  have hkw : (LightKaratsuba.wordBound q N : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show LightKaratsuba.wordBound q N ≤ word p N U by
      unfold word; change LightKaratsuba.wordBound (capacity p) N ≤ _; omega)).trans hword
  have hew : (4*U+4*p+16 : ℤ) ≤ lim.word := by
    have hh : 4*U+4*p+16 ≤ word p N U := by unfold word; omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  have hcw : ((2*p+1 : ℕ) : ℤ) ≤ lim.word := by push_cast; omega
  let F := signedHistogram p 1 (fun i => μ (b+i)) nRight
  let H := signedHistogram p 1 (fun i => μ (a+i)) nLeft
  have hHneg : signedHistogram p (-1) (fun i => μ (a+i)) nLeft = (fun z => H (-z)) := by
    funext z
    exact signedHistogram_neg p _ _ z
  have hFbound : Karatsuba.CoeffBound (vector p F) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) 1 (fun i => μ (b+i)) nRight 0
    simp only [padTo,Nat.zero_sub,List.replicate_zero,List.append_nil] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnRight)
  have hHbound : Karatsuba.CoeffBound (vector p (fun z => H (-z))) (N : ℤ) := by
    have hh := padded_histogram_bound (p := p) (-1) (fun i => μ (a+i)) nLeft 0
    simp only [padTo,Nat.zero_sub,List.replicate_zero,List.append_nil] at hh
    rw [hHneg] at hh
    intro i
    exact (hh i).trans (Int.ofNat_le.mpr hnLeft)
  apply Meets.of_body C.main
  unfold body time
  light_call (LightCapacity.meets C.capacityProc μ hp hcw) using q,capacity
    with capVal μ₀ ⟨hcapacity,hmem⟩
  subst μ₀
  subst capVal
  light_set (free+q)
  light_set (free+2*q)
  light_set (free+3*q)
  light_set (free+5*q)
  light_set (free+5*q+N)
  light_call (LightResidueHistogram.meets (d := d+1) (src := a) (dst := free+2*q)
    (codes := free+5*q) (work := free+5*q+N) (cap := q) (c := -1)
    C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega) hp hpq
    (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hLeft)
    using q,capacity with _ μ₁ ⟨hLeftSeg,hkeep₁⟩
  rw [hHneg] at hLeftSeg
  have hRightRead (i : ℕ) (hi : i < nRight) : μ₁ (b+i) = μ (b+i) :=
    hkeep₁ _ ⟨by omega,Or.inl (by omega)⟩
  have hRight₁ : ∀ i < nRight, |μ₁ (b+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hRightRead i hi]
    exact hRight i hi
  light_call (LightResidueHistogram.meets (d := d+1) (src := b) (dst := free+q)
    (codes := free+5*q) (work := free+5*q+N) (cap := q) (c := 1)
    C.histogram C.residues C.emod C.count C.karatsuba.fill hw (by omega) hp hpq
    (by omega) (by omega) (by omega) (by omega) (by norm_num) hew hRight₁)
    using q,capacity with _ μ₂ ⟨hRightSeg,hkeep₂⟩
  rw [ModuloCounts.signedHistogram_congr (p := p) (c := 1) hRightRead] at hRightSeg
  have hLeftSeg₂ : Seg μ₂ (free+2*q) (padTo q (vector p (fun z => H (-z)))) := by
    intro i hi
    have hlen : (padTo q (vector p (fun z => H (-z)))).length = q :=
      padTo_length _ _ (by rw [vector_length]; exact hpq)
    have hiq : i < q := by omega
    rw [hkeep₂ _ ⟨by omega,Or.inr (by omega)⟩]
    exact hLeftSeg i hi
  light_call (LightBalancedOffset.meets (d := d+1) (k := Nat.clog 2 p)
    (a := free+q) (b := free+2*q) (prod := free+3*q) (dst := free)
    (work := free+5*q+N) C.offset C.cyclic C.minimum C.karatsuba F H hw hpq
    hRightSeg hLeftSeg₂ hFbound hHbound
    (by change free+q+q ≤ free+5*q+N; omega)
    (by change free+2*q+q ≤ free+5*q+N; omega)
    (by change free+3*q+2*q ≤ free+5*q+N; omega)
    (by omega) (by right; change free+p ≤ free+3*q; omega)
    (by change free+5*q+N+8*q ≤ lim.space; omega) hkw (by omega))
    using q,capacity with result μ₃ ⟨hresult,hkeep₃⟩
  refine ⟨hresult,?_⟩
  intro i hi
  change μ₃ i = μ i
  rw [hkeep₃ i (by omega) (Or.inl (by omega)) (Or.inl (by omega))]
  exact (hkeep₂ i ⟨by omega,Or.inl (by omega)⟩).trans
    (hkeep₁ i ⟨by omega,Or.inl (by omega)⟩)

def program : Program :=
  [body 1 2 7,LightCapacity.body,LightResidueHistogram.body 3 5,residuesBody 4,
    emodBody,LightHistogram.histogramBody 6,fillBody,LightBalancedOffset.body 8 12,
    LightCyclic.body 9 11,LightKaratsuba.body 9 10 11 6,halfBody,
    LightArray.linearBody,LightMinimum.body]

def programProcs : Procs program 0 :=
  ⟨1,2,3,4,5,6,7,8,9,10,11,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩

theorem program_length : program.length = 13 := rfl

theorem program_meets {a b nLeft nRight p N free U : ℕ} [NeZero p] {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+nLeft ≤ free) (hb : b+nRight ≤ free)
    (hnLeft : nLeft ≤ N) (hnRight : nRight ≤ N)
    (hspace : space free p N U ≤ lim.space) (hword : (word p N U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 p+4 ≤ lim.depth)
    (hLeft : ∀ i < nLeft, |μ (a+i)| ≤ (U : ℤ))
    (hRight : ∀ i < nRight, |μ (b+i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [a,b,nLeft,nRight,p,N,free] μ (time p nLeft nRight U)
      (fun r ν => r = (selected p (fun i => μ (a+i)) (fun i => μ (b+i)) nLeft nRight : ℤ) ∧
        Kept μ ν free) :=
  programProcs.meets hw ha hb hnLeft hnRight hspace hword hd hLeft hRight

theorem time_bound (p nLeft nRight U : ℕ) :
    time p nLeft nRight U ≤ LightKaratsuba.time (Nat.clog 2 p)+252*capacity p+
      131*(nLeft+nRight)*(Nat.log 2 (U+1)+1)+12*Nat.clog 2 p+642 := by
  have hL := LightResidueHistogram.time_bound nLeft (capacity p) U
  have hR := LightResidueHistogram.time_bound nRight (capacity p) U
  have hM := LightBalancedOffset.time_bound (Nat.clog 2 p) p (le_capacity p)
  change LightBalancedOffset.time (Nat.clog 2 p) p ≤
    LightKaratsuba.time (Nat.clog 2 p)+226*capacity p+226 at hM
  calc
    time p nLeft nRight U ≤ LightCapacity.time p+
        (13*capacity p+131*nLeft*(Nat.log 2 (U+1)+1)+53)+
        (13*capacity p+131*nRight*(Nat.log 2 (U+1)+1)+53)+
        (LightKaratsuba.time (Nat.clog 2 p)+226*capacity p+226)+300 := by
      unfold time
      omega
    _ = _ := by unfold LightCapacity.time; ring

end ThreeSum.LightOriginalOffset
