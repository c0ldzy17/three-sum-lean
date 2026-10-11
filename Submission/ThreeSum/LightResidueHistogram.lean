import Submission.ThreeSum.LightResidues
import Submission.ThreeSum.LightHistogram
import Submission.ThreeSum.CyclicFold

/-!
# Original integers to a padded signed histogram

The executable procedure first computes canonical residues of the signed
original integers and then fills the entire requested histogram capacity.
Its postcondition is the precise padded polynomial vector consumed by the
verified cyclic-convolution routine. Repeated input values remain distinct
incidences and contribute their full multiplicity.
-/

namespace ThreeSum.LightResidueHistogram

open Light Finset ThreeSum.LightResidues ThreeSum.LightHistogram
open ThreeSum.CyclicFold ThreeSum.Karatsuba

variable {lim : Limits} {P : Program} {d : ℕ}

def signedHistogram (p : ℕ) (c : ℤ) (values : ℕ → ℤ) (n : ℕ) (z : ZMod p) : ℕ :=
  Histograms.histogram (Finset.range n) (fun i => ((c * values i : ℤ) : ZMod p))
    (fun _ => 1) z

/-- Negating the original integers supplies the reversal needed by a
correlation, without a separate reverse-array operation. -/
theorem signedHistogram_neg (p : ℕ) (values : ℕ → ℤ) (n : ℕ) (z : ZMod p) :
    signedHistogram p (-1) values n z = signedHistogram p 1 values n (-z) := by
  simp only [signedHistogram, Histograms.histogram, neg_mul, one_mul, Int.cast_neg,
    neg_eq_iff_eq_neg]

theorem sum_signedHistogram {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n : ℕ) :
    (∑ z : ZMod p, signedHistogram p c values n z) = n := by
  unfold signedHistogram
  rw [Histograms.sum_histogram]
  simp

theorem residue_zmod {p : ℕ} (hp : 0 < p) (c x : ℤ) :
    (residue p c x : ZMod p) = ((c * x : ℤ) : ZMod p) := by
  unfold residue
  rw [ZMod.natCast_toNat p (Int.emod_nonneg _ (by exact_mod_cast hp.ne')),
    ZMod.intCast_mod]

theorem residue_eq_iff {p : ℕ} [NeZero p] (c x : ℤ) {r : ℕ} (hr : r < p) :
    residue p c x = r ↔ ((c * x : ℤ) : ZMod p) = (r : ZMod p) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  constructor
  · intro h
    rw [← residue_zmod hp, h]
  · intro h
    rw [← residue_zmod hp] at h
    have hv := congrArg ZMod.val h
    simpa only [ZMod.val_natCast_of_lt (residue_lt hp c x),
      ZMod.val_natCast_of_lt hr] using hv

theorem signedHistogram_eq_count {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : r < p) :
    signedHistogram p c values n (r : ZMod p) =
      count (fun i => residue p c (values i)) r n := by
  unfold signedHistogram Histograms.histogram count
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [residue_eq_iff c (values i) hr]

theorem signed_count_zero {p : ℕ} (hp : 0 < p)
    (c : ℤ) (values : ℕ → ℤ) (n r : ℕ) (hr : p ≤ r) :
    count (fun i => residue p c (values i)) r n = 0 := by
  unfold count
  apply Finset.card_eq_zero.mpr
  apply Finset.filter_eq_empty_iff.mpr
  intro i hi heq
  change residue p c (values i) = r at heq
  have h := residue_lt hp c (values i)
  omega

/-- This equality holds at every index, including the zero padding. -/
theorem padded_histogram_getD {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap r : ℕ) :
    (padTo cap (vector p (signedHistogram p c values n))).getD r 0 =
      (count (fun i => residue p c (values i)) r n : ℤ) := by
  rw [← asPolynomial_coeff, asPolynomial_padTo, asPolynomial_coeff]
  by_cases hr : r < p
  · rw [vector_getD _ _ _ hr, signedHistogram_eq_count c values n r hr]
  · rw [List.getD_eq_default _ _ (by rw [vector_length]; omega)]
    rw [signed_count_zero (Nat.pos_of_ne_zero (NeZero.ne p)) c values n r (by omega)]
    rfl

theorem padded_histogram_bound {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) (n cap : ℕ) :
    CoeffBound (padTo cap (vector p (signedHistogram p c values n))) (n : ℤ) := by
  intro r
  rw [padded_histogram_getD, abs_of_nonneg (Int.natCast_nonneg _)]
  exact_mod_cast count_le (fun i => residue p c (values i)) r n

theorem padded_histogram_segment {p : ℕ} [NeZero p]
    (c : ℤ) (values : ℕ → ℤ) {n cap dst : ℕ} {μ : ℕ → ℤ}
    (hcap : p ≤ cap)
    (hout : ∀ r < cap, μ (dst + r) =
      (count (fun i => residue p c (values i)) r n : ℤ)) :
    Seg μ dst (padTo cap (vector p (signedHistogram p c values n))) := by
  intro r hr
  have hlen : (padTo cap (vector p (signedHistogram p c values n))).length = cap := by
    apply padTo_length
    rw [vector_length]
    exact hcap
  have hrcap : r < cap := by omega
  rw [← List.getD_eq_getElem _ 0 hr, padded_histogram_getD]
  exact hout r hrcap

/-- Arguments: source, histogram, item count, modulus, histogram capacity,
first scratch cell, remainder scratch cell, sign. -/
def body (pResidues pHistogram : ℕ) : Stmt :=
  .call pResidues [v 0, v 5, v 2, v 3, v 6, v 7] 8 ;;
  .call pHistogram [v 5, v 1, v 2, v 4] 8

def time (n cap U : ℕ) : ℕ := residuesTime n U + histogramTime n cap + 30

theorem meets {pMain pResidues pEmod pHistogram pFill : ℕ}
    (hmain : P[pMain]? = some (body pResidues pHistogram))
    (hres : P[pResidues]? = some (residuesBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    (hhist : P[pHistogram]? = some (histogramBody pFill))
    (hfill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {src dst n p cap codes work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hp : 0 < p) (hcap : p ≤ cap)
    (hsrc : src + n ≤ codes) (hdst : dst + cap ≤ codes)
    (hcodes : codes + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hc : |c| ≤ 1) (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim P pMain d [src, dst, n, p, cap, codes, work, c] μ (time n cap U)
      fun _ μ' =>
        Seg μ' dst (padTo cap (vector p (signedHistogram p c (fun i => μ (src+i)) n))) ∧
          KeptBut μ μ' codes dst cap := by
  haveI : NeZero p := ⟨hp.ne'⟩
  apply Meets.of_body hmain
  unfold body time
  have hcall := residues_meets (d := d + 1) (src := src) (dst := codes)
    (n := n) (p := p) (work := work) (c := c) hres hem hw hd hp
    (by omega) hcodes hspace (by left; omega) hc hword hvalues
  light_call hcall using residuesTime, histogramTime, countTime, residueBudget
    with _ μ₁ ⟨hkeys, hkept₁⟩
  have hcall₂ := histogram_meets (d := d + 1) (src := codes) (dst := dst)
    (n := n) (p := cap) (μ := μ₁) hhist hfill
    (fun i => residue p c (μ (src + i))) hw hd
    (by omega) (by omega) (by right; omega) hkeys
    (fun i hi => (residue_lt hp c (μ (src + i))).trans_le hcap)
  light_call hcall₂ using residuesTime, histogramTime, countTime, residueBudget
    with _ μ₂ ⟨hcounts, hkept₂⟩
  refine ⟨padded_histogram_segment c (fun i => μ (src + i)) hcap hcounts, ?_⟩
  intro a ⟨ha, hout⟩
  exact (hkept₂ a hout).trans (hkept₁ a ⟨by omega, by omega⟩)

def program : Program :=
  [body 1 3, residuesBody 2, emodBody, histogramBody 4, fillBody]

theorem program_meets
    {μ : ℕ → ℤ} {src dst n p cap codes work U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d + 1 < lim.depth)
    (hp : 0 < p) (hcap : p ≤ cap)
    (hsrc : src + n ≤ codes) (hdst : dst + cap ≤ codes)
    (hcodes : codes + n ≤ work)
    (hspace : work + (Nat.log 2 (U + 1) + 2) ≤ lim.space)
    (hc : |c| ≤ 1) (hword : (4 * U + 4 * p + 16 : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (src + i)| ≤ (U : ℤ)) :
    Meets lim program 0 d [src, dst, n, p, cap, codes, work, c] μ (time n cap U)
      (fun _ μ' =>
        Seg μ' dst (padTo cap (vector p (signedHistogram p c (fun i => μ (src+i)) n))) ∧
          KeptBut μ μ' codes dst cap) := by
  exact meets rfl rfl rfl rfl rfl hw hd hp hcap hsrc hdst hcodes hspace hc hword hvalues

theorem time_bound (n cap U : ℕ) :
    time n cap U ≤ 13 * cap + 131 * n * (Nat.log 2 (U + 1) + 1) + 53 := by
  unfold time residuesTime residueBudget histogramTime countTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightResidueHistogram
