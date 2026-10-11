import Submission.ThreeSum.LightArray
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Range

/-!
# A linear-time histogram procedure in the benchmark language

The input is an array of already computed residue indices in `[0,p)`.
The output is cleared and incremented once per input item. Multiplicities
are retained, including repeated equal residues.
-/

namespace ThreeSum.LightHistogram

open Light Finset

variable {lim : Limits} {P : Program} {d : ℕ}

def count (key : ℕ → ℕ) (r i : ℕ) : ℕ :=
  ((Finset.range i).filter fun j => key j = r).card

@[simp] theorem count_zero (key : ℕ → ℕ) (r : ℕ) : count key r 0 = 0 := by
  simp [count]

theorem count_le (key : ℕ → ℕ) (r i : ℕ) : count key r i ≤ i := by
  exact (Finset.card_filter_le _ _).trans (by simp)

theorem count_succ (key : ℕ → ℕ) (r i : ℕ) :
    count key r (i + 1) = count key r i + if key i = r then 1 else 0 := by
  unfold count
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases heq : key i = r
  · rw [if_pos heq, Finset.card_insert_of_notMem (by simp)]
    simp [heq]
  · simp [heq]

/-- The address is deliberately recomputed instead of stored in a temporary:
this makes the loop preserve all locals apart from its counter. -/
def countBody : Stmt :=
  .for 4 (v 2) (.store (v 1 +' M (v 0 +' v 4))
    (M (v 1 +' M (v 0 +' v 4)) +' k 1))

def countTime (n : ℕ) : ℕ := 24 * n + 6

theorem count_ends {μ : ℕ → ℤ} {loc : ℕ → ℤ} {src dst n p : ℕ}
    (key : ℕ → ℕ) (hsrc : loc 0 = src) (hdst : loc 1 = dst) (hlen : loc 2 = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p)
    (hzero : ∀ r < p, μ (dst + r) = 0) :
    Ends lim P d countBody ⟨loc, μ⟩ (countTime n) fun σ' =>
      (∀ r < p, σ'.mem (dst + r) = count key r n) ∧
        SameOutside μ σ'.mem dst p := by
  let Inv := fun i (μ' : ℕ → ℤ) =>
    (∀ r < p, μ' (dst + r) = count key r i) ∧ SameOutside μ μ' dst p
  unfold countBody
  apply Ends.forMem Inv n 16 (hn := by omega)
    (hT := by unfold countTime; light_time)
  · exact ⟨by simpa only [count_zero, Nat.cast_zero] using hzero, fun _ _ => rfl⟩
  · intro i μ' hi hI
    obtain ⟨hcnt, hsame⟩ := hI
    have hki := hkeyLt i hi
    have hread : μ' (src + i) = key i :=
      (hsame _ (by omega)).trans (hkeys i hi)
    have hcell := hcnt (key i) hki
    have hcount := count_le key (key i) i
    have hq0 : (0 : ℤ) ≤ count key (key i) i := Int.natCast_nonneg _
    have hqle : (count key (key i) i : ℤ) < n := by exact_mod_cast hcount.trans_lt hi
    have ha : (v 1 +' M (v 0 +' v 4)).val ⟨Function.update loc 4 (i : ℤ), μ'⟩ =
        ((dst + key i : ℕ) : ℤ) := by light_side [hsrc, hdst, hread]
    have hv : (M (v 1 +' M (v 0 +' v 4)) +' k 1).val
        ⟨Function.update loc 4 (i : ℤ), μ'⟩ = ((count key (key i) i + 1 : ℕ) : ℤ) := by
      light_side [hsrc, hdst, hread, hcell]
    refine Ends.storeLast ?_ (by light_side [hsrc, hdst, hread, hcell]) (by light_time)
    change Function.update loc 4 (i : ℤ) = Function.update loc 4 (i : ℤ) ∧
      Inv (i + 1) (Function.update μ' ((v 1 +' M (v 0 +' v 4)).val
        ⟨Function.update loc 4 (i : ℤ), μ'⟩).toNat
        ((M (v 1 +' M (v 0 +' v 4)) +' k 1).val ⟨Function.update loc 4 (i : ℤ), μ'⟩))
    rw [ha, hv, Int.toNat_natCast]
    refine ⟨rfl, ?_, ?_⟩
    · intro r hr
      rw [count_succ]
      by_cases heq : key i = r
      · subst r
        simp [Function.update_self]
      · rw [Function.update_of_ne (by omega), hcnt r hr]
        simp [heq]
    · intro a ha
      rw [Function.update_of_ne (by omega)]
      exact hsame a ha
  · intro μ' hI
    exact hI
  · intro i μ' hi hI
    simp [hlen]

def histogramBody (pFill : ℕ) : Stmt :=
  .call pFill [v 1, v 3, k 0] 5 ;; countBody

def histogramTime (n p : ℕ) : ℕ := fillTime p + countTime n + 5

/-- Actual clearing, incrementing, and memory-preservation contract. -/
theorem histogram_meets {pHist pFill : ℕ}
    (hp : P[pHist]? = some (histogramBody pFill))
    (hfill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {src dst n p : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hdepth : d < lim.depth)
    (hS : src + n ≤ lim.space) (hD : dst + p ≤ lim.space)
    (hsep : Apart src n dst p)
    (hkeys : ∀ i < n, μ (src + i) = key i)
    (hkeyLt : ∀ i < n, key i < p) :
    Meets lim P pHist d [(src : ℤ), dst, n, p] μ (histogramTime n p) fun _ μ' =>
      (∀ r < p, μ' (dst + r) = count key r n) ∧ SameOutside μ μ' dst p := by
  apply Meets.of_body hp
  unfold histogramBody histogramTime
  light_call (fill_meets hfill (μ := μ) (x := 0) hw hD) with res μ₁ ⟨hfilled, hkept⟩
  have hread : ∀ i < n, μ₁ (src + i) = key i := by
    intro i hi
    exact (hkept _ (by omega)).trans (hkeys i hi)
  have hzero : ∀ r < p, μ₁ (dst + r) = 0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply Ends.pieceLast (count_ends key (by simp) (by simp) (by simp)
    hw hS hD hsep hread hkeyLt hzero)
  · intro σ' hpost
    exact ⟨hpost.1, fun a ha => (hpost.2 a ha).trans (hkept a ha)⟩

end ThreeSum.LightHistogram
