import Submission.ThreeSum.LightResidueHistogram
import Submission.ThreeSum.Arithmetic

/-!
# Modular triple counts from the original integer arrays

This interface identifies the executable histogram/correlation lookup with
the exact `Arithmetic.modCount` used in the weighted false-triple argument.
The three indices retain their multiplicities even when input values repeat.
-/

namespace ThreeSum.ModuloCounts

open Finset LightResidueHistogram
open scoped BigOperators

def triples (nA nB nC : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  range nA ×ˢ (range nB ×ˢ range nC)

def difference (a b c : ℕ → ℤ) (t : ℕ × ℕ × ℕ) : ℤ :=
  c t.2.2 - b t.2.1 - a t.1

def count (p nA nB nC : ℕ) (a b c : ℕ → ℤ) : ℕ :=
  Arithmetic.modCount (triples nA nB nC) (difference a b c) (p : ℤ)

theorem cast_add_eq_iff_dvd (p : ℕ) (a b c : ℤ) :
    (a : ZMod p) + (b : ZMod p) = (c : ZMod p) ↔ (p : ℤ) ∣ c-b-a := by
  have h := ZMod.intCast_eq_intCast_iff_dvd_sub (a+b) c p
  rw [show c-(a+b) = c-b-a by ring] at h
  simpa only [Int.cast_add] using h

theorem count_eq_tripleMass {p : ℕ} [NeZero p]
    (nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c =
      Histograms.tripleMass (range nA) (range nB) (range nC)
        (fun i => (a i : ZMod p)) (fun i => (b i : ZMod p))
        (fun i => (c i : ZMod p)) (fun _ => 1) (fun _ => 1) (fun _ => 1) := by
  unfold count Arithmetic.modCount triples difference Histograms.tripleMass
  simp only [sum_product, Arithmetic.dividesIndicator, one_mul]
  simp_rw [cast_add_eq_iff_dvd]

theorem count_eq_correlation {p : ℕ} [NeZero p]
    (nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c =
      ∑ i ∈ range nA, Balancing.correlation
        (signedHistogram p 1 c nC) (signedHistogram p 1 b nB) (a i : ZMod p) := by
  rw [count_eq_tripleMass, Histograms.tripleMass_eq_histogram]
  unfold LightResidueHistogram.signedHistogram
  simp only [one_mul]

theorem count_le (p nA nB nC : ℕ) (a b c : ℕ → ℤ) :
    count p nA nB nC a b c ≤ nA*nB*nC := by
  have h : count p nA nB nC a b c ≤ (triples nA nB nC).card := by
    unfold count Arithmetic.modCount
    calc
      _ ≤ ∑ _t ∈ triples nA nB nC, (1 : ℕ) := by
        apply sum_le_sum
        intro t ht
        unfold Arithmetic.dividesIndicator
        split <;> omega
      _ = _ := by simp
  simpa only [triples, card_product, card_range, Nat.mul_assoc] using h

theorem signedHistogram_congr {p c n} {a b : ℕ → ℤ}
    (hab : ∀ i < n, a i = b i) :
    signedHistogram p c a n = signedHistogram p c b n := by
  funext z
  unfold signedHistogram Histograms.histogram
  apply sum_congr rfl
  intro i hi
  simp only [hab i (mem_range.mp hi)]

theorem correlation_le {p : ℕ} [NeZero p]
    (nB nC : ℕ) (b c : ℕ → ℤ) (z : ZMod p) :
    Balancing.correlation (signedHistogram p 1 c nC) (signedHistogram p 1 b nB) z
      ≤ nB*nC := by
  have h := single_le_sum (f := Balancing.correlation
    (signedHistogram p 1 c nC) (signedHistogram p 1 b nB))
    (fun _ _ => Nat.zero_le _) (mem_univ z)
  rw [Balancing.sum_correlation, sum_signedHistogram, sum_signedHistogram] at h
  simpa only [Nat.mul_comm nC nB] using h

end ThreeSum.ModuloCounts
