import Submission.ThreeSum.EncodedColorNormalizedData

/-! # The same normalized finite witnesses and their actually selected prime -/

namespace ThreeSum.EncodedColorPrimeReadyData

open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData

def moduli (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ → ℕ :=
  LightEncodedColorPrime.moduli A B C (bandSize n) (bandSize_pos n) hsA hsB hsC (primeWindow n)

def selected (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  moduli n A B C hsA hsB hsC (LightBandPrimeDepth.depth (radix n) (primeWindow n))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) : Prop :=
  Seg μ free (normalizedHeads free n (bandSize n)) ∧
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    μ (normalizedEnd free n (bandSize n))=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    SourceFiniteData.Normalized μ (av free n) (ae free n) (bv free n) (be free n) (cv free n) (ce free n)
      (tables free n) (rec free n (bandSize n)) (vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
      (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
      A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    EncodedColorPrimeData.Stored μ (prime free n (bandSize n)) (radix n) (primeWindow n)
      (moduli n A B C hsA hsB hsC)

theorem selected_pos {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} :
    0 < selected n A B C hsA hsB hsC :=
  EncodedColorPrimeCosts.moduli_pos (lt_of_lt_of_le (by decide : 0 < 2) (primeWindow_ge_two n)) _

theorem selected_guard {n : ℕ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hR : 4 ≤ radix n) : 4*selected n A B C hsA hsB hsC ≤ radix n :=
  EncodedColorPrimeCosts.scheduled_modulus_guard hR

end ThreeSum.EncodedColorPrimeReadyData
