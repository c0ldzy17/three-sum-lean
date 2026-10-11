import Submission.ThreeSum.EncodedColorLayout
import Submission.ThreeSum.EncodedColorParameterData
import Submission.ThreeSum.EncodedColorPrimeCosts

/-! # Retained normalized pointers and the actual incidence-count cell -/

namespace ThreeSum.EncodedColorNormalizedData

open Light Scales BandScales ColorClassLists BandRawA EncodedColorLayout

def incidences (n : ℕ) (A B C : List ℤ) (hsA : A.Pairwise (· < ·))
    (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List ℤ :=
  values (fun j => A.getD j 0)
    (items A.length (bandSize n) (sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC))

def Output (μ : ℕ → ℤ) (free n : ℕ) (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ) : Prop :=
  Seg μ free (normalizedHeads free n (bandSize n)) ∧
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·)) (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    μ (normalizedEnd free n (bandSize n))=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    SourceFiniteData.Normalized μ (av free n) (ae free n) (bv free n) (be free n) (cv free n) (ce free n)
      (tables free n) (rec free n (bandSize n)) (vals free n (bandSize n)) (bandSize n) (bandSize_pos n)
      (classList color x 0 1) (classList color x 1 1) (classList color x 2 (-1))
      A B C hsA hsB hsC ((incidences n A B C hsA hsB hsC).length : ℤ)

theorem records_length_le {A B C : List ℤ} {g n : ℕ} {hg : 0 < g}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (sortedRecords A B C g hg hsA hsB hsC).length ≤ ColorBandBounds.count n g := by
  have h := EncodedColorPrimeCosts.count_mono (g := g) ha hb hc
  have hright : LightEncodedColorPrime.count n n n g=ColorBandBounds.count n g := by
    unfold LightEncodedColorPrime.count ColorBandBounds.count
    ring
  rw [hright] at h
  simp only [sortedRecords, BandCandidateRows.records_length]
  exact h

theorem incidences_length_le {A B C : List ℤ} {n : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (ha : A.length ≤ n) (hb : B.length ≤ n) (hc : C.length ≤ n) :
    (incidences n A B C hsA hsB hsC).length ≤ bandSize n*ColorBandBounds.count n (bandSize n) := by
  unfold incidences
  rw [values_length]
  exact (items_length_le ..).trans (Nat.mul_le_mul_left _ (records_length_le ha hb hc))

theorem incidences_bounded {A B C : List ℤ} {n U : ℕ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hA : ∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) :
    ∀ z ∈ incidences n A B C hsA hsB hsC, |z| ≤ (U : ℤ) := values_bounded hA

theorem heads_read {μ : ℕ → ℤ} {free n g : ℕ} (H : Seg μ free (normalizedHeads free n g)) :
    μ free=(av free n : ℤ) ∧ μ (free+1)=(ae free n : ℤ) ∧
    μ (free+2)=(bv free n : ℤ) ∧ μ (free+3)=(be free n : ℤ) ∧
    μ (free+4)=(cv free n : ℤ) ∧ μ (free+5)=(ce free n : ℤ) ∧
    μ (free+6)=(rec free n g : ℤ) ∧ μ (free+7)=(vals free n g : ℤ) := by
  have h (i : ℕ) (hi : i < 8) := H.getD (i := i) (by simpa [normalizedHeads] using hi) 0
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [normalizedHeads] using h 0 (by omega)
  · simpa [normalizedHeads] using h 1 (by omega)
  · simpa [normalizedHeads] using h 2 (by omega)
  · simpa [normalizedHeads] using h 3 (by omega)
  · simpa [normalizedHeads] using h 4 (by omega)
  · simpa [normalizedHeads] using h 5 (by omega)
  · simpa [normalizedHeads] using h 6 (by omega)
  · simpa [normalizedHeads] using h 7 (by omega)

end ThreeSum.EncodedColorNormalizedData
