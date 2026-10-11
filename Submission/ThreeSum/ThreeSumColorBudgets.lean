import Submission.ThreeSum.EncodedColorPipelineData
import Submission.ThreeSum.LightDenseSetup
import Submission.ThreeSum.UniformStageBounds

/-!
# Actual encoding-output masses fit the uniform reporting budgets

Both inequalities come from the retained pipeline payload. The wanted
count includes all physical A occurrences and all three lifts; the false
score uses the very common modulus selected from the original normalized
arrays. No input-dependent counting or prime-quality premise is assumed.
The explicit numerical divisor premise is discharged eventually, uniformly
before the input arrays are quantified.
-/

namespace ThreeSum.ThreeSumColorBudgets

open Light Scales BandScales CostLedger GlobalEncoding LocalCoverBounds
open ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 2200000
set_option maxRecDepth 12000

theorem total_keys_eq (n : ℕ) :
    LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n))=
      TrimScales.scheduleCount n*typedOutputs n := by
  have hh : 2*microHalf (inputBits n)=muZero n := rfl
  have hw : 512*microHalf (inputBits n)=256*muZero n := by rw [← hh]; ring
  unfold LightGuardedWanted.totalKeys LightGlobalKeys.localCount outputCount
    TrimScales.scheduleCount TrimScales.replicatedHalf TrimScales.localLength typedOutputs
  rw [mul_pow,scheduleSize_eq_length]
  congr 1
  rw [hh,hw]

theorem representation_cap_eq (n : ℕ) :
    representationCap (microHalf (inputBits n)) (blockCount (inputBits n))=
      TrimScales.representationBound n := by
  unfold representationCap TrimScales.representationBound TrimScales.localLength
  rw [scheduleSize_eq_length]

variable {μ : ℕ → ℤ} {free n : ℕ}
    {color : Coloring.Parameter (inputBits n+1)} {x : Fin n → ℤ}
    {A B C : List ℤ} {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_lengths (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    A.length ≤ n ∧ B.length ≤ n ∧ C.length ≤ n :=
  ⟨H.normalized.2.1.2.1.trans (length_classList_le color x 0 1),
    H.normalized.2.2.1.2.1.trans (length_classList_le color x 1 1),
    H.normalized.2.2.2.1.2.1.trans (length_classList_le color x 2 (-1))⟩

theorem normalized_values {U : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    (∀ j < A.length, |A.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < B.length, |B.getD j 0| ≤ (U : ℤ)) ∧
      (∀ j < C.length, |C.getD j 0| ≤ (U : ℤ)) :=
  ⟨SourceFiniteInputs.prepared_bound H.normalized.2.1
      (LightColorBands.class_bounded color x 0 1 (by norm_num) hx),
    SourceFiniteInputs.prepared_bound H.normalized.2.2.1
      (LightColorBands.class_bounded color x 1 1 (by norm_num) hx),
    SourceFiniteInputs.prepared_bound H.normalized.2.2.2.1
      (LightColorBands.class_bounded color x 2 (-1) (by norm_num) hx)⟩

theorem records_length_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC).length ≤ 3*bandCount n^2 := by
  obtain ⟨ha,hb,hc⟩ := normalized_lengths H
  have hr := EncodedColorNormalizedData.records_length_le ha hb hc
    (g := bandSize n) (hg := bandSize_pos n) (hsA := hsA) (hsB := hsB) (hsC := hsC)
  have hs := SourceBandCosts.size_le_bandCount (n := n) (le_refl n)
  exact hr.trans (Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hs 2))

theorem incidences_length_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (incidences n A B C hsA hsB hsC).length ≤ bandSize n*(3*bandCount n^2) := by
  unfold incidences
  rw [BandRawA.values_length]
  exact (BandRawA.items_length_le ..).trans (Nat.mul_le_mul_left _ (records_length_le H))

theorem wanted_count_le (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    (μ (EncodedColorPipelineData.wantedHeader free n (incidences n A B C hsA hsB hsC).length)).toNat ≤
      UniformStageBounds.wantedBudget n := by
  apply UniformStageBounds.wanted_le_budget
  have hw := H.countBound
  have hc := Nat.mul_le_mul_right
    (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (Nat.mul_le_mul_left 3 (incidences_length_le H))
  have hn : 3*(bandSize n*(3*bandCount n^2))*
      LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n))=
      MassScales.wantedNumerator n := by
    rw [total_keys_eq]
    unfold MassScales.wantedNumerator
    ring
  rw [hn] at hc
  rw [Nat.mul_comm] at hw
  exact hw.trans hc

def falseScore (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : ℕ :=
  LightDenseSetup.falseScore (LightPrimePool.prime (primeWindow n)) (LightPrimePool.size (primeWindow n))
    (EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC)
    A.length B.length C.length (bandSize n)
    (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
    (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC)

theorem false_score_eq (n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    falseScore n A B C hsA hsB hsC=
      BandPrimeScales.score n (BandPrimeScales.modulus n A.length B.length C.length
        (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC))
        A.length B.length C.length (fun j => A.getD j 0) (fun j => B.getD j 0) (fun j => C.getD j 0)
        (BandRawA.sortedRecords A B C (bandSize n) (bandSize_pos n) hsA hsB hsC) := by
  unfold falseScore
  rw [LightDenseSetup.falseScore_eq]
  rfl

theorem false_score_le_budget {k : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hbudget : divisorBudget k n*primeWindow n ≤ candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hx : ∀ i, |x i| ≤ ((n^k : ℕ) : ℤ)) :
    falseScore n A B C hsA hsB hsC ≤ UniformStageBounds.falseBudget k n := by
  obtain ⟨ha,hb,hc⟩ := normalized_values H hx
  have ha' : ∀ j < A.length, |A.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using ha
  have hb' : ∀ j < B.length, |B.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using hb
  have hc' : ∀ j < C.length, |C.getD j 0| ≤ (n^k : ℤ) := by simpa only [Nat.cast_pow] using hc
  rw [false_score_eq]
  exact UniformStageBounds.false_le_budget
    (BandPrimeScales.score_loss _ _ _ _ hbudget ha' hb' hc')
    (BandPrimeScales.initial_score_bound _ _ _ _ (records_length_le H))
    (BandPrimeScales.modulus_loss n _ _ _ _ _ _ _)

theorem threshold_le_budget {k : ℕ}
    (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC)
    (hbudget : divisorBudget k n*primeWindow n ≤ candidateCount n*(4*(k+2)*(inputBits n+1)))
    (hx : ∀ i, |x i| ≤ ((n^k : ℕ) : ℤ)) :
    representationCap (microHalf (inputBits n)) (blockCount (inputBits n))*falseScore n A B C hsA hsB hsC ≤
      UniformStageBounds.falseBudget k n*TrimScales.representationBound n := by
  rw [representation_cap_eq,Nat.mul_comm]
  exact Nat.mul_le_mul_right _ (false_score_le_budget H hbudget hx)

open Filter

theorem threshold_eventually (k : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (μ : ℕ → ℤ) (free : ℕ) (color : Coloring.Parameter (inputBits n+1))
      (x : Fin n → ℤ) (A B C : List ℤ)
      (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)),
      EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC →
      (∀ i, |x i| ≤ ((n^k : ℕ) : ℤ)) →
      representationCap (microHalf (inputBits n)) (blockCount (inputBits n))*falseScore n A B C hsA hsB hsC ≤
        UniformStageBounds.falseBudget k n*TrimScales.representationBound n := by
  filter_upwards [actual_divisor_budget k] with n hn
  intro μ free color x A B C hsA hsB hsC H hx
  exact threshold_le_budget H hn hx

end ThreeSum.ThreeSumColorBudgets
