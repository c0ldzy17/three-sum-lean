import Submission.ThreeSum.TernaryPhysicalSources
import Submission.ThreeSum.LightTernaryWeightedHistogram

/-!
# Signed original-record channels in the exact ternary convolution

Weights belong to physical join records, not to distinct word values.
Thus equal words retain both their multiplicity and their original weights.
-/

noncomputable section
namespace ThreeSum.TernaryWeightedPhysicalSources

open Finset TernaryJointType TernaryBank TernaryConvolution
open scoped BigOperators

variable {ι κ : Type*}

def histogram {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (weight : ι → ℤ) (A : TritWord N) : ℤ :=
  ∑ i ∈ S, if word i=A then weight i else 0

theorem histogram_homogeneous {N h : ℕ} (S : Finset ι)
    (word : ι → TritWord N) (weight : ι → ℤ)
    (hrank : ∀ i ∈ S, rank (word i)=h) :
    ∀ A, histogram S word weight A≠0 → rank A=h := by
  classical
  intro A hA
  by_contra hneq
  apply hA
  unfold histogram
  apply sum_eq_zero
  intro i hi
  have hn : word i≠A := by
    intro he
    exact hneq (by rw [← he]; exact hrank i hi)
  simp [hn]

theorem histogram_type_homogeneous {N : ℕ} (S : Finset ι)
    (word : ι → TritWord N) (weight : ι → ℤ) (α : DigitType)
    (htype : ∀ i ∈ S, HasType (word i) α) :
    ∀ A, histogram S word weight A≠0 → rank A=α 1+2*α 2 :=
  histogram_homogeneous S word weight
    (fun i hi => TernaryPhysicalSources.rank_of_type (htype i hi))

theorem histogram_sum {N : ℕ} (S : Finset ι) (word : ι → TritWord N)
    (weight : ι → ℤ) (F : TritWord N → ℤ) :
    (∑ A, histogram S word weight A*F A)=∑ i ∈ S, weight i*F (word i) := by
  classical
  unfold histogram
  simp only [sum_mul,ite_mul,zero_mul]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  simp

def pairWeight {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N)
    (leftWeight : ι → ℤ) (rightWeight : κ → ℤ) (Q : TritWord N) : ℤ :=
  ∑ i ∈ S, ∑ j ∈ T,
    if Adds (left i) (right j) Q then leftWeight i*rightWeight j else 0

theorem convolution_histograms {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι → TritWord N) (right : κ → TritWord N)
    (leftWeight : ι → ℤ) (rightWeight : κ → ℤ) (Q : TritWord N) :
    convolution (histogram S left leftWeight) (histogram T right rightWeight) Q=
      pairWeight S T left right leftWeight rightWeight Q := by
  classical
  have hcon : convolution (histogram S left leftWeight)
      (histogram T right rightWeight) Q=
      ∑ A, histogram S left leftWeight A*
        (∑ B, histogram T right rightWeight B*(if Adds A B Q then 1 else 0)) := by
    unfold convolution
    apply sum_congr rfl
    intro A hA
    rw [mul_sum]
    apply sum_congr rfl
    intro B hB
    split <;> simp_all
  rw [hcon,histogram_sum]
  unfold pairWeight
  apply sum_congr rfl
  intro i hi
  rw [histogram_sum,mul_sum]
  apply sum_congr rfl
  intro j hj
  split <;> simp_all

/-- The physical weighted loop has exactly the histogram semantics when
its compact enumeration is injective on the bank. -/
theorem histogram_eq_machine_total {N bank n r : ℕ}
    (enumeration : ℕ → TritWord N) (key : ℕ → ℕ) (weight : ℕ → ℤ)
    (hr : r < bank) (hkey : ∀ j < n, key j < bank)
    (hinj : ∀ i j, i < bank → j < bank → enumeration i=enumeration j → i=j) :
    histogram (range n) (fun i => enumeration (key i)) weight (enumeration r)=
      LightTernaryWeightedHistogram.total key weight r n := by
  classical
  unfold histogram LightTernaryWeightedHistogram.total
  apply sum_congr rfl
  intro j hj
  have he : enumeration (key j)=enumeration r ↔ key j=r := by
    exact ⟨hinj _ _ (hkey j (mem_range.mp hj)) hr,fun h => by rw [h]⟩
  simp only [he]

end ThreeSum.TernaryWeightedPhysicalSources
