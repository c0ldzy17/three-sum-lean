import Submission.ThreeSum.TernaryWeightChannels
import Submission.ThreeSum.TernaryPairedTensor

/-! Exact finite physical-pair types for moment and quartic source channels. -/
noncomputable section
namespace ThreeSum.TernaryPhysicalTensorChannels
open Finset TernaryJointType TernaryWeightedPhysicalSources TernaryWeightChannels
open scoped BigOperators

variable {ι κ I : Type*}

def records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N) (Q : TritWord N) : Finset (ι×κ) := by
  classical
  exact (S×ˢT).filter fun x => TernaryConvolution.Adds (left x.1) (right x.2) Q

theorem sum_records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N) (Q : TritWord N) (F : ι×κ→ℤ) :
    (∑ x : records S T left right Q, F x.val)=
      ∑ i∈S, ∑ j∈T, if TernaryConvolution.Adds (left i) (right j) Q then F (i,j) else 0 := by
  classical
  rw [sum_coe_sort]
  unfold records
  rw [sum_filter,sum_product]

theorem moment_on_physical_records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), TernaryConvolution.convolution
      (histogram S left (fun i => (leftMoment k j).eval (fun _ => B i)))
      (histogram T right (fun i => (rightMoment k j).eval (fun _ => C i))) Q)=
      ∑ x : records S T left right Q, (C x.val.2-B x.val.1)^k := by
  rw [convolution_moment_channels]
  exact (sum_records S T left right Q (fun x => (C x.2-B x.1)^k)).symm

theorem fourth_tensor_on_physical_records {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (L : ι→I→ℤ) (R : κ→I→ℤ) (a b c d : I) (Q : TritWord N) :
    TernaryConvolution.convolution
      (histogram S left (productWeight L a b))
      (histogram T right (productWeight R c d)) Q=
      TernaryPairedTensor.tensor (fun x : records S T left right Q => L x.val.1)
        (fun x : records S T left right Q => R x.val.2) a b c d := by
  rw [convolution_histograms,fourth_pair_channel]
  unfold TernaryPairedTensor.tensor
  exact (sum_records S T left right Q (fun x => L x.1 a*L x.1 b*R x.2 c*R x.2 d)).symm

end ThreeSum.TernaryPhysicalTensorChannels
