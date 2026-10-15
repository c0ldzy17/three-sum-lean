import Submission.ThreeSum.TernaryWeightedPhysicalSources
import Submission.ThreeSum.LightFixedArithmetic

/-! Fixed signed source channels, with exact original-record pair semantics. -/
namespace ThreeSum.TernaryWeightChannels
open Finset LightFixedArithmetic TernaryJointType TernaryWeightedPhysicalSources
open scoped BigOperators

def powerCircuit (e : Circuit) : ℕ→Circuit
  | 0 => .literal 1
  | k+1 => .mul (powerCircuit e k) e

@[simp] theorem powerCircuit_eval (e : Circuit) (k : ℕ) (x : ℕ→ℤ) :
    (powerCircuit e k).eval x=(e.eval x)^k := by
  induction k with
  | zero => simp [powerCircuit,Circuit.eval]
  | succ k ih => simp [powerCircuit,Circuit.eval,ih,pow_succ]

def scalarPower (k : ℕ) : Circuit := powerCircuit (.atom 0) k
def leftMoment (k j : ℕ) : Circuit :=
  .mul (.literal (k.choose j : ℤ)) (powerCircuit (.sub (.literal 0) (.atom 0)) j)
def rightMoment (k j : ℕ) : Circuit := scalarPower (k-j)

@[simp] theorem scalarPower_eval (k : ℕ) (x : ℕ→ℤ) :
    (scalarPower k).eval x=(x 0)^k := by simp [scalarPower,Circuit.eval]
@[simp] theorem leftMoment_eval (k j : ℕ) (x : ℕ→ℤ) :
    (leftMoment k j).eval x=(k.choose j : ℤ)*(-(x 0))^j := by
  simp [leftMoment,Circuit.eval]
@[simp] theorem rightMoment_eval (k j : ℕ) (x : ℕ→ℤ) :
    (rightMoment k j).eval x=(x 0)^(k-j) := by simp [rightMoment]

theorem difference_power_channels (k : ℕ) (b c : ℤ) :
    (c-b)^k=∑ j∈range (k+1), (k.choose j : ℤ)*(-b)^j*c^(k-j) := by
  have h := add_pow (-b) c k
  rw [show -b+c=c-b by ring] at h
  rw [h]
  apply sum_congr rfl
  intro j hj
  ring

variable {ι κ I : Type*}

theorem pair_moment_channels {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), pairWeight S T left right
      (fun i => (leftMoment k j).eval (fun _ => B i))
      (fun i => (rightMoment k j).eval (fun _ => C i)) Q)=
      ∑ b∈S, ∑ c∈T, if TernaryConvolution.Adds (left b) (right c) Q then
        (C c-B b)^k else 0 := by
  classical
  simp only [leftMoment_eval,rightMoment_eval,pairWeight]
  rw [sum_comm]
  apply sum_congr rfl
  intro b hb
  rw [sum_comm]
  apply sum_congr rfl
  intro c hc
  by_cases h : TernaryConvolution.Adds (left b) (right c) Q
  · simp only [h,if_true]
    exact (difference_power_channels k (B b) (C c)).symm
  · simp [h]

/-- Shared weighted source banks compute the exact integer moment of the
physical pair measure, retaining repeated words and original multiplicity. -/
theorem convolution_moment_channels {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (B : ι→ℤ) (C : κ→ℤ) (Q : TritWord N) (k : ℕ) :
    (∑ j∈range (k+1), TernaryConvolution.convolution
      (histogram S left (fun i => (leftMoment k j).eval (fun _ => B i)))
      (histogram T right (fun i => (rightMoment k j).eval (fun _ => C i))) Q)=
      ∑ b∈S, ∑ c∈T, if TernaryConvolution.Adds (left b) (right c) Q then
        (C c-B b)^k else 0 := by
  simp_rw [convolution_histograms]
  exact pair_moment_channels S T left right B C Q k

def productWeight (F : ι→I→ℤ) (a b : I) (i : ι) : ℤ := F i a*F i b

theorem fourth_pair_channel {N : ℕ} (S : Finset ι) (T : Finset κ)
    (left : ι→TritWord N) (right : κ→TritWord N)
    (L : ι→I→ℤ) (R : κ→I→ℤ) (a b c d : I) (Q : TritWord N) :
    pairWeight S T left right (productWeight L a b) (productWeight R c d) Q=
      ∑ i∈S, ∑ j∈T, if TernaryConvolution.Adds (left i) (right j) Q then
        L i a*L i b*R j c*R j d else 0 := by
  classical
  unfold pairWeight productWeight
  apply sum_congr rfl
  intro i hi
  apply sum_congr rfl
  intro j hj
  split <;> ring

end ThreeSum.TernaryWeightChannels
