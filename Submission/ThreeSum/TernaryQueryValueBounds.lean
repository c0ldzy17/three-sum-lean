import Submission.ThreeSum.TernaryConvolution

/-! Integer value bounds for physical source histograms and their query tables. -/
namespace ThreeSum.TernaryQueryValueBounds
open Finset ThreeSum.TernaryJointType ThreeSum.TernaryEuler ThreeSum.TernaryConvolution
set_option maxHeartbeats 3000000

theorem weighted_digit (r a : Fin 3) :
    0≤digitChoose r a*(a.val.factorial : ℤ) ∧ digitChoose r a*(a.val.factorial : ℤ)≤2 := by
  fin_cases r <;> fin_cases a <;> norm_num [digitChoose,Nat.choose,Nat.factorial]

theorem weighted_kernel {N : ℕ} (R A : TritWord N) :
    0≤weight R A*factorial A ∧ weight R A*factorial A≤(2 : ℤ)^N := by
  unfold weight factorial
  rw [←Finset.prod_mul_distrib]
  constructor
  · exact Finset.prod_nonneg (fun i _ => (weighted_digit (R i) (A i)).1)
  · calc
      (∏ i, digitChoose (R i) (A i)*((A i).val.factorial : ℤ))≤∏ i : Fin N, (2 : ℤ) :=
        Finset.prod_le_prod (fun i _ => (weighted_digit (R i) (A i)).1)
          (fun i _ => (weighted_digit (R i) (A i)).2)
      _=(2 : ℤ)^N := by simp

def mass {N : ℕ} (f : TritWord N→ℤ) : ℤ :=∑ A, |f A|

theorem mass_nonneg {N : ℕ} (f : TritWord N→ℤ) : 0≤mass f :=
  Finset.sum_nonneg (fun _ _ => abs_nonneg _)

theorem weighted_zeta_abs {N : ℕ} (f : TritWord N→ℤ) (R : TritWord N) :
    |binomialZeta (fun A => factorial A*f A) R|≤(2 : ℤ)^N*mass f := by
  unfold binomialZeta mass
  calc
    |∑ A, weight R A*(factorial A*f A)|≤∑ A, |weight R A*(factorial A*f A)| :=
      Finset.abs_sum_le_sum_abs _ _
    _≤∑ A : TritWord N, (2 : ℤ)^N*|f A| := by
      apply Finset.sum_le_sum
      intro A _
      rw [←mul_assoc,abs_mul,abs_of_nonneg (weighted_kernel R A).1]
      exact mul_le_mul_of_nonneg_right (weighted_kernel R A).2 (abs_nonneg _)
    _=(2 : ℤ)^N*∑ A, |f A| := by rw [Finset.mul_sum]

theorem product_abs {N : ℕ} (f g : TritWord N→ℤ) (R : TritWord N) :
    |binomialZeta (fun A => factorial A*f A) R *
      binomialZeta (fun B => factorial B*g B) R|≤(4 : ℤ)^N*mass f*mass g := by
  rw [abs_mul]
  have hf := weighted_zeta_abs f R
  have hg := weighted_zeta_abs g R
  calc
    |binomialZeta (fun A => factorial A*f A) R| *
        |binomialZeta (fun B => factorial B*g B) R|≤
        ((2 : ℤ)^N*mass f)*((2 : ℤ)^N*mass g) :=
      mul_le_mul hf hg (abs_nonneg _) (mul_nonneg (by positivity) (mass_nonneg f))
    _=(4 : ℤ)^N*mass f*mass g := by
      rw [show ((2 : ℤ)^N*mass f)*((2 : ℤ)^N*mass g)=
        ((2 : ℤ)^N*(2 : ℤ)^N)*mass f*mass g by ring,←mul_pow]
      norm_num

theorem product_abs_of_mass {N : ℕ} (f g : TritWord N→ℤ) (A B : ℕ)
    (hf : mass f≤(A : ℤ)) (hg : mass g≤(B : ℤ)) (R : TritWord N) :
    |binomialZeta (fun a => factorial a*f a) R *
      binomialZeta (fun b => factorial b*g b) R|≤((4^N*A*B : ℕ) : ℤ) := by
  have hm : mass f*mass g≤(A : ℤ)*(B : ℤ) :=
    mul_le_mul hf hg (mass_nonneg g) (by positivity)
  have hh := mul_le_mul_of_nonneg_left hm (by positivity : 0≤(4 : ℤ)^N)
  rw [←mul_assoc,←mul_assoc] at hh
  simpa [Nat.cast_mul,Nat.cast_pow,mul_assoc] using (product_abs f g R).trans hh

end ThreeSum.TernaryQueryValueBounds
