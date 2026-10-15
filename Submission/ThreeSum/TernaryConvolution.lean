import Submission.ThreeSum.TernaryReconstruction
import Submission.ThreeSum.TernaryTransform
import Mathlib.Algebra.BigOperators.Finprod

/-! Exact factorial-weighted top-rank convolution on the ternary word lattice. -/

noncomputable section
namespace ThreeSum.TernaryConvolution

open Finset ThreeSum.TernaryJointType ThreeSum.TernaryBank
open ThreeSum.TernaryEuler ThreeSum.TernaryQuery ThreeSum.TernaryReconstruction

set_option maxHeartbeats 2000000

def digitCoefficient (q a b : Fin 3) : ℤ :=
  ∑ r : Fin 3, inverseCoefficient q r * digitChoose r a * digitChoose r b

def pairCoefficient {N : ℕ} (Q A B : TritWord N) : ℤ :=
  ∏ i, digitCoefficient (Q i) (A i) (B i)

def factorial {N : ℕ} (A : TritWord N) : ℤ := ∏ i, ((A i).val.factorial : ℤ)

def Adds {N : ℕ} (A B Q : TritWord N) : Prop :=
  ∀ i, (A i).val+(B i).val=(Q i).val

instance {N : ℕ} (A B Q : TritWord N) : Decidable (Adds A B Q) :=
  inferInstanceAs (Decidable (∀ i, (A i).val+(B i).val=(Q i).val))

def convolution {N : ℕ} (f g : TritWord N → ℤ) (Q : TritWord N) : ℤ :=
  ∑ A, ∑ B, if Adds A B Q then f A*g B else 0

def inverseWeight {N : ℕ} (Q R : TritWord N) : ℤ :=
  ∏ i, inverseCoefficient (Q i) (R i)

def binomialInverse {N : ℕ} (H : TritWord N → ℤ) (Q : TritWord N) : ℤ :=
  ∑ R, inverseWeight Q R * H R

theorem factorial_eq_power_two {N : ℕ} (A : TritWord N) :
    factorial A=(2 : ℤ)^digitCount A 2 := by
  have hlocal (d : Fin 3) : (d.val.factorial : ℤ) =
      (2 : ℤ)^(if d=2 then 1 else 0 : ℕ) := by
    fin_cases d <;> norm_num [Fin.ext_iff,Nat.factorial]
  unfold factorial
  simp_rw [hlocal]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem factorial_pos {N : ℕ} (A : TritWord N) : 0<factorial A := by
  rw [factorial_eq_power_two]
  positivity

theorem factorial_ne_zero {N : ℕ} (A : TritWord N) : factorial A≠0 :=
  ne_of_gt (factorial_pos A)

def partialKernel {N : ℕ} (s : Finset (Fin N)) (Q A : TritWord N) : ℤ :=
  ∏ i, if i ∈ s then inverseCoefficient (Q i) (A i) else if A i=Q i then 1 else 0

def partialInverse {N : ℕ} (s : Finset (Fin N)) (H : TritWord N → ℤ)
    (Q : TritWord N) : ℤ := ∑ A, partialKernel s Q A * H A

theorem partialKernel_empty {N : ℕ} (Q A : TritWord N) :
    partialKernel ∅ Q A=if A=Q then 1 else 0 := by
  by_cases h : A=Q
  · subst A
    simp [partialKernel]
  · simp only [partialKernel,notMem_empty,↓reduceIte,h]
    obtain ⟨i,hi⟩ : ∃ i, A i≠Q i := by
      by_contra hn
      apply h
      funext i
      exact not_not.mp (not_exists.mp hn i)
    exact Finset.prod_eq_zero (mem_univ i) (by simp [hi])

theorem partialInverse_empty {N : ℕ} (H : TritWord N → ℤ) :
    partialInverse ∅ H=H := by
  funext Q
  simp [partialInverse,partialKernel_empty]

theorem partialInverse_univ {N : ℕ} (H : TritWord N → ℤ) :
    partialInverse univ H=binomialInverse H := by
  funext Q
  simp [partialInverse,partialKernel,binomialInverse,inverseWeight]

private theorem inverse_delta (q a : Fin 3) (C : ℤ) :
    inverseDigit (fun d => (if a=d then 1 else 0)*C) q =
      inverseCoefficient q a*C := by
  fin_cases q <;> fin_cases a <;>
    norm_num [inverseDigit,inverseCoefficient,Nat.choose,Fin.le_def,Fin.ext_iff] <;> ring

theorem coordinateInverse_sum {N : ℕ} {α : Type*} [Fintype α]
    (i : Fin N) (H : α → TritWord N → ℤ) (Q : TritWord N) :
    coordinateInverse i (fun R => ∑ A, H A R) Q =
      ∑ A, coordinateInverse i (H A) Q := by
  generalize hd : Q i=d
  fin_cases d <;>
    simp [coordinateInverse,inverseDigit,hd,Fin.ext_iff,
      Finset.sum_sub_distrib,Finset.sum_add_distrib,Finset.mul_sum]

theorem coordinateInverse_kernel {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i∉s) (A Q : TritWord N) (C : ℤ) :
    coordinateInverse i (fun R => partialKernel s R A*C) Q =
      partialKernel (insert i s) Q A*C := by
  let other : ℤ := ∏ j ∈ (univ : Finset (Fin N)).erase i,
    if j∈s then inverseCoefficient (Q j) (A j) else if A j=Q j then 1 else 0
  have hu (d : Fin 3) : partialKernel s (Function.update Q i d) A =
      (if A i=d then 1 else 0)*other := by
    unfold partialKernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [hi,↓reduceIte,Function.update_self]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    simp [Function.update_of_ne (mem_erase.mp hj).1]
  have hv : partialKernel (insert i s) Q A = inverseCoefficient (Q i) (A i)*other := by
    unfold partialKernel
    rw [← Finset.mul_prod_erase univ _ (mem_univ i)]
    simp only [mem_insert_self,↓reduceIte]
    congr 1
    apply Finset.prod_congr rfl
    intro j hj
    have hji := (mem_erase.mp hj).1
    simp [hji]
  unfold coordinateInverse
  simp_rw [hu,mul_assoc]
  rw [inverse_delta,hv]
  ring

theorem coordinateInverse_partial {N : ℕ} (s : Finset (Fin N)) (i : Fin N)
    (hi : i∉s) (H : TritWord N → ℤ) :
    coordinateInverse i (partialInverse s H)=partialInverse (insert i s) H := by
  funext Q
  unfold partialInverse
  rw [coordinateInverse_sum]
  apply Finset.sum_congr rfl
  intro A hA
  exact coordinateInverse_kernel s i hi A Q (H A)

theorem frozenInverse_eq_partial {N : ℕ} (coords : List (Fin N)) (h : coords.Nodup)
    (H : TritWord N → ℤ) : frozenInverse coords H=partialInverse coords.toFinset H := by
  induction coords with
  | nil => simpa [frozenInverse] using (partialInverse_empty H).symm
  | cons i rest ih =>
    obtain ⟨hi,hn⟩ := List.nodup_cons.mp h
    change coordinateInverse i (frozenInverse rest H)=_
    rw [ih hn,List.toFinset_cons]
    exact coordinateInverse_partial rest.toFinset i (by simpa using hi) H

theorem frozenInverse_eq_binomialInverse {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset=univ) (H : TritWord N → ℤ) :
    frozenInverse coords H=binomialInverse H := by
  rw [frozenInverse_eq_partial coords h,hall,partialInverse_univ]

theorem frozenInverse_append {N : ℕ} (xs ys : List (Fin N)) (H : TritWord N → ℤ) :
    frozenInverse (xs++ys) H=frozenInverse xs (frozenInverse ys H) := by
  induction xs with
  | nil => rfl
  | cons i rest ih =>
    funext Q
    simp only [List.cons_append,frozenInverse,ih]

theorem runInverse_eq_frozen_reverse {N : ℕ} (coords : List (Fin N))
    (H : TritWord N → ℤ) : runInverse coords H=frozenInverse coords.reverse H := by
  induction coords generalizing H with
  | nil => rfl
  | cons i rest ih =>
    rw [runInverse,ih,List.reverse_cons,frozenInverse_append]
    rfl

theorem runInverse_eq_binomialInverse {N : ℕ} (coords : List (Fin N))
    (h : coords.Nodup) (hall : coords.toFinset=univ) (H : TritWord N → ℤ) :
    runInverse coords H=binomialInverse H := by
  rw [runInverse_eq_frozen_reverse]
  exact frozenInverse_eq_binomialInverse coords.reverse (by simpa using h)
    (by simpa using hall) H

theorem digitCoefficient_zero_of_lt (q a b : Fin 3)
    (h : a.val+b.val<q.val) : digitCoefficient q a b=0 := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;>
    norm_num [digitCoefficient,inverseCoefficient,digitChoose,Fin.sum_univ_succ,
      Nat.choose,Fin.le_def] at *

theorem digitCoefficient_rank_le (q a b : Fin 3) (h : digitCoefficient q a b≠0) :
    q.val≤a.val+b.val := by
  by_contra hn
  exact h (digitCoefficient_zero_of_lt q a b (by omega))

theorem digitCoefficient_factorial (q a b : Fin 3) (h : a.val+b.val=q.val) :
    digitCoefficient q a b * (a.val.factorial : ℤ) * (b.val.factorial : ℤ) =
      (q.val.factorial : ℤ) := by
  fin_cases q <;> fin_cases a <;> fin_cases b <;>
    norm_num [digitCoefficient,inverseCoefficient,digitChoose,Fin.sum_univ_succ,
      Nat.choose,Nat.factorial,Fin.le_def] at *

theorem pairCoefficient_adds {N : ℕ} (Q A B : TritWord N)
    (hrank : rank A+rank B=rank Q) (hn : pairCoefficient Q A B≠0) : Adds A B Q := by
  have hlocal : ∀ i, digitCoefficient (Q i) (A i) (B i)≠0 := by
    intro i hz
    apply hn
    unfold pairCoefficient
    exact Finset.prod_eq_zero (mem_univ i) hz
  have hle : ∀ i, (Q i).val≤(A i).val+(B i).val :=
    fun i => digitCoefficient_rank_le _ _ _ (hlocal i)
  intro i
  by_contra hn
  have hlei := hle i
  have hlt : (Q i).val<(A i).val+(B i).val := by omega
  have hs := Finset.sum_lt_sum (fun j (_ : j ∈ (univ : Finset (Fin N))) => hle j)
    ⟨i,mem_univ i,hlt⟩
  rw [Finset.sum_add_distrib] at hs
  change rank Q<rank A+rank B at hs
  omega

theorem pairCoefficient_factorial {N : ℕ} (Q A B : TritWord N)
    (hrank : rank A+rank B=rank Q) :
    pairCoefficient Q A B * factorial A * factorial B =
      if Adds A B Q then factorial Q else 0 := by
  by_cases hadd : Adds A B Q
  · simp only [hadd,↓reduceIte]
    unfold pairCoefficient factorial
    rw [← Finset.prod_mul_distrib,← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro i hi
    exact digitCoefficient_factorial _ _ _ (hadd i)
  · have hz : pairCoefficient Q A B=0 := by
      by_contra hn
      exact hadd (pairCoefficient_adds Q A B hrank hn)
    simp [hadd,hz]

theorem coefficient_sum {N : ℕ} (Q A B : TritWord N) :
    (∑ R : TritWord N, inverseWeight Q R * weight R A * weight R B) =
      pairCoefficient Q A B := by
  unfold pairCoefficient digitCoefficient
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro R hR
  unfold inverseWeight weight
  rw [Finset.prod_mul_distrib,Finset.prod_mul_distrib]

theorem inverse_product_expand {N : ℕ} (f g : TritWord N → ℤ) (Q : TritWord N) :
    binomialInverse (fun R => binomialZeta f R * binomialZeta g R) Q =
      ∑ A, ∑ B, pairCoefficient Q A B * f A * g B := by
  unfold binomialInverse binomialZeta
  simp only [Finset.mul_sum,Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro B hB
  calc
    (∑ R, inverseWeight Q R * (weight R B * f B * (weight R A * g A))) =
        (∑ R, inverseWeight Q R * weight R B * weight R A) * f B * g A := by
      rw [Finset.sum_mul,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro R hR
      ring
    _ = pairCoefficient Q B A * f B * g A := by rw [coefficient_sum]

/-- The top-rank coefficient is exactly the original convolution, times Q!. -/
theorem factorial_convolution {N a b : ℕ} (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    binomialInverse
      (fun R => binomialZeta (fun A => factorial A*f A) R *
        binomialZeta (fun B => factorial B*g B) R) Q =
      factorial Q * convolution f g Q := by
  rw [inverse_product_expand]
  unfold convolution
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro B hB
  by_cases hzA : f A=0
  · simp [hzA]
  by_cases hzB : g B=0
  · simp [hzB]
  have hrank : rank A+rank B=rank Q := by rw [hf A hzA,hg B hzB,hQ]
  have hp := pairCoefficient_factorial Q A B hrank
  calc
    pairCoefficient Q A B * (factorial A*f A) * (factorial B*g B) =
      (pairCoefficient Q A B * factorial A * factorial B) * (f A*g B) := by ring
    _ = (if Adds A B Q then factorial Q else 0) * (f A*g B) := by rw [hp]
    _ = factorial Q * (if Adds A B Q then f A*g B else 0) := by
      split_ifs <;> ring

/-- The actual coordinate transforms have the exact top-rank convolution law. -/
theorem stages_factorial_convolution {N a b : ℕ} (coords : List (Fin N))
    (hn : coords.Nodup) (hall : coords.toFinset=univ) (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    runInverse coords
      (fun R => runZeta coords (fun A => factorial A*f A) R *
        runZeta coords (fun B => factorial B*g B) R) Q =
      factorial Q * convolution f g Q := by
  rw [runInverse_eq_binomialInverse coords hn hall,
    ThreeSum.TernaryTransform.runZeta_eq_binomialZeta coords hn hall,
    ThreeSum.TernaryTransform.runZeta_eq_binomialZeta coords hn hall]
  exact factorial_convolution f g hf hg Q hQ

theorem stages_div_convolution {N a b : ℕ} (coords : List (Fin N))
    (hn : coords.Nodup) (hall : coords.toFinset=univ) (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    runInverse coords
      (fun R => runZeta coords (fun A => factorial A*f A) R *
        runZeta coords (fun B => factorial B*g B) R) Q / factorial Q =
      convolution f g Q := by
  rw [stages_factorial_convolution coords hn hall f g hf hg Q hQ]
  exact Int.mul_ediv_cancel_left _ (factorial_ne_zero Q)

theorem stages_zero_iff_convolution_zero {N a b : ℕ} (coords : List (Fin N))
    (hn : coords.Nodup) (hall : coords.toFinset=univ) (f g : TritWord N → ℤ)
    (hf : ∀ A, f A≠0 → rank A=a) (hg : ∀ B, g B≠0 → rank B=b)
    (Q : TritWord N) (hQ : rank Q=a+b) :
    runInverse coords
      (fun R => runZeta coords (fun A => factorial A*f A) R *
        runZeta coords (fun B => factorial B*g B) R) Q=0 ↔
      convolution f g Q=0 := by
  rw [stages_factorial_convolution coords hn hall f g hf hg Q hQ]
  simp [factorial_ne_zero Q]

end ThreeSum.TernaryConvolution
