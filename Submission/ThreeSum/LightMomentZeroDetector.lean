import Submission.ThreeSum.LightMomentDeterminant

namespace ThreeSum.LightMomentZeroDetector
open Light ThreeSum.LightMomentDeterminant ThreeSum.LightFixedArithmetic
open FiniteMomentZeroDetector

/-- Atom zero is the target.  The remaining atoms read the finite moment array.
Out-of-range atoms compile to zero, so the safety contract is genuinely finite. -/
def atoms (H : ℕ) : ℕ → Expr
  | 0 => v 1
  | offset+1 => if offset≤2*H then M (v 0 +' k offset) else k 0

@[simp] theorem atoms_target (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) :
    (atoms H 0).val ⟨frame [base,a],μ⟩=a := by rfl

theorem atoms_moment (H base k : ℕ) (a : ℤ) (μ : ℕ → ℤ) (hk : k≤2*H) :
    (atoms H (k+1)).val ⟨frame [base,a],μ⟩=μ (base+k) := by
  simp [atoms,hk,Expr.val,Op.eval,frame]

theorem atoms_safe (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {lim : Limits}
    (hspace : base+(2*H+1)≤lim.space) (hw : (lim.space : ℤ)≤lim.word) :
    ∀ i, (atoms H i).Safe lim ⟨frame [base,a],μ⟩ := by
  intro i
  cases i with
  | zero => trivial
  | succ k =>
    simp only [atoms]
    split_ifs with hk
    · have haddr : base+k<lim.space := by omega
      have haddrWord : ((base+k : ℕ) : ℤ)≤lim.word := by
        have hle : ((base+k : ℕ) : ℤ)≤(lim.space : ℤ) := by exact_mod_cast (Nat.le_of_lt haddr)
        exact hle.trans hw
      have hkWord : (k : ℤ)≤lim.word := by omega
      light_side [haddr,haddrWord,hkWord]
    · change (0 : ℤ)≤lim.word
      omega

theorem atoms_abs (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) (U : ℤ)
    (hU : 0≤U) (ha : |a|≤U) (hm : ∀ k≤2*H, |μ (base+k)|≤U) :
    ∀ i, |(atoms H i).val ⟨frame [base,a],μ⟩|≤U := by
  intro i
  cases i with
  | zero => exact ha
  | succ k =>
    by_cases hk : k≤2*H
    · rw [atoms_moment H base k a μ hk]
      exact hm k hk
    · simpa [atoms,hk,Expr.val] using hU

theorem leading_memory (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hm : ∀ k≤2*H, μ (base+k)=moment v w k)
    (d : ℕ) (hd : d≤H) :
    (leading d).eval (fun i => (atoms H i).val ⟨frame [base,a],μ⟩)=(hankel v w d).det := by
  rw [eval_leading]
  congr 1
  ext i j
  change (atoms H (i.val+j.val+1)).val ⟨frame [base,a],μ⟩=moment v w (i.val+j.val)
  rw [atoms_moment H base _ a μ (by have := i.isLt; have := j.isLt; omega)]
  exact hm _ (by have := i.isLt; have := j.isLt; omega)

theorem modified_memory (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hm : ∀ k≤2*H, μ (base+k)=moment v w k)
    (d : ℕ) (hd : d≤H) :
    (modified d).eval (fun i => (atoms H i).val ⟨frame [base,a],μ⟩)=(modifiedHankel v w a d).det := by
  rw [eval_modified]
  congr 1
  ext i j
  have h0 := atoms_target H base a μ
  have h1 := atoms_moment H base (i.val+j.val) a μ (by have := i.isLt; have := j.isLt; omega)
  have h2 := atoms_moment H base (i.val+j.val+1) a μ (by have := i.isLt; have := j.isLt; omega)
  have h3 := atoms_moment H base (i.val+j.val+2) a μ (by have := i.isLt; have := j.isLt; omega)
  simp only [←Nat.add_assoc,Nat.reduceAdd] at h1 h2 h3
  simp only [Matrix.of_apply,h0,h1,h2,h3,modifiedHankel,modifiedMoment]
  simp only [Nat.add_assoc]
  rw [hm _ (by have := i.isLt; have := j.isLt; omega),
    hm _ (by have := i.isLt; have := j.isLt; omega),
    hm _ (by have := i.isLt; have := j.isLt; omega)]

/-- A complete finite Light procedure implementing exact zero-mode detection. -/
noncomputable def program (H : ℕ) : Program := [body (atoms H) H]

theorem meets (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hv : Function.Injective v) (hweights : ∀ s, w s≠0)
    (ht : t≤H) {lim : Limits} {P : Program} {p depth : ℕ}
    (hp : P[p]?=some (body (atoms H) H))
    (hspace : base+(2*H+1)≤lim.space) (hspaceWord : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (ha : |a|≤U)
    (hword : wordBound U H≤lim.word)
    (hmabs : ∀ k≤2*H, |μ (base+k)|≤U)
    (hm : ∀ k≤2*H, μ (base+k)=moment v w k) :
    Meets lim P p depth [base,a] μ (time (atoms H) H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hp
  exact body_ends H v w a hv hweights ht (atoms H) _ U hU
    (atoms_safe H base a μ hspace hspaceWord)
    (atoms_abs H base a μ U hU ha hmabs) hword
    (leading_memory H base a μ v w hm) (modified_memory H base a μ v w hm)

/-- The one-procedure program has no hidden initialization or advice. -/
theorem program_meets (H base : ℕ) (a : ℤ) (μ : ℕ → ℤ) {t : ℕ}
    (v w : Fin t → ℤ) (hv : Function.Injective v) (hweights : ∀ s, w s≠0)
    (ht : t≤H) {lim : Limits} {depth : ℕ}
    (hspace : base+(2*H+1)≤lim.space) (hspaceWord : (lim.space : ℤ)≤lim.word)
    (U : ℤ) (hU : 0≤U) (ha : |a|≤U)
    (hword : wordCoefficient H*(U+1)^wordDegree H≤lim.word)
    (hmabs : ∀ k≤2*H, |μ (base+k)|≤U)
    (hm : ∀ k≤2*H, μ (base+k)=moment v w k) :
    Meets lim (program H) 0 depth [base,a] μ (time (atoms H) H)
      (fun r ν => r=(if ∃ s, v s=a then 1 else 0 : ℤ) ∧ ν=μ) := by
  exact meets H base a μ v w hv hweights ht rfl hspace hspaceWord U hU ha
    ((wordBound_polynomial H hU).trans hword) hmabs hm

open scoped BigOperators in
/-- Ordinary polynomial bounds on the physical moments suffice; no multiword
arithmetic or denominator representation is used by the detector. -/
theorem moment_abs_bound {t H k : ℕ} (v w : Fin t → ℤ) (V : ℤ)
    (hV : 1≤V) (hv : ∀ s, |v s|≤V) (hk : k≤2*H) :
    |moment v w k|≤(∑ s, |w s|)*V^(2*H) := by
  unfold moment
  calc
    |∑ s, w s*v s^k|≤∑ s, |w s*v s^k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s, |w s| *V^(2*H) := by
      apply Finset.sum_le_sum
      intro s hs
      rw [abs_mul,abs_pow]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      exact (pow_le_pow_left₀ (abs_nonneg _) (hv s) k).trans (pow_le_pow_right₀ hV hk)
    _ = _ := by rw [Finset.sum_mul]

end ThreeSum.LightMomentZeroDetector
