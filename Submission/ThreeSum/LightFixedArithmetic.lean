import Submission.ThreeSum.LightSignedFiniteTable
import Mathlib.Tactic

/-! Fixed integer arithmetic circuits compile to literal Light expression trees.
The circuit is fixed program text; input atoms are ordinary words or memory reads. -/
namespace ThreeSum.LightFixedArithmetic
open Light

inductive Circuit where
  | literal (z : ℤ)
  | atom (i : ℕ)
  | add (a b : Circuit)
  | sub (a b : Circuit)
  | mul (a b : Circuit)

def Circuit.eval (x : ℕ → ℤ) : Circuit → ℤ
  | .literal z => z
  | .atom i => x i
  | .add a b => a.eval x+b.eval x
  | .sub a b => a.eval x-b.eval x
  | .mul a b => a.eval x*b.eval x

def Circuit.compile (atoms : ℕ → Expr) : Circuit → Expr
  | .literal z => LightSignedFiniteTable.literal z
  | .atom i => atoms i
  | .add a b => a.compile atoms +' b.compile atoms
  | .sub a b => a.compile atoms -' b.compile atoms
  | .mul a b => a.compile atoms *' b.compile atoms

/-- Bounds every intermediate arithmetic value, including literal magnitudes. -/
def Circuit.bound (U : ℤ) : Circuit → ℤ
  | .literal z => |z|+1
  | .atom _ => U+1
  | .add a b => a.bound U+b.bound U
  | .sub a b => a.bound U+b.bound U
  | .mul a b => a.bound U*b.bound U

theorem Circuit.bound_pos (e : Circuit) {U : ℤ} (hU : 0≤U) : 1≤e.bound U := by
  induction e with
  | literal z => simp only [bound]; have := abs_nonneg z; omega
  | atom i => simp only [bound]; omega
  | add a b ha hb => simp only [bound]; omega
  | sub a b ha hb => simp only [bound]; omega
  | mul a b ha hb => simp only [bound]; nlinarith

theorem Circuit.eval_abs_le (e : Circuit) (x : ℕ → ℤ) {U : ℤ}
    (hU : 0≤U) (hx : ∀ i, |x i|≤U) : |e.eval x|≤e.bound U := by
  induction e with
  | literal z => simp only [eval,bound]; omega
  | atom i => exact (hx i).trans (by simp [bound])
  | add a b ha hb => exact (abs_add_le _ _).trans (add_le_add ha hb)
  | sub a b ha hb => exact (abs_sub _ _).trans (add_le_add ha hb)
  | mul a b ha hb =>
    simp only [eval,bound,abs_mul]
    exact mul_le_mul ha hb (abs_nonneg _) (le_trans (abs_nonneg _) ha)

theorem Circuit.compile_val (e : Circuit) (atoms : ℕ → Expr) (σ : State) :
    (e.compile atoms).val σ=e.eval (fun i => (atoms i).val σ) := by
  induction e with
  | literal z => simp [compile,LightSignedFiniteTable.literal,Expr.val,Op.eval,eval,Int.toNat_sub_toNat_neg]
  | atom i => rfl
  | add a b ha hb => simp [compile,Expr.val,Op.eval,eval,ha,hb]
  | sub a b ha hb => simp [compile,Expr.val,Op.eval,eval,ha,hb]
  | mul a b ha hb => simp [compile,Expr.val,Op.eval,eval,ha,hb]

theorem Circuit.compile_safe (e : Circuit) (atoms : ℕ → Expr) (σ : State)
    {lim : Limits} {U : ℤ} (hU : 0≤U)
    (hs : ∀ i, (atoms i).Safe lim σ)
    (hx : ∀ i, |(atoms i).val σ|≤U) (hw : e.bound U≤lim.word) :
    (e.compile atoms).Safe lim σ := by
  induction e with
  | literal z =>
    have hz := abs_nonneg z
    have hpos := le_abs_self z
    have hneg := neg_le_abs z
    simp only [compile,LightSignedFiniteTable.literal,Expr.Safe,Expr.val,Op.eval]
    refine ⟨?_,?_,?_⟩
    · simp only [bound] at hw; omega
    · simp only [bound] at hw; omega
    · rw [Int.toNat_sub_toNat_neg]; simp only [bound] at hw; omega
  | atom i => exact hs i
  | add a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    refine ⟨ha (by simp only [bound] at hw; omega),hb (by simp only [bound] at hw; omega),?_⟩
    change |(a.compile atoms).val σ+(b.compile atoms).val σ|≤lim.word
    rw [a.compile_val,b.compile_val]
    exact (Circuit.eval_abs_le (.add a b) _ hU hx).trans hw
  | sub a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    refine ⟨ha (by simp only [bound] at hw; omega),hb (by simp only [bound] at hw; omega),?_⟩
    change |(a.compile atoms).val σ-(b.compile atoms).val σ|≤lim.word
    rw [a.compile_val,b.compile_val]
    exact (Circuit.eval_abs_le (.sub a b) _ hU hx).trans hw
  | mul a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    refine ⟨ha (by simp only [bound] at hw; nlinarith),hb (by simp only [bound] at hw; nlinarith),?_⟩
    change |(a.compile atoms).val σ*(b.compile atoms).val σ|≤lim.word
    rw [a.compile_val,b.compile_val]
    exact (Circuit.eval_abs_le (.mul a b) _ hU hx).trans hw

/-- A fixed circuit has a fixed polynomial word bound. -/
def Circuit.coefficient : Circuit → ℤ
  | .literal z => |z|+1
  | .atom _ => 1
  | .add a b => a.coefficient+b.coefficient
  | .sub a b => a.coefficient+b.coefficient
  | .mul a b => a.coefficient*b.coefficient

def Circuit.degree : Circuit → ℕ
  | .literal _ => 0
  | .atom _ => 1
  | .add a b => max a.degree b.degree
  | .sub a b => max a.degree b.degree
  | .mul a b => a.degree+b.degree

theorem Circuit.coefficient_pos (e : Circuit) : 1≤e.coefficient := by
  induction e with
  | literal z => simp only [coefficient]; have := abs_nonneg z; omega
  | atom i => simp [coefficient]
  | add a b ha hb => simp only [coefficient]; omega
  | sub a b ha hb => simp only [coefficient]; omega
  | mul a b ha hb => simp only [coefficient]; nlinarith

theorem Circuit.bound_polynomial (e : Circuit) {U : ℤ} (hU : 0≤U) :
    e.bound U≤e.coefficient*(U+1)^e.degree := by
  have hbase : 1≤U+1 := by omega
  induction e with
  | literal z => simp [bound,coefficient,degree]
  | atom i => simp [bound,coefficient,degree]
  | add a b ha hb | sub a b ha hb =>
    have hca := a.coefficient_pos
    have hcb := b.coefficient_pos
    have hpa : (U+1)^a.degree≤(U+1)^max a.degree b.degree :=
      pow_le_pow_right₀ hbase (Nat.le_max_left _ _)
    have hpb : (U+1)^b.degree≤(U+1)^max a.degree b.degree :=
      pow_le_pow_right₀ hbase (Nat.le_max_right _ _)
    simp only [bound,coefficient,degree]
    calc
      a.bound U+b.bound U≤a.coefficient*(U+1)^max a.degree b.degree+
          b.coefficient*(U+1)^max a.degree b.degree :=
        add_le_add (ha.trans (mul_le_mul_of_nonneg_left hpa (by omega)))
          (hb.trans (mul_le_mul_of_nonneg_left hpb (by omega)))
      _ = _ := by ring
  | mul a b ha hb =>
    have hpa := a.bound_pos hU
    have hpb := b.bound_pos hU
    simp only [bound,coefficient,degree,pow_add]
    calc
      a.bound U*b.bound U≤(a.coefficient*(U+1)^a.degree)*
          (b.coefficient*(U+1)^b.degree) := mul_le_mul ha hb (by omega) (by nlinarith)
      _ = _ := by ring

end ThreeSum.LightFixedArithmetic
