import Submission.ThreeSum.LightArray

/-! # Actual pointwise product of the two compressed source banks -/

namespace ThreeSum.LightTernaryProduct

open Light ThreeSum.LightArray

def body : Stmt :=
  pass 4 (v 3) (v 2) (M (v 0 +' v 4) *' M (v 1 +' v 4))

def time (n : ℕ) : ℕ := 24*n+10

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {p a b dst n U V : ℕ} (hprog : P[p]? = some body)
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hb : b+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsepA : SourceSafe a dst n) (hsepB : SourceSafe b dst n)
    (hA : ∀ j < n, |μ (a+j)| ≤ U) (hB : ∀ j < n, |μ (b+j)| ≤ V)
    (hword : (U : ℤ)*(V : ℤ) ≤ lim.word) :
    Meets lim P p d [a,b,dst,n] μ (time n)
      (fun _ μ' => (∀ j < n, μ' (dst+j) = μ (a+j)*μ (b+j)) ∧
        SameOutside μ μ' dst n) := by
  apply Meets.of_body hprog
  unfold body time
  refine Ends.pass (fun j => μ (a+j)*μ (b+j)) (fun j hj => ?_)
    ⟨fun j hj => wrote_done (f := fun j => μ (a+j)*μ (b+j)) hj,
      by light_keep⟩ hw hdst rfl rfl
    (hT := by light_time)
  have hrA := source_read (μ := μ) (f := fun j => μ (a+j)*μ (b+j)) hsepA hj
  have hrB := source_read (μ := μ) (f := fun j => μ (a+j)*μ (b+j)) hsepB hj
  have hprod : |μ (a+j)*μ (b+j)| ≤ (U : ℤ)*(V : ℤ) := by
    rw [abs_mul]
    exact mul_le_mul (hA j hj) (hB j hj) (abs_nonneg _) (Int.natCast_nonneg _)
  have hbounds := abs_le.mp (hprod.trans hword)
  light_side [hrA,hrB]

def program : Program := [body]

end ThreeSum.LightTernaryProduct
