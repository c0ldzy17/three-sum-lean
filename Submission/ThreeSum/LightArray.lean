import Submission.ThreeSumApsp.Lang.Lib.Copy
import Submission.ThreeSumApsp.Lang.Tactics

/-!
# Costed array arithmetic in the benchmark's imperative language

These are actual `Light.Stmt` programs and `Light.Meets` execution proofs.
Their contracts count every expression evaluation and memory operation.
-/

namespace ThreeSum.LightArray

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Reading a source in place is safe because each pass writes only earlier
indices.  Disjoint sources are safe as well. -/
def SourceSafe (src dst n : ℕ) : Prop := src = dst ∨ Apart src n dst n

theorem source_read {μ : ℕ → ℤ} {src dst n j : ℕ} {f : ℕ → ℤ}
    (h : SourceSafe src dst n) (hj : j < n) :
    wrote μ dst f j (src + j) = μ (src + j) := by
  rcases h with rfl | h
  · exact wrote_rest (by omega)
  · exact wrote_rest (by omega)

/-- linear(srcA, srcB, dst, n, c): dst[i] := srcA[i] + c*srcB[i]. -/
def linearBody : Stmt :=
  pass 5 (v 3) (v 2) (M (v 0 +' v 5) +' v 4 *' M (v 1 +' v 5))

def linearTime (n : ℕ) : ℕ := 23 * n + 6

theorem linear_meets {p : ℕ} (hp : P[p]? = some linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n)
    (hmul : ∀ i < n, |c * μ (srcB + i)| ≤ lim.word)
    (hsum : ∀ i < n, |μ (srcA + i) + c * μ (srcB + i)| ≤ lim.word) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        SameOutside μ μ' dst n := by
  refine .of_body hp (Ends.pass (fun i => μ (srcA + i) + c * μ (srcB + i))
    (fun i hi => ?_) ⟨fun i hi => wrote_done (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hi, by light_keep⟩
    hw hD rfl rfl (hT := by light_time [linearTime]))
  have hrA := source_read (μ := μ)
    (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hsepA hi
  have hrB := source_read (μ := μ)
    (f := fun i => μ (srcA + i) + c * μ (srcB + i)) hsepB hi
  have hm := abs_le.mp (hmul i hi)
  have hs := abs_le.mp (hsum i hi)
  light_side [hrA, hrB]

/-- A convenient polynomial-word bound for both addition and subtraction. -/
theorem linear_bounded_meets {p : ℕ} (hp : P[p]? = some linearBody)
    {μ : ℕ → ℤ} {srcA srcB dst n U : ℕ} {c : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : srcA + n ≤ lim.space) (hB : srcB + n ≤ lim.space)
    (hD : dst + n ≤ lim.space)
    (hsepA : SourceSafe srcA dst n) (hsepB : SourceSafe srcB dst n)
    (hc : |c| ≤ 1) (hword : 2 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (srcA + i)| ≤ U ∧ |μ (srcB + i)| ≤ U) :
    Meets lim P p d [(srcA : ℤ), srcB, dst, n, c] μ (linearTime n) fun _ μ' =>
      (∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) ∧
        SameOutside μ μ' dst n := by
  have hm : ∀ i < n, |c * μ (srcB + i)| ≤ U := by
    intro i hi
    rw [abs_mul]
    calc
      _ ≤ 1 * (U : ℤ) := mul_le_mul hc (hvalues i hi).2 (abs_nonneg _) (by omega)
      _ = U := one_mul _
  apply linear_meets hp hw hA hB hD hsepA hsepB
  · intro i hi
    exact (hm i hi).trans (by omega)
  · intro i hi
    exact (abs_add_le _ _).trans ((add_le_add (hvalues i hi).1 (hm i hi)).trans (by omega))

/-- Turn the per-cell execution postcondition into an ordinary segment
specification, without treating arbitrary function evaluation as a machine op. -/
theorem linear_output_segment {μ μ' : ℕ → ℤ} {srcA srcB dst n : ℕ}
    {c : ℤ} {as bs : List ℤ} (hA : Seg μ srcA as) (hB : Seg μ srcB bs)
    (hlenA : as.length = n) (hlenB : bs.length = n)
    (hout : ∀ i < n, μ' (dst + i) = μ (srcA + i) + c * μ (srcB + i)) :
    Seg μ' dst (List.zipWith (fun a b => a + c * b) as bs) := by
  intro i hi
  have hin : i < n := by simpa only [List.length_zipWith, hlenA, hlenB, min_self] using hi
  rw [List.getElem_zipWith, hout i hin, hA i (by omega), hB i (by omega)]

end ThreeSum.LightArray
