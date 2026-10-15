import Submission.ThreeSum.TernaryJointType
import Mathlib.Tactic

set_option maxRecDepth 10000
set_option maxHeartbeats 0

namespace ThreeSum.TernaryProjectionCells
variable {K : Type*} [Field K]

/-- Ordered images of (0,0),(0,1),(1,0),(0,2),(1,1),(2,0). -/
def projectedCell (a b : K) : Fin 6 → K := ![0,b,a,2*b,a+b,2*a]

theorem generic_projection_injective {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b) :
    Function.Injective (projectedCell a b) := by
  intro i j h
  fin_cases i <;> fin_cases j <;> norm_num [projectedCell] at h ⊢
  all_goals try simp only [h2, or_false, false_or] at h
  all_goals first
    | (apply ha; linear_combination h)
    | (apply ha; linear_combination -h)
    | (apply hb; linear_combination h)
    | (apply hb; linear_combination -h)
    | (apply hsum; linear_combination h)
    | (apply hsum; linear_combination -h)
    | (apply heq; linear_combination h)
    | (apply heq; linear_combination -h)
    | (apply hhalf; linear_combination h)
    | (apply hhalf; linear_combination -h)
    | (apply hdouble; linear_combination h)
    | (apply hdouble; linear_combination -h)

theorem collision_classification {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    {i j : Fin 6} (hij : i ≠ j) (h : projectedCell a b i = projectedCell a b j) :
    a+b = 0 ∨ a = b ∨ 2*a = b ∨ a = 2*b := by
  by_contra hn
  push_neg at hn
  exact hij (generic_projection_injective ha hb h2 hn.1 hn.2.1 hn.2.2.1 hn.2.2.2 h)

end ThreeSum.TernaryProjectionCells
