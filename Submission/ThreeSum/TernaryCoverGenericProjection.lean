import Submission.ThreeSum.TernaryProjectionCells
import Submission.ThreeSum.TernaryCoverLocal
import Mathlib.Tactic

set_option maxHeartbeats 0
noncomputable section
namespace ThreeSum.TernaryCoverGenericProjection
open Finset TernaryJointType TernaryCoverLocal

variable {K : Type*} [Field K]

/-- A generic projection identifies the original admissible digit pair. -/
theorem generic_cell_unique {a b : K}
    (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : K) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b)
    (x y u v : Fin 3) (hxy : x.val+y.val ≤ 2) (huv : u.val+v.val ≤ 2)
    (h : a*(x.val : K)+b*(y.val : K) = a*(u.val : K)+b*(v.val : K)) :
    x = u ∧ y = v := by
  fin_cases x <;> fin_cases y <;> fin_cases u <;> fin_cases v <;> norm_num at hxy
  all_goals norm_num at huv
  all_goals norm_num at h
  all_goals norm_num
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

variable {L p : ℕ}

def mixedFiber (α π : DigitType) (a b : ZMod p) (q : Fin L → ZMod p) :
    Finset (LocalEdge L α π) :=
  univ.filter fun e => ∀ i, a*fieldLeft (p := p) e i+b*fieldRight e i = q i

/-- Generic full-word projection fibers contain at most one genuine edge. -/
theorem mixedFiber_generic_card_le_one [Fact p.Prime] (α π : DigitType)
    {a b : ZMod p} (ha : a ≠ 0) (hb : b ≠ 0) (h2 : (2 : ZMod p) ≠ 0)
    (hsum : a+b ≠ 0) (heq : a ≠ b) (hhalf : 2*a ≠ b) (hdouble : a ≠ 2*b)
    (q : Fin L → ZMod p) : (mixedFiber α π a b q).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro e he f hf
  have hpair (i : Fin L) : left e i = left f i ∧ right e i = right f i := by
    have h := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
    apply generic_cell_unique ha hb h2 hsum heq hhalf hdouble _ _ _ _ ?_ ?_ h
    · have hs := (edge_data e).2.2.2 i; have hq := (output e i).isLt; omega
    · have hs := (edge_data f).2.2.2 i; have hq := (output f i).isLt; omega
  apply endpoint_injective α π
  exact Prod.ext (funext fun i => (hpair i).1) (funext fun i => (hpair i).2)

end ThreeSum.TernaryCoverGenericProjection
