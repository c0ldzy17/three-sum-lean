import Submission.ThreeSum.TernaryCoverRegularity
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryCoverOutputCap
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

abbrev outputFiber (α π : DigitType) (q : TritWord L) := {e : LocalEdge L α π // output e = q}

def choiceCode {α π : DigitType} {q : TritWord L} (e : outputFiber α π q) :
    (i : Fin L) → Fin ((q i).val+1) := fun i =>
  ⟨(left e.val i).val, by
    have hs := (edge_data e.val).2.2.2 i
    rw [e.property] at hs
    omega⟩

theorem choiceCode_injective (α π : DigitType) (q : TritWord L) :
    Function.Injective (choiceCode (α := α) (π := π) (q := q)) := by
  intro e f h
  have hl : left e.val = left f.val := by
    funext i
    apply Fin.ext
    exact congrArg (fun z : Fin ((q i).val+1) => z.val) (congrFun h i)
  have hr : right e.val = right f.val := by
    funext i
    apply Fin.ext
    have hs := (edge_data e.val).2.2.2 i
    have ht := (edge_data f.val).2.2.2 i
    rw [e.property] at hs
    rw [f.property] at ht
    rw [hl] at hs
    omega
  apply Subtype.ext
  exact endpoint_injective α π (Prod.ext hl hr)

/-- Fixed-output choices are bounded before any endpoint-type restrictions. -/
theorem outputFiber_card_le_product (α π : DigitType) (q : TritWord L) :
    Fintype.card (outputFiber α π q) ≤ ∏ i, ((q i).val+1) := by
  have h := Fintype.card_le_of_injective (choiceCode (α := α) (π := π) (q := q))
    (choiceCode_injective α π q)
  simpa [Fintype.card_pi] using h

theorem digit_product (q : TritWord L) :
    (∏ i, ((q i).val+1)) = 2^(digitCount q 1) * 3^(digitCount q 2) := by
  have h := prod_fiberwise (univ : Finset (Fin L)) q (fun i => (q i).val+1)
  have hf (d : Fin 3) :
      (∏ i ∈ univ.filter (fun i => q i = d), ((q i).val+1)) =
        (d.val+1)^(digitCount q d) := by
    calc
      _ = ∏ _i ∈ univ.filter (fun i => q i = d), (d.val+1) := by
        apply prod_congr rfl
        intro i hi
        rw [(mem_filter.mp hi).2]
      _ = _ := by rw [prod_const, card_filter]; rfl
  rw [← h]
  simp_rw [hf]
  simp [Fin.prod_univ_three]

/-- The output partition cap is 2^π₁3^π₂ for every genuine output type. -/
theorem outputFiber_card_le (α π : DigitType) (q : TritWord L) (hq : HasType q π) :
    Fintype.card (outputFiber α π q) ≤ 2^(π 1) * 3^(π 2) := by
  have h := outputFiber_card_le_product α π q
  rw [digit_product, hq 1, hq 2] at h
  exact h

theorem edges_card_le (α π : DigitType) :
    Fintype.card (LocalEdge L α π) ≤ (vertices L π).card * (2^(π 1)*3^(π 2)) := by
  classical
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (LocalEdge L α π)))
    (t := vertices L π) (f := output)
    (fun e _ => mem_filter.mpr ⟨mem_univ _, (edge_data e).2.2.1⟩)
  have hf (q : TritWord L) (hq : q ∈ vertices L π) :
      (univ.filter (fun e : LocalEdge L α π => output e = q)).card ≤ 2^(π 1)*3^(π 2) := by
    rw [← Fintype.card_subtype]
    exact outputFiber_card_le α π q ((mem_filter.mp hq).2)
  calc
    _ = ∑ q ∈ vertices L π, (univ.filter (fun e : LocalEdge L α π => output e = q)).card :=
      by simpa only [card_univ] using h
    _ ≤ ∑ _q ∈ vertices L π, (2^(π 1)*3^(π 2)) := sum_le_sum (fun q hq => hf q hq)
    _ = _ := by simp

/-- The prime-size inequality alone now pays all source fibers. -/
theorem source_degree_cap {α π : DigitType} {a : TritWord L} (ha : HasType a α)
    (P : ℕ) (hP : (vertices L π).card * (2^(π 1)*3^(π 2)) ≤ P^2) :
    Fintype.card (TernaryCoverRegularity.sourceFiber α π a) ≤ P :=
  TernaryCoverRegularity.source_degree_le_prime ha P ((edges_card_le α π).trans hP)

end ThreeSum.TernaryCoverOutputCap
