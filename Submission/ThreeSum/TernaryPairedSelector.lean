import Mathlib.Tactic

/-! Simultaneous exact normalized selection. A zero upper normalizer is
handled using nonnegativity, rather than dividing by zero or assuming the
potential is positive. The score uses only rational arithmetic. -/

namespace ThreeSum.TernaryPairedSelector
open Finset
open scoped BigOperators

variable {Ω : Type*} [DecidableEq Ω]

def score (f : Fin 3 → Ω → ℚ) (normalizer : Fin 3 → ℚ) (seed : Ω) : ℚ :=
  ∑ i, if normalizer i = 0 then 0 else f i seed / normalizer i

theorem exists_three_objectives (S : Finset Ω) (hS : S.Nonempty)
    (f : Fin 3 → Ω → ℚ) (normalizer : Fin 3 → ℚ)
    (hf : ∀ i seed, 0 ≤ f i seed) (hN : ∀ i, 0 ≤ normalizer i)
    (havg : ∀ i, (∑ seed ∈ S, f i seed) ≤ S.card*normalizer i) :
    ∃ seed ∈ S, ∀ i, f i seed ≤ 3*normalizer i := by
  let term := fun i seed => if normalizer i = 0 then 0 else f i seed / normalizer i
  have ht0 (i : Fin 3) (seed : Ω) : 0 ≤ term i seed := by
    dsimp [term]
    split_ifs
    · exact le_rfl
    · exact div_nonneg (hf i seed) (hN i)
  have hsum (i : Fin 3) : (∑ seed ∈ S, term i seed) ≤ S.card := by
    by_cases hn : normalizer i = 0
    · simp [term,hn]
    · have hp : 0 < normalizer i := lt_of_le_of_ne (hN i) (Ne.symm hn)
      simpa [term,hn,← sum_div] using (div_le_iff₀ hp).mpr (havg i)
  have hscore : (∑ seed ∈ S, score f normalizer seed) ≤ ∑ _seed ∈ S, (3 : ℚ) := by
    unfold score
    rw [sum_comm]
    calc
      _ ≤ ∑ _i : Fin 3, (S.card : ℚ) := sum_le_sum fun i _ => hsum i
      _ = _ := by simp; ring
  obtain ⟨seed,hseed,hs⟩ := exists_le_of_sum_le hS hscore
  refine ⟨seed,hseed, ?_⟩
  intro i
  by_cases hn : normalizer i = 0
  · have hle : f i seed ≤ ∑ seed ∈ S, f i seed :=
      single_le_sum (fun a ha => hf i a) hseed
    have hh := havg i
    simp only [hn,mul_zero] at hh ⊢
    exact hle.trans hh
  · have hp : 0 < normalizer i := lt_of_le_of_ne (hN i) (Ne.symm hn)
    have ht : term i seed ≤ score f normalizer seed :=
      single_le_sum (fun j hj => ht0 j seed) (mem_univ i)
    have hh : f i seed / normalizer i ≤ 3 := by
      simpa [term,hn] using ht.trans hs
    exact (div_le_iff₀ hp).mp hh

/-- The exact integer test used by the actual selector. Its three expected
contractions each carry the factor three from conditioning on admissibility;
simultaneous selection therefore gives the paid factor nine. -/
theorem exists_cross_multiplied (S : Finset Ω) (hS : S.Nonempty)
    (f : Fin 3 → Ω → ℕ) (numerator denominator : Fin 3 → ℕ)
    (hd : ∀ i, 0 < denominator i)
    (havg : ∀ i, denominator i*(∑ seed ∈ S, f i seed) ≤ 3*S.card*numerator i) :
    ∃ seed ∈ S, ∀ i, denominator i*f i seed ≤ 9*numerator i := by
  have hden (i : Fin 3) : (0 : ℚ) < denominator i := by exact_mod_cast hd i
  obtain ⟨seed,hseed,hscore⟩ := exists_three_objectives S hS
    (fun i seed => (f i seed : ℚ))
    (fun i => 3*(numerator i : ℚ)/(denominator i : ℚ))
    (by intro i seed; positivity) (by intro i; positivity) (by
      intro i
      have hh : (denominator i : ℚ)*(∑ seed ∈ S, (f i seed : ℚ)) ≤
          3*(S.card : ℚ)*(numerator i : ℚ) := by exact_mod_cast havg i
      have hh' : (∑ seed ∈ S, (f i seed : ℚ)) ≤
          3*(S.card : ℚ)*(numerator i : ℚ)/(denominator i : ℚ) :=
        (le_div_iff₀ (hden i)).mpr (by nlinarith [hh])
      convert hh' using 1 <;> ring)
  refine ⟨seed,hseed, ?_⟩
  intro i
  have hh := hscore i
  have he : (3 : ℚ)*(3*(numerator i : ℚ)/(denominator i : ℚ)) =
      9*(numerator i : ℚ)/(denominator i : ℚ) := by ring
  rw [he] at hh
  have hmul := (le_div_iff₀ (hden i)).mp hh
  have hm : (denominator i : ℚ)*(f i seed : ℚ) ≤ 9*(numerator i : ℚ) := by nlinarith
  exact_mod_cast hm

end ThreeSum.TernaryPairedSelector
