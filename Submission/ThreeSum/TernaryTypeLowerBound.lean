import Submission.ThreeSum.TernaryCoverOutputCap
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Sum
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryTypeLowerBound
open Finset TernaryJointType TernaryCoverLocal

abbrev BlockIndex (t1 t2 r : ℕ) := (Fin t1 × Fin 2) ⊕ ((Fin t2 × Fin 3) ⊕ Fin r)
abbrev BlockChoice (t1 t2 : ℕ) := (Fin t1 → Fin 2) × (Fin t2 → Fin 3)

abbrev blockWord {t1 t2 r : ℕ} (c : BlockChoice t1 t2) : BlockIndex t1 t2 r → Fin 3
  | Sum.inl (i,j) => if j = c.1 i then 1 else 0
  | Sum.inr (Sum.inl (i,j)) => if j = c.2 i then 2 else 0
  | Sum.inr (Sum.inr _) => 0

def count {I : Type*} [Fintype I] (w : I → Fin 3) (d : Fin 3) : ℕ :=
  ∑ i, if w i = d then 1 else 0

private theorem indicator_one (P : Prop) [Decidable P] :
    (if (if P then (1 : Fin 3) else 0) = 1 then 1 else 0 : ℕ) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]
private theorem indicator_two (P : Prop) [Decidable P] :
    (if (if P then (2 : Fin 3) else 0) = 2 then 1 else 0 : ℕ) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]
private theorem indicator_one_two (P : Prop) [Decidable P] :
    (if (if P then (1 : Fin 3) else 0) = 2 then 1 else 0 : ℕ) = 0 := by
  by_cases h : P <;> simp [h]
private theorem indicator_two_one (P : Prop) [Decidable P] :
    (if (if P then (2 : Fin 3) else 0) = 1 then 1 else 0 : ℕ) = 0 := by
  by_cases h : P <;> simp [h]

theorem block_count_one {t1 t2 r : ℕ} (c : BlockChoice t1 t2) :
    count (blockWord (r := r) c) 1 = t1 := by
  simp only [count, Fintype.sum_sum_type, Fintype.sum_prod_type, blockWord]
  simp_rw [indicator_one, indicator_two_one]
  simp

theorem block_count_two {t1 t2 r : ℕ} (c : BlockChoice t1 t2) :
    count (blockWord (r := r) c) 2 = t2 := by
  simp only [count, Fintype.sum_sum_type, Fintype.sum_prod_type, blockWord]
  simp_rw [indicator_two, indicator_one_two]
  simp

theorem count_total {I : Type*} [Fintype I] (w : I → Fin 3) :
    count w 0 + count w 1 + count w 2 = Fintype.card I := by
  unfold count
  rw [← sum_add_distrib, ← sum_add_distrib]
  have hi (i : I) : (if w i = 0 then 1 else 0) + (if w i = 1 then 1 else 0) +
      (if w i = 2 then 1 else 0 : ℕ) = 1 := by generalize w i = a; fin_cases a <;> decide
  simp_rw [hi]
  simp

theorem blockWord_injective {t1 t2 r : ℕ} :
    Function.Injective (blockWord (t1 := t1) (t2 := t2) (r := r)) := by
  intro c d h
  apply Prod.ext
  · funext i
    have hh := congrFun h (Sum.inl (i,c.1 i))
    by_contra hne
    simp [blockWord, hne] at hh
  · funext i
    have hh := congrFun h (Sum.inr (Sum.inl (i,c.2 i)))
    by_contra hne
    simp [blockWord, hne] at hh

/-- Two-way choices for 1-digits and three-way choices for 2-digits give
an explicit subfamily of the required output type. -/
theorem vertices_lower_bound {L : ℕ} (π : DigitType)
    (htotal : π 0+π 1+π 2 = L) (hspace : 2*(π 1)+3*(π 2) ≤ L) :
    2^(π 1)*3^(π 2) ≤ (vertices L π).card := by
  classical
  let r := L-(2*(π 1)+3*(π 2))
  have hcard : Fintype.card (Fin L) = Fintype.card (BlockIndex (π 1) (π 2) r) := by
    simp [BlockIndex, r]
    omega
  let e : Fin L ≃ BlockIndex (π 1) (π 2) r := Fintype.equivOfCardEq hcard
  let f (c : BlockChoice (π 1) (π 2)) : TritWord L := blockWord c ∘ e
  have hcount (c : BlockChoice (π 1) (π 2)) (d : Fin 3) :
      digitCount (f c) d = count (blockWord (r := r) c) d :=
    Equiv.sum_comp e (fun i => if blockWord c i = d then 1 else 0)
  have hf (c : BlockChoice (π 1) (π 2)) : HasType (f c) π := by
    have h1 : digitCount (f c) 1 = π 1 := by rw [hcount, block_count_one]
    have h2 : digitCount (f c) 2 = π 2 := by rw [hcount, block_count_two]
    have hz := count_total (f c)
    change digitCount (f c) 0+digitCount (f c) 1+digitCount (f c) 2 = Fintype.card (Fin L) at hz
    rw [h1,h2,Fintype.card_fin] at hz
    have h0 : digitCount (f c) 0 = π 0 := by omega
    intro d
    fin_cases d
    · change digitCount (f c) 0 = π 0
      exact h0
    · change digitCount (f c) 1 = π 1
      exact h1
    · change digitCount (f c) 2 = π 2
      exact h2
  let g : BlockChoice (π 1) (π 2) → {q // q ∈ vertices L π} :=
    fun c => ⟨f c, mem_filter.mpr ⟨mem_univ _, hf c⟩⟩
  have hg : Function.Injective g := by
    intro c d h
    apply blockWord_injective (r := r)
    funext i
    have hh := congrFun (congrArg Subtype.val h) (e.symm i)
    simpa [g,f] using hh
  have h := Fintype.card_le_of_injective g hg
  simpa [BlockChoice, Fintype.card_fun] using h

/-- Consequently the basic prime-size guard also pays every output partition. -/
theorem partition_cap_le_prime {L : ℕ} (π : DigitType)
    (htotal : π 0+π 1+π 2 = L) (hspace : 2*(π 1)+3*(π 2) ≤ L)
    (P : ℕ) (hP : (vertices L π).card*(2^(π 1)*3^(π 2)) ≤ P^2) :
    2^(π 1)*3^(π 2) ≤ P := by
  have h := vertices_lower_bound π htotal hspace
  nlinarith

end ThreeSum.TernaryTypeLowerBound
