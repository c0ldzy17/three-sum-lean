import Submission.ThreeSum.HashFamily
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.FieldTheory.Finite.GaloisField

/-! An explicit extension-field seed menu on the ORIGINAL coefficient vectors.
The seed space is `E × E`, with multiplicity retained.  This module proves
its finite counting properties; it does not claim a RAM implementation of
extension-field construction. -/

noncomputable section
namespace ThreeSum.TernaryOriginalRowMenu

open Finset
open Polynomial
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
  [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]

def vectorPoly (Λ : ℕ) : (Fin Λ → K) →ₗ[K] E[X] :=
  ((Polynomial.ofFn Λ).restrictScalars K).comp
    (LinearMap.pi fun i => (Algebra.linearMap K E).comp (LinearMap.proj i))

theorem vectorPoly_injective (Λ : ℕ) : Function.Injective (vectorPoly (K := K) (E := E) Λ) := by
  intro v w h
  have he := Polynomial.injective_ofFn Λ h
  funext i
  exact (algebraMap K E).injective (congrFun he i)

theorem vectorPoly_natDegree_le (Λ : ℕ) (v : Fin Λ → K) :
    (vectorPoly (E := E) Λ v).natDegree ≤ Λ - 1 := by
  by_cases h : Λ = 0
  · subst Λ
    simp [vectorPoly]
  · have hh := Polynomial.ofFn_natDegree_lt (R := E) (by omega : 1 ≤ Λ)
      (fun i => algebraMap K E (v i))
    exact Nat.le_pred_of_lt hh

def evalVector (Λ : ℕ) (x : E) : (Fin Λ → K) →ₗ[K] E :=
  ((Polynomial.aeval x).toLinearMap.restrictScalars K).comp (vectorPoly (E := E) Λ)

def pairing (ℓ : E →ₗ[K] K) : E →ₗ[K] Module.Dual K E :=
  LinearMap.mk₂ K (fun a y => ℓ (a*y))
    (by intro a b y; simp [add_mul])
    (by intro c a y; simp [smul_mul_assoc])
    (by intro a y z; simp [mul_add])
    (by intro c a y; simp [mul_smul_comm])

theorem pairing_injective (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0) :
    Function.Injective (pairing ℓ) := by
  apply LinearMap.ker_eq_bot.mp
  rw [LinearMap.ker_eq_bot']
  intro a ha
  by_contra hne
  apply hℓ
  ext z
  have hh := congrArg (fun f : Module.Dual K E => f (z/a)) ha
  simpa [pairing, mul_div_cancel₀, hne, mul_comm, mul_left_comm, mul_assoc] using hh

def jointMap {t : ℕ} (ℓ : E →ₗ[K] K) (v : Fin t → E) : E →ₗ[K] (Fin t → K) :=
  LinearMap.pi fun i => pairing ℓ (v i)

theorem jointMap_surjective {t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → E) (hv : LinearIndependent K v) :
    Function.Surjective (jointMap ℓ v) := by
  let B := (pairing ℓ).comp (Fintype.linearCombination K v)
  have hi : Function.Injective B := (pairing_injective ℓ hℓ).comp
    hv.fintypeLinearCombination_injective
  have hs := (LinearMap.flip_surjective_iff₁).mpr hi
  intro target
  obtain ⟨y,hy⟩ := hs (dotProductEquiv K (Fin t) target)
  refine ⟨y, ?_⟩
  funext i
  have he := congrArg (fun f : Module.Dual K (Fin t → K) => f (Pi.single i 1)) hy
  simpa [jointMap, B, pairing, Fintype.linearCombination_apply] using he

theorem good_y_fiber_card {t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → E) (hv : LinearIndependent K v) (target : Fin t → K) :
    Fintype.card K ^ t * (univ.filter fun y => jointMap ℓ v y = target).card =
      Fintype.card E := by
  simpa using HashFamily.linear_fiber_card (jointMap ℓ v)
    (jointMap_surjective ℓ hℓ v hv) target

def combination {Λ t : ℕ} (v : Fin t → Fin Λ → K) (c : Fin t → K) : E[X] :=
  vectorPoly Λ (∑ i, c i • v i)

theorem combination_ne_zero {Λ t : ℕ} (v : Fin t → Fin Λ → K)
    (hv : LinearIndependent K v) (c : Fin t → K) (hc : c ≠ 0) :
    combination (E := E) v c ≠ 0 := by
  intro hz
  have he : (∑ i, c i • v i) = 0 :=
    vectorPoly_injective Λ (hz.trans (map_zero (vectorPoly Λ)).symm)
  apply hc
  funext i
  exact Fintype.linearIndependent_iff.mp hv c he i

def badSeeds {Λ t : ℕ} (v : Fin t → Fin Λ → K) : Finset E :=
  (univ.erase (0 : Fin t → K)).biUnion fun c =>
    univ.filter fun x => (combination (E := E) v c).eval x = 0

theorem badSeeds_card_le {Λ t : ℕ} (v : Fin t → Fin Λ → K)
    (hv : LinearIndependent K v) :
    (badSeeds (E := E) v).card ≤ (Fintype.card K ^ t - 1) * (Λ - 1) := by
  have hroot (c : Fin t → K) (hc : c ∈ univ.erase 0) :
      (univ.filter fun x => (combination (E := E) v c).eval x = 0).card ≤ Λ - 1 := by
    have hn := combination_ne_zero (E := E) v hv c (mem_erase.mp hc).1
    have hh : (univ.filter fun x => (combination (E := E) v c).eval x = 0).val ⊆
        (combination (E := E) v c).roots := by
      intro x hx
      exact (Polynomial.mem_roots hn).mpr (mem_filter.mp hx).2
    exact (Polynomial.card_le_degree_of_subset_roots hh).trans
      (vectorPoly_natDegree_le Λ _)
  calc
    _ ≤ ∑ c ∈ univ.erase (0 : Fin t → K),
        (univ.filter fun x => (combination (E := E) v c).eval x = 0).card :=
      card_biUnion_le
    _ ≤ ∑ _c ∈ univ.erase (0 : Fin t → K), (Λ - 1) := sum_le_sum hroot
    _ = _ := by simp

theorem good_eval_independent {Λ t : ℕ} (v : Fin t → Fin Λ → K)
    (x : E) (hx : x ∉ badSeeds (E := E) v) :
    LinearIndependent K (fun i => evalVector Λ x (v i)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_cases hz : c = 0
  · simp [hz]
  · exfalso
    apply hx
    apply mem_biUnion.mpr
    refine ⟨c, mem_erase.mpr ⟨hz,mem_univ _⟩, mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
    have hh : evalVector Λ x (∑ j, c j • v j) = 0 := by
      simpa only [map_sum, map_smul] using hc
    change (Polynomial.aeval x) (combination (E := E) v c) = 0 at hh
    simpa only [Polynomial.aeval_def, Algebra.algebraMap_self, Polynomial.eval₂_id] using hh

def row (Λ : ℕ) (ℓ : E →ₗ[K] K) (seed : E × E) : (Fin Λ → K) →ₗ[K] K :=
  ((pairing ℓ).flip seed.2).comp (evalVector Λ seed.1)

def menuEvent {Λ t : ℕ} (ℓ : E →ₗ[K] K) (v : Fin t → Fin Λ → K)
    (target : Fin t → K) : Finset (E × E) :=
  univ.filter fun seed => ∀ i, row Λ ℓ seed (v i) = target i

theorem menuEvent_card_eq_sum {Λ t : ℕ} (ℓ : E →ₗ[K] K)
    (v : Fin t → Fin Λ → K) (target : Fin t → K) :
    (menuEvent ℓ v target).card = ∑ x : E,
      (univ.filter fun y : E => jointMap ℓ (fun i => evalVector Λ x (v i)) y = target).card := by
  simp only [menuEvent, card_eq_sum_ones, sum_filter, Fintype.sum_prod_type]
  apply sum_congr rfl
  intro x hx
  apply sum_congr rfl
  intro y hy
  congr 1
  apply propext
  exact funext_iff.symm

theorem menuEvent_card_bound {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K) :
    Fintype.card K ^ t * (menuEvent ℓ v target).card ≤
      Fintype.card E ^ 2 + Fintype.card K ^ t *
        ((Fintype.card K ^ t - 1) * (Λ - 1)) * Fintype.card E := by
  let bad := badSeeds (E := E) v
  let a := Fintype.card K ^ t
  let q := Fintype.card E
  let fiber := fun x : E =>
    (univ.filter fun y : E => jointMap ℓ (fun i => evalVector Λ x (v i)) y = target).card
  have hrow (x : E) : a * fiber x ≤ q + if x ∈ bad then a*q else 0 := by
    by_cases hb : x ∈ bad
    · simp only [if_pos hb]
      have hh : fiber x ≤ q := card_le_card (filter_subset ..)
      exact (Nat.mul_le_mul_left a hh).trans (Nat.le_add_left _ _)
    · have hc := good_y_fiber_card ℓ hℓ _ (good_eval_independent v x hb) target
      simpa only [if_neg hb, add_zero] using hc.le
  have hh : a * (menuEvent ℓ v target).card ≤ q^2 + a*bad.card*q := by
    rw [menuEvent_card_eq_sum, mul_sum]
    calc
      _ ≤ ∑ x : E, (q + if x ∈ bad then a*q else 0) := sum_le_sum fun x _ => hrow x
      _ = _ := by simp [sum_add_distrib, q]; ring
  exact hh.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right q (Nat.mul_le_mul_left a (badSeeds_card_le v hv))) _)

/-- With `|E| ≥ 8 Λ p^(2t)`, every rank-`t` prescribed event occupies
at most `9/(8 p^t)` of the literal seed menu.  All quantities are exact
natural cardinalities, so no probability oracle occurs. -/
theorem menuEvent_nine_eighths {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K)
    (hsize : 8 * Λ * Fintype.card K ^ (2*t) ≤ Fintype.card E) :
    8 * Fintype.card K ^ t * (menuEvent ℓ v target).card ≤ 9 * Fintype.card E ^ 2 := by
  let a := Fintype.card K ^ t
  let q := Fintype.card E
  have hb : (Fintype.card K ^ t - 1) * (Λ - 1) ≤ a*Λ :=
    Nat.mul_le_mul (Nat.sub_le _ _) (Nat.sub_le _ _)
  have hc := menuEvent_card_bound ℓ hℓ v hv target
  have hsize' : 8*Λ*a^2 ≤ q := by
    simpa only [a,q, mul_comm 2 t, pow_mul] using hsize
  have hc' : a * (menuEvent ℓ v target).card ≤ q^2 + a*(a*Λ)*q :=
    hc.trans (Nat.add_le_add_left
      (Nat.mul_le_mul_right q (Nat.mul_le_mul_left a hb)) _)
  have hz := Nat.mul_le_mul_right q hsize'
  change 8*a*(menuEvent ℓ v target).card ≤ 9*q^2
  nlinarith

def seedRow (Λ : ℕ) (ℓ : E →ₗ[K] K) (seed : E × E) : Fin Λ → K :=
  fun i => row Λ ℓ seed (Pi.single i 1)

theorem row_eq_dot (Λ : ℕ) (ℓ : E →ₗ[K] K) (seed : E × E) (v : Fin Λ → K) :
    row Λ ℓ seed v = ∑ i, v i * seedRow Λ ℓ seed i := by
  have he : v = ∑ i, v i • Pi.single i 1 := by ext j; simp [Pi.single_apply]
  conv_lhs => rw [he]
  simp [seedRow]

def admissible (Λ : ℕ) (ℓ : E →ₗ[K] K) (V : Submodule K (Fin Λ → K)) : Finset (E × E) :=
  univ.filter fun seed => seedRow Λ ℓ seed ∉ V

theorem proper_span_annihilator (Λ : ℕ) (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) :
    ∃ v : Fin Λ → K, v ≠ 0 ∧ ∀ w ∈ V, ∑ i, v i * w i = 0 := by
  have ha : V.dualAnnihilator ≠ ⊥ := by
    intro h
    exact hV (Submodule.dualAnnihilator_eq_bot_iff.mp h)
  obtain ⟨φ,hφ,hne⟩ := V.dualAnnihilator.ne_bot_iff.mp ha
  let v := (dotProductEquiv K (Fin Λ)).symm φ
  have he : dotProductEquiv K (Fin Λ) v = φ := LinearEquiv.apply_symm_apply _ _
  refine ⟨v, ?_, ?_⟩
  · intro hz
    apply hne
    rw [← he,hz,map_zero]
  · intro w hw
    have hh := (Submodule.mem_dualAnnihilator φ).mp hφ w hw
    rw [← he] at hh
    exact hh

theorem admissible_at_least_half (Λ : ℕ) (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤)
    (hp : 3 ≤ Fintype.card K)
    (hsize : 8*Λ*Fintype.card K ^ 2 ≤ Fintype.card E) :
    Fintype.card E ^ 2 ≤ 2*(admissible Λ ℓ V).card := by
  obtain ⟨v,hv,hann⟩ := proper_span_annihilator Λ V hV
  let bad := univ.filter fun seed : E × E => seedRow Λ ℓ seed ∈ V
  have hind : LinearIndependent K (fun _ : Fin 1 => v) := by
    simpa only [linearIndependent_unique_iff] using hv
  have hs := menuEvent_nine_eighths ℓ hℓ (fun _ : Fin 1 => v) hind 0
    (by simpa using hsize)
  have hsub : bad ⊆ menuEvent ℓ (fun _ : Fin 1 => v) 0 := by
    intro seed hseed
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    rw [row_eq_dot]
    exact hann _ (mem_filter.mp hseed).2
  have hb := Nat.mul_le_mul_left (8*Fintype.card K) (card_le_card hsub)
  simp only [pow_one] at hs
  have hpart : bad.card + (admissible Λ ℓ V).card = Fintype.card E ^ 2 := by
    have hh := card_filter_add_card_filter_not (s := (univ : Finset (E × E)))
      (p := fun seed => seedRow Λ ℓ seed ∈ V)
    simpa only [admissible, bad, card_univ, Fintype.card_prod, pow_two] using hh
  nlinarith

theorem admissible_event_bound {Λ t : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) (hp : 3 ≤ Fintype.card K)
    (v : Fin t → Fin Λ → K) (hv : LinearIndependent K v) (target : Fin t → K)
    (hsize1 : 8*Λ*Fintype.card K ^ 2 ≤ Fintype.card E)
    (hsize : 8*Λ*Fintype.card K ^ (2*t) ≤ Fintype.card E) :
    Fintype.card K ^ t * ((admissible Λ ℓ V) ∩ menuEvent ℓ v target).card ≤
      3 * (admissible Λ ℓ V).card := by
  have ha := admissible_at_least_half Λ ℓ hℓ V hV hp hsize1
  have he := menuEvent_nine_eighths ℓ hℓ v hv target hsize
  have hc := Nat.mul_le_mul_left (8*Fintype.card K ^ t)
    (card_le_card (inter_subset_right (s₁ := admissible Λ ℓ V) (s₂ := menuEvent ℓ v target)))
  nlinarith

end ThreeSum.TernaryOriginalRowMenu
