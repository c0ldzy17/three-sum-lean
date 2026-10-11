import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.Dual
import Mathlib.Data.Fin.VecNotation
import Mathlib.GroupTheory.Index
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Push
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# The actual one-hot hash family

This file develops the dependence classification of the binary one-hot hash
vectors used in the local cover. Hash weights are independent field elements
at coordinate/symbol pairs. The independence statements concern this concrete
family, not an assumed random oracle.
-/

namespace ThreeSum.HashFamily

open scoped BigOperators

variable {α K : Type*}

def oneHot [Zero K] [One K] (s : α → Bool) : α × Bool → K :=
  fun p => if s p.1 = p.2 then 1 else 0

theorem exists_coordinate_ne {s t : α → Bool} (hst : s ≠ t) :
    ∃ i, s i ≠ t i := by
  classical
  by_contra h
  push Not at h
  exact hst (funext h)

section Relations

variable [Ring K]

/-- Two distinct one-hot words have no nontrivial linear relation. -/
theorem two_relation {s t : α → Bool} (hst : s ≠ t) {a b : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p = 0) : a = 0 ∧ b = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have ha := h (i, s i)
  have hb := h (i, t i)
  simpa [oneHot, hi, Ne.symm hi] using And.intro ha hb

/-- Any three pairwise distinct binary one-hot words are independent.
At a coordinate separating the first two words, the third agrees with one
of them, leaving one coefficient isolated. -/
theorem three_relation {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) {a b c : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p + c * oneHot u p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  obtain ⟨i, hi⟩ := exists_coordinate_ne hst
  have hu : u i = s i ∨ u i = t i := by
    cases hs : s i <;> cases ht : t i <;> cases hu : u i <;> simp_all
  rcases hu with hu | hu
  · have hb : b = 0 := by
      simpa [oneHot, hi, Ne.symm hi, hu] using h (i, t i)
    have hac : a = 0 ∧ c = 0 := two_relation hsu fun p => by simpa [hb] using h p
    exact ⟨hac.1, hb, hac.2⟩
  · have ha : a = 0 := by
      simpa [oneHot, hi, Ne.symm hi, hu] using h (i, s i)
    have hbc : b = 0 ∧ c = 0 := two_relation htu fun p => by simpa [ha] using h p
    exact ⟨ha, hbc.1, hbc.2⟩

/-- If the equality masks of two edges differ, one coordinate has a 3+1
pattern among their four endpoint words. With four distinct endpoints this
forces full independence. The only possible no-shared-endpoint dependence
therefore has an identical output equality mask. -/
theorem four_relation_of_mask_ne {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) {a b c d : K}
    (h : ∀ p, a * oneHot s p + b * oneHot t p + c * oneHot u p + d * oneHot v p = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 := by
  have hz : a = 0 ∨ b = 0 ∨ c = 0 ∨ d = 0 := by
    obtain ⟨i, hi⟩ := hm
    have hf := h (i, false)
    have ht := h (i, true)
    cases hs : s i <;> cases hti : t i <;> cases hu : u i <;> cases hv : v i <;>
      simp_all [oneHot]
  rcases hz with ha | hb | hc | hd
  · have hr := three_relation htu htv huv (a := b) (b := c) (c := d)
      (fun p => by simpa [ha] using h p)
    exact ⟨ha, hr.1, hr.2.1, hr.2.2⟩
  · have hr := three_relation hsu hsv huv (a := a) (b := c) (c := d)
      (fun p => by simpa [hb] using h p)
    exact ⟨hr.1, hb, hr.2.1, hr.2.2⟩
  · have hr := three_relation hst hsv htv (a := a) (b := b) (c := d)
      (fun p => by simpa [hc] using h p)
    exact ⟨hr.1, hr.2.1, hc, hr.2.2⟩
  · have hr := three_relation hst hsu htu (a := a) (b := b) (c := c)
      (fun p => by simpa [hd] using h p)
    exact ⟨hr.1, hr.2.1, hr.2.2, hd⟩

end Relations

section LinearIndependence

variable [Field K]

theorem oneHot_two_independent {s t : α → Bool} (hst : s ≠ t) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := two_relation hst (a := g 0) (b := g 1) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ] using hp)
  fin_cases i <;> simp_all

theorem oneHot_three_independent {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t, oneHot u] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := three_relation hst hsu htu (a := g 0) (b := g 1) (c := g 2) (fun p => by
    have hp := congrFun hg p
    simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all

theorem oneHot_four_independent {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) :
    LinearIndependent K ![oneHot (K := K) s, oneHot t, oneHot u, oneHot v] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have hr := four_relation_of_mask_ne hst hsu hsv htu htv huv hm
    (a := g 0) (b := g 1) (c := g 2) (d := g 3) (fun p => by
      have hp := congrFun hg p
      simpa [Fin.sum_univ_succ, add_assoc] using hp)
  fin_cases i <;> simp_all

end LinearIndependence

section UniformFibers

variable {σ ι : Type*} [Fintype σ] [Fintype ι] [Field K]

/-- The linear map associated with any concrete list of hash coefficient
vectors. This is the ordinary row-by-weight product. -/
noncomputable def hashMap (v : ι → σ → K) : (σ → K) →ₗ[K] (ι → K) := by
  classical
  exact LinearMap.pi (fun i => dotProductEquiv K σ (v i))

@[simp] theorem hashMap_apply (v : ι → σ → K) (w : σ → K) (i : ι) :
    hashMap v w i = ∑ x, v i x * w x := by
  classical
  rfl

/-- Independent concrete coefficient rows give a surjective hash map.
This supplies every target vector; it is not an assumed uniformity property. -/
theorem hashMap_surjective {v : ι → σ → K} (hv : LinearIndependent K v) :
    Function.Surjective (hashMap v) := by
  classical
  let f := Fintype.linearCombination K v
  let B : (ι → K) →ₗ[K] (σ → K) →ₗ[K] K :=
    (dotProductEquiv K σ).toLinearMap.comp f
  have hi : Function.Injective B :=
    (dotProductEquiv K σ).injective.comp hv.fintypeLinearCombination_injective
  have hs : Function.Surjective B.flip := (LinearMap.flip_surjective_iff₁).mpr hi
  intro target
  obtain ⟨w, hw⟩ := hs (dotProductEquiv K ι target)
  refine ⟨w, ?_⟩
  funext i
  have he := congrArg (fun φ : Module.Dual K (ι → K) => φ (Pi.single i 1)) hw
  change dotProduct (v i) w = target i
  simpa [B, f, Fintype.linearCombination_apply] using he

/-- Equal-sized fibers of a surjective linear map, with the full sample
space cardinality on the right. This exact integer equality is the finite
uniform-distribution statement used in the hash moments. -/
theorem linear_fiber_card {V W : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [Fintype V] [Fintype W] [DecidableEq W]
    (f : V →ₗ[K] W) (hf : Function.Surjective f) (target : W) :
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
      Fintype.card V := by
  classical
  have heq : ∀ y : W, (Finset.univ.filter (fun x => f x = y)).card =
      (Finset.univ.filter (fun x => f x = target)).card := by
    intro y
    exact AddMonoidHom.card_fiber_eq_of_mem_range f (hf y) (hf target)
  calc
    Fintype.card W * (Finset.univ.filter (fun x => f x = target)).card =
        ∑ y : W, (Finset.univ.filter (fun x => f x = y)).card := by
      simp [heq]
    _ = ∑ y : W, ∑ x : V, if f x = y then (1 : ℕ) else 0 := by
      simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
    _ = ∑ x : V, ∑ y : W, if f x = y then (1 : ℕ) else 0 := Finset.sum_comm
    _ = Fintype.card V := by simp

/-- The exact joint-output count for independent hash coefficient rows. -/
theorem hash_fiber_card [Fintype K] [DecidableEq K] [DecidableEq σ] [DecidableEq ι]
    {v : ι → σ → K}
    (hv : LinearIndependent K v) (target : ι → K) :
    Fintype.card K ^ Fintype.card ι *
        (Finset.univ.filter (fun w : σ → K => hashMap v w = target)).card =
      Fintype.card K ^ Fintype.card σ := by
  classical
  simpa using linear_fiber_card (hashMap v) (hashMap_surjective hv) target

end UniformFibers

section ActualHashes

variable {ι : Type*} [Fintype α] [Field K]

/-- One independent weight for each coordinate/symbol pair. -/
def hashValue (w : α × Bool → K) (s : α → Bool) : K :=
  ∑ i, w (i, s i)

theorem hashValue_eq_dotProduct (w : α × Bool → K) (s : α → Bool) :
    hashValue w s = ∑ p, oneHot (K := K) s p * w p := by
  classical
  simp [hashValue, oneHot, Fintype.sum_prod_type]

theorem hashValue_family (v : ι → α → Bool) (w : α × Bool → K)
    [Fintype ι] :
    (fun i => hashValue w (v i)) = hashMap (fun i => oneHot (K := K) (v i)) w := by
  funext i
  exact hashValue_eq_dotProduct w (v i)

end ActualHashes

section WordEvents

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

/-- Probability of an event under uniform enumeration of the finite space. -/
noncomputable def eventProbability {Ω : Type*} [Fintype Ω] (A : Finset Ω) : ℝ :=
  (A.card : ℝ) / Fintype.card Ω

/-- The simultaneous prescribed hashes of a concrete word tuple. -/
def wordEvent {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K) :
    Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => ∀ i, hashValue w (words i) = target i)

theorem wordEvent_eq_linear_fiber {r : ℕ}
    (words : Fin r → α → Bool) (target : Fin r → K) :
    wordEvent words target =
      Finset.univ.filter (fun w => hashMap (fun i => oneHot (K := K) (words i)) w = target) := by
  ext w
  simp only [wordEvent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hashValue_family]
  exact funext_iff.symm

/-- Exact uniform joint count, instantiated with the actual one-hot family. -/
theorem wordEvent_card {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => oneHot (K := K) (words i))) :
    Fintype.card K ^ r * (wordEvent words target).card =
      Fintype.card (α × Bool → K) := by
  rw [wordEvent_eq_linear_fiber]
  simpa using hash_fiber_card hwords target

theorem wordEvent_probability {r : ℕ} (words : Fin r → α → Bool) (target : Fin r → K)
    (hwords : LinearIndependent K (fun i => oneHot (K := K) (words i))) :
    eventProbability (wordEvent words target) = 1 / (Fintype.card K : ℝ) ^ r := by
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have ho : (0 : ℝ) < Fintype.card (α × Bool → K) := by exact_mod_cast Fintype.card_pos
  have hc : (Fintype.card K : ℝ) ^ r * (wordEvent words target).card =
      Fintype.card (α × Bool → K) := by exact_mod_cast wordEvent_card words target hwords
  unfold eventProbability
  apply (div_eq_div_iff (ne_of_gt ho) (ne_of_gt (pow_pos hp _))).mpr
  simpa only [one_mul, mul_comm] using hc

def pairEvent (s t : α → Bool) (a b : K) : Finset (α × Bool → K) :=
  Finset.univ.filter (fun w => hashValue w s = a ∧ hashValue w t = b)

theorem pairEvent_eq (s t : α → Bool) (a b : K) :
    pairEvent s t a b = wordEvent ![s, t] ![a, b] := by
  ext w
  simp [pairEvent, wordEvent, Fin.forall_fin_succ]

/-- A pair of distinct actual endpoint words hashes uniformly, including
when the two requested target residues are equal. -/
theorem pairEvent_probability {s t : α → Bool} (hst : s ≠ t) (a b : K) :
    eventProbability (pairEvent s t a b) = 1 / (Fintype.card K : ℝ) ^ 2 := by
  rw [pairEvent_eq]
  apply wordEvent_probability
  convert oneHot_two_independent (K := K) hst using 1
  funext i
  fin_cases i <;> rfl

theorem pairEvent_card {s t : α → Bool} (hst : s ≠ t) (a b : K) :
    Fintype.card K ^ 2 * (pairEvent s t a b).card =
      Fintype.card (α × Bool → K) := by
  rw [pairEvent_eq]
  apply wordEvent_card
  convert oneHot_two_independent (K := K) hst using 1
  funext i
  fin_cases i <;> rfl

theorem tripleEvent_card {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    Fintype.card K ^ 3 * (wordEvent ![s, t, u] ![a, b, c]).card =
      Fintype.card (α × Bool → K) := by
  apply wordEvent_card
  convert oneHot_three_independent (K := K) hst hsu htu using 1
  funext i
  fin_cases i <;> rfl

/-- Two distinct edges always impose at least three independent hash tests
when the left and right vertex classes are disjoint. -/
theorem jointPair_card_le_cube {s t u v : α → Bool}
    (hst : s ≠ t) (hsv : s ≠ v) (htu : t ≠ u) (huv : u ≠ v)
    (hpair : (s, t) ≠ (u, v)) (a b : K) :
    Fintype.card K ^ 3 * (pairEvent s t a b ∩ pairEvent u v a b).card ≤
      Fintype.card (α × Bool → K) := by
  by_cases hsu : s = u
  · have htv : t ≠ v := by
      intro htv
      exact hpair (Prod.ext hsu htv)
    have hsub : pairEvent s t a b ∩ pairEvent u v a b ⊆
        wordEvent ![s, t, v] ![a, b, b] := by
      intro w hw
      simpa [wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).2)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (tripleEvent_card hst hsv htv a b b)
  · have hsub : pairEvent s t a b ∩ pairEvent u v a b ⊆
        wordEvent ![s, t, u] ![a, b, a] := by
      intro w hw
      simpa [wordEvent, Fin.forall_fin_succ] using
        And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).1
          (And.intro ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).1).2).2
            ((Finset.mem_filter.mp (Finset.mem_inter.mp hw).2).2).1)
    exact (Nat.mul_le_mul_left _ (Finset.card_le_card hsub)).trans_eq
      (tripleEvent_card hst hsu htu a b a)

theorem jointPair_card_four {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b : K) :
    Fintype.card K ^ 4 * (pairEvent s t a b ∩ pairEvent u v a b).card =
      Fintype.card (α × Bool → K) := by
  have he : pairEvent s t a b ∩ pairEvent u v a b =
      wordEvent ![s, t, u, v] ![a, b, a, b] := by
    ext w
    simp [pairEvent, wordEvent, Fin.forall_fin_succ, and_assoc]
  rw [he]
  apply wordEvent_card
  convert oneHot_four_independent (K := K) hst hsu hsv htu htv huv hm using 1
  funext i
  fin_cases i <;> rfl

theorem tripleEvent_probability {s t u : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (htu : t ≠ u) (a b c : K) :
    eventProbability (wordEvent ![s, t, u] ![a, b, c]) =
      1 / (Fintype.card K : ℝ) ^ 3 := by
  apply wordEvent_probability
  convert oneHot_three_independent (K := K) hst hsu htu using 1
  funext i
  fin_cases i <;> rfl

theorem quadrupleEvent_probability {s t u v : α → Bool}
    (hst : s ≠ t) (hsu : s ≠ u) (hsv : s ≠ v)
    (htu : t ≠ u) (htv : t ≠ v) (huv : u ≠ v)
    (hm : ∃ i, (s i == t i) ≠ (u i == v i)) (a b c d : K) :
    eventProbability (wordEvent ![s, t, u, v] ![a, b, c, d]) =
      1 / (Fintype.card K : ℝ) ^ 4 := by
  apply wordEvent_probability
  convert oneHot_four_independent (K := K) hst hsu hsv htu htv huv hm using 1
  funext i
  fin_cases i <;> rfl

end WordEvents

section IncidenceCounting

variable {Ω E : Type*} [Fintype Ω] [Fintype E] [DecidableEq Ω]

/-- Number of represented edges in one weight assignment. -/
def incidenceCount (events : E → Finset Ω) (w : Ω) : ℕ :=
  (Finset.univ.filter (fun e => w ∈ events e)).card

theorem incidenceCount_eq_sum (events : E → Finset Ω) (w : Ω) :
    incidenceCount events w = ∑ e, if w ∈ events e then (1 : ℕ) else 0 := by
  unfold incidenceCount
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]

theorem sum_incidenceCount (events : E → Finset Ω) :
    (∑ w, incidenceCount events w) = ∑ e, (events e).card := by
  simp only [incidenceCount_eq_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e he
  simp

theorem incidenceCount_mono {events events' : E → Finset Ω}
    (h : ∀ e, events e ⊆ events' e) (w : Ω) :
    incidenceCount events w ≤ incidenceCount events' w := by
  apply Finset.card_le_card
  intro e he
  exact Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, h e (Finset.mem_filter.mp he).2⟩

/-- Exact second-moment expansion over edge pairs, with no independence
assumption and no probabilistic approximation. -/
theorem sum_incidenceCount_sq (events : E → Finset Ω) :
    (∑ w, incidenceCount events w ^ 2) =
      ∑ e, ∑ f, (events e ∩ events f).card := by
  calc
    (∑ w, incidenceCount events w ^ 2) =
        ∑ w, ∑ e, ∑ f,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [incidenceCount_eq_sum, pow_two, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f hf
      by_cases he : w ∈ events e <;> by_cases hf : w ∈ events f <;> simp [he, hf]
    _ = ∑ e, ∑ f, ∑ w,
          if w ∈ events e ∧ w ∈ events f then (1 : ℕ) else 0 := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.sum_comm
    _ = ∑ e, ∑ f, (events e ∩ events f).card := by
      apply Finset.sum_congr rfl
      intro e he
      apply Finset.sum_congr rfl
      intro f hf
      simp [← Finset.mem_inter]

end IncidenceCounting

section GraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

def outputMask (left right : E → α → Bool) (e : E) : α → Bool :=
  fun i => left e i == right e i

def badPartners (left right : E → α → Bool) (e : E) : Finset E :=
  Finset.univ.filter (fun f => left e = left f ∨ right e = right f ∨
    outputMask left right e = outputMask left right f)

theorem badPartners_card_le (left right : E → α → Bool) (e : E) (Delta G : ℕ)
    (hL : (Finset.univ.filter (fun f => left e = left f)).card ≤ Delta)
    (hR : (Finset.univ.filter (fun f => right e = right f)).card ≤ Delta)
    (hG : (Finset.univ.filter (fun f =>
      outputMask left right e = outputMask left right f)).card ≤ G) :
    (badPartners left right e).card ≤ 2 * Delta + G := by
  have he : badPartners left right e =
      ((Finset.univ.filter (fun f => left e = left f)) ∪
        (Finset.univ.filter (fun f => right e = right f))) ∪
          (Finset.univ.filter (fun f => outputMask left right e = outputMask left right f)) := by
    ext f
    simp [badPartners, or_assoc]
  rw [he]
  have hu := Finset.card_union_le
    ((Finset.univ.filter (fun f => left e = left f)) ∪
      (Finset.univ.filter (fun f => right e = right f)))
    (Finset.univ.filter (fun f => outputMask left right e = outputMask left right f))
  have hv := Finset.card_union_le (Finset.univ.filter (fun f => left e = left f))
    (Finset.univ.filter (fun f => right e = right f))
  omega

/-- The raw first moment for a concrete finite graph of one-hot endpoints. -/
theorem raw_first_moment (left right : E → α → Bool)
    (hcross : ∀ e f, left e ≠ right f) (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w) =
      Fintype.card E * Fintype.card (α × Bool → K) := by
  rw [sum_incidenceCount, Finset.mul_sum]
  simp_rw [pairEvent_card (hcross _ _) a b]
  simp

theorem joint_pair_charge (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f) (a b : K) (e f : E) :
    Fintype.card K ^ 4 *
        (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card ≤
      Fintype.card (α × Bool → K) *
        (1 + (if e = f then Fintype.card K ^ 2 else 0) +
          (if f ∈ badPartners left right e then Fintype.card K else 0)) := by
  by_cases hef : e = f
  · subst f
    have hc := pairEvent_card (hcross e e) a b
    have heq : Fintype.card K ^ 4 * (pairEvent (left e) (right e) a b).card =
        Fintype.card (α × Bool → K) * Fintype.card K ^ 2 := by
      calc
        _ = Fintype.card K ^ 2 *
            (Fintype.card K ^ 2 * (pairEvent (left e) (right e) a b).card) := by ring
        _ = _ := by rw [hc]; ring
    simp only [Finset.inter_self, ite_true, heq]
    apply Nat.mul_le_mul_left
    omega
  · have hpair : (left e, right e) ≠ (left f, right f) := fun h => hef (hinj h)
    by_cases hbad : f ∈ badPartners left right e
    · have hc := jointPair_card_le_cube (hcross e e) (hcross e f)
        (Ne.symm (hcross f e)) (hcross f f) hpair a b
      calc
        _ = Fintype.card K * (Fintype.card K ^ 3 *
            (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card) := by ring
        _ ≤ Fintype.card K * Fintype.card (α × Bool → K) := Nat.mul_le_mul_left _ hc
        _ ≤ _ := by
          simp only [if_neg hef, if_pos hbad, add_zero]
          rw [Nat.mul_comm (Fintype.card K)]
          exact Nat.mul_le_mul_left _ (by omega)
    · have hn : left e ≠ left f ∧ right e ≠ right f ∧
          outputMask left right e ≠ outputMask left right f := by
        simpa [badPartners, not_or] using hbad
      have hm : ∃ i, (left e i == right e i) ≠ (left f i == right f i) :=
        exists_coordinate_ne hn.2.2
      have hc := jointPair_card_four (hcross e e) hn.1 (hcross e f)
        (Ne.symm (hcross f e)) hn.2.1 (hcross f f) hm a b
      simp only [if_neg hef, if_neg hbad, add_zero, mul_one, hc]
      rfl

/-- Full second moment, derived by counting the exceptional partner classes.
`B` bounds the number of shared-endpoint or same-output partners per edge;
the local graph instantiation takes `B = 2*Delta + G`. -/
theorem raw_second_moment (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B) (a b : K) :
    Fintype.card K ^ 4 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      Fintype.card (α × Bool → K) *
        (Fintype.card E * Fintype.card K ^ 2 + Fintype.card E ^ 2 +
          Fintype.card E * B * Fintype.card K) := by
  have hrow : ∀ e : E, (∑ f : E, Fintype.card K ^ 4 *
      (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card) ≤
      Fintype.card (α × Bool → K) * (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) := by
    intro e
    calc
      _ ≤ ∑ f : E, Fintype.card (α × Bool → K) *
          (1 + (if e = f then Fintype.card K ^ 2 else 0) +
            (if f ∈ badPartners left right e then Fintype.card K else 0)) :=
        Finset.sum_le_sum (fun f hf => joint_pair_charge left right hinj hcross a b e f)
      _ = Fintype.card (α × Bool → K) *
          (Fintype.card E + Fintype.card K ^ 2 + (badPartners left right e).card * Fintype.card K) := by
        rw [← Finset.mul_sum]
        congr 1
        simp [Finset.sum_add_distrib]
      _ ≤ _ := by
        apply Nat.mul_le_mul_left
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (hB e)) _
  calc
    _ = ∑ e : E, ∑ f : E, Fintype.card K ^ 4 *
        (pairEvent (left e) (right e) a b ∩ pairEvent (left f) (right f) a b).card := by
      rw [sum_incidenceCount_sq, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e he
      exact Finset.mul_sum ..
    _ ≤ ∑ _e : E, Fintype.card (α × Bool → K) *
        (Fintype.card E + Fintype.card K ^ 2 + B * Fintype.card K) :=
      Finset.sum_le_sum (fun e he => hrow e)
    _ = _ := by simp; ring

/-- The paper's coarse `5 lambda` raw second-moment bound follows from
explicit graph-size and exceptional-partner inequalities. -/
theorem raw_second_moment_five (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (B : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ B)
    (hBp : B ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) :
    Fintype.card K ^ 2 *
        (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  have hp : 0 < Fintype.card K ^ 2 := pow_pos Fintype.card_pos _
  have hs := raw_second_moment left right hinj hcross B hB a b
  have hE : Fintype.card E ^ 2 ≤ Fintype.card E * Fintype.card K ^ 2 := by
    simpa [pow_two] using Nat.mul_le_mul_left (Fintype.card E) hEp
  have hBB : Fintype.card E * B * Fintype.card K ≤
      3 * Fintype.card E * Fintype.card K ^ 2 := by
    have h := Nat.mul_le_mul_right (Fintype.card K)
      (Nat.mul_le_mul_left (Fintype.card E) hBp)
    convert h using 1 <;> ring
  have hs' : Fintype.card K ^ 4 *
      (∑ w, incidenceCount (fun e => pairEvent (left e) (right e) a b) w ^ 2) ≤
        Fintype.card (α × Bool → K) * (5 * Fintype.card E * Fintype.card K ^ 2) := by
    refine hs.trans (Nat.mul_le_mul_left _ ?_)
    nlinarith only [hE, hBB]
  apply Nat.le_of_mul_le_mul_left (c := Fintype.card K ^ 2) ?_ hp
  convert hs' using 1 <;> ring

end GraphMoments

section SeparableTrimming

variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

def bucketSize (vertices : Finset (α → Bool)) (w : α × Bool → K) (target : K) : ℕ :=
  (vertices.filter (fun s => hashValue w s = target)).card

def loadedPairMass (s t : α → Bool) (a b : K) (vertices : Finset (α → Bool)) : ℕ :=
  ∑ w ∈ pairEvent s t a b, bucketSize vertices w a

theorem sum_filtered_cards {X Y : Type*} [DecidableEq X] [DecidableEq Y]
    (A : Finset X) (B : Finset Y) (P : X → Y → Prop) [DecidableRel P] :
    (∑ x ∈ A, (B.filter (P x)).card) =
      ∑ y ∈ B, (A.filter (fun x => P x y)).card := by
  simp only [Finset.card_eq_sum_ones, Finset.sum_filter]
  exact Finset.sum_comm

/-- Conditional bucket-load bound proved from actual three-word uniformity.
The right endpoint must be outside the entire left vertex class. -/
theorem loadedPairMass_bound {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t) :
    Fintype.card K ^ 3 * loadedPairMass s t a b vertices ≤
      (Fintype.card K + vertices.card) * Fintype.card (α × Bool → K) := by
  unfold loadedPairMass bucketSize
  rw [sum_filtered_cards, Finset.mul_sum]
  have hterm : ∀ u ∈ vertices, Fintype.card K ^ 3 *
      ((pairEvent s t a b).filter (fun w => hashValue w u = a)).card ≤
        Fintype.card (α × Bool → K) * (1 + if u = s then Fintype.card K else 0) := by
    intro u hu
    by_cases he : u = s
    · subst u
      have hfilter : (pairEvent s t a b).filter (fun w => hashValue w s = a) =
          pairEvent s t a b := by
        ext w
        constructor
        · intro hw
          exact (Finset.mem_filter.mp hw).1
        · intro hw
          exact Finset.mem_filter.mpr ⟨hw, (Finset.mem_filter.mp hw).2.1⟩
      rw [hfilter]
      have hc := pairEvent_card hst a b
      calc
        _ = Fintype.card K * (Fintype.card K ^ 2 * (pairEvent s t a b).card) := by ring
        _ = Fintype.card K * Fintype.card (α × Bool → K) := by rw [hc]
        _ ≤ _ := by
          simp only [ite_true]
          rw [Nat.mul_comm (Fintype.card K)]
          exact Nat.mul_le_mul_left _ (by omega)
    · have hfilter : (pairEvent s t a b).filter (fun w => hashValue w u = a) =
          wordEvent ![s, t, u] ![a, b, a] := by
        ext w
        simp [pairEvent, wordEvent, Fin.forall_fin_succ, and_assoc]
      rw [hfilter, tripleEvent_card hst (Ne.symm he) (Ne.symm (hcross u hu)) a b a]
      simp [he]
  calc
    _ ≤ ∑ u ∈ vertices, Fintype.card (α × Bool → K) *
        (1 + if u = s then Fintype.card K else 0) := Finset.sum_le_sum hterm
    _ ≤ _ := by
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
      by_cases hs : s ∈ vertices
      · simp [hs, Nat.mul_comm, Nat.add_comm]
      · simp only [Finset.sum_const, smul_eq_mul, mul_one,
          Finset.sum_ite_eq', if_neg hs, add_zero]
        rw [Nat.mul_comm (Fintype.card (α × Bool → K))]
        exact Nat.mul_le_mul_right _ (by omega)

def heavyPairEvent (s t : α → Bool) (a b : K)
    (vertices : Finset (α → Bool)) (B : ℕ) : Finset (α × Bool → K) :=
  (pairEvent s t a b).filter (fun w => B < bucketSize vertices w a)

/-- Finite Markov counting, with the actual bucket cardinality. -/
theorem heavyPairEvent_markov (s t : α → Bool) (a b : K)
    (vertices : Finset (α → Bool)) (B : ℕ) :
    B * (heavyPairEvent s t a b vertices B).card ≤ loadedPairMass s t a b vertices := by
  calc
    _ = ∑ _w ∈ heavyPairEvent s t a b vertices B, B := by simp [Nat.mul_comm]
    _ ≤ ∑ w ∈ heavyPairEvent s t a b vertices B, bucketSize vertices w a := by
      apply Finset.sum_le_sum
      intro w hw
      exact (Finset.mem_filter.mp hw).2.le
    _ ≤ loadedPairMass s t a b vertices := by
      unfold loadedPairMass
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset ..)
        (fun w hw hnot => Nat.zero_le _)

/-- Discarding a bucket above the prescribed threshold loses at most a
quarter of each pair's raw representation mass, uniformly in the targets. -/
theorem heavyPairEvent_bound {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (vertices : Finset (α → Bool)) (hcross : ∀ u ∈ vertices, u ≠ t)
    (B : ℕ) (hB : 4 * (Fintype.card K + vertices.card) ≤ B * Fintype.card K) :
    4 * Fintype.card K ^ 2 * (heavyPairEvent s t a b vertices B).card ≤
      Fintype.card (α × Bool → K) := by
  have hm := heavyPairEvent_markov s t a b vertices B
  have hl := loadedPairMass_bound hst a b vertices hcross
  have hp : 0 < Fintype.card K := Fintype.card_pos
  have hpos : 0 < B * Fintype.card K := lt_of_lt_of_le (by omega) hB
  apply Nat.le_of_mul_le_mul_left (c := B * Fintype.card K) ?_ hpos
  calc
    _ = 4 * (Fintype.card K ^ 3 *
        (B * (heavyPairEvent s t a b vertices B).card)) := by ring
    _ ≤ 4 * (Fintype.card K ^ 3 * loadedPairMass s t a b vertices) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hm)
    _ ≤ 4 * ((Fintype.card K + vertices.card) * Fintype.card (α × Bool → K)) :=
      Nat.mul_le_mul_left _ hl
    _ ≤ _ := by
      simpa only [Nat.mul_assoc] using
        Nat.mul_le_mul_right (Fintype.card (α × Bool → K)) hB

def trimmedPairEvent (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    Finset (α × Bool → K) :=
  (pairEvent s t a b).filter (fun w =>
    bucketSize leftVertices w a ≤ B ∧ bucketSize rightVertices w b ≤ B)

theorem trimmedPairEvent_subset (s t : α → Bool) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool)) (B : ℕ) :
    trimmedPairEvent s t a b leftVertices rightVertices B ⊆ pairEvent s t a b :=
  Finset.filter_subset ..

/-- Both separable masks retain at least half of every pair's raw mass. -/
theorem trimmedPairEvent_bound {s t : α → Bool} (hst : s ≠ t) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool))
    (hL : ∀ u ∈ leftVertices, u ≠ t) (hR : ∀ u ∈ rightVertices, u ≠ s)
    (B : ℕ)
    (hBL : 4 * (Fintype.card K + leftVertices.card) ≤ B * Fintype.card K)
    (hBR : 4 * (Fintype.card K + rightVertices.card) ≤ B * Fintype.card K) :
    Fintype.card (α × Bool → K) ≤ 2 * Fintype.card K ^ 2 *
      (trimmedPairEvent s t a b leftVertices rightVertices B).card := by
  have hsub : pairEvent s t a b ⊆
      (trimmedPairEvent s t a b leftVertices rightVertices B ∪
        heavyPairEvent s t a b leftVertices B) ∪ heavyPairEvent t s b a rightVertices B := by
    intro w hw
    by_cases hl : bucketSize leftVertices w a ≤ B
    · by_cases hr : bucketSize rightVertices w b ≤ B
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_filter.mpr ⟨hw, hl, hr⟩))
      · have hw' : w ∈ pairEvent t s b a := by simpa [pairEvent, and_comm] using hw
        exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hw', by omega⟩)
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hw, by omega⟩))
  have hcard : (pairEvent s t a b).card ≤
      (trimmedPairEvent s t a b leftVertices rightVertices B).card +
        (heavyPairEvent s t a b leftVertices B).card +
          (heavyPairEvent t s b a rightVertices B).card := by
    exact (Finset.card_le_card hsub).trans ((Finset.card_union_le ..).trans
      (Nat.add_le_add_right (Finset.card_union_le ..) _))
  have hraw := pairEvent_card hst a b
  have hleft := heavyPairEvent_bound hst a b leftVertices hL B hBL
  have hright := heavyPairEvent_bound (Ne.symm hst) b a rightVertices hR B hBR
  have hscaled := Nat.mul_le_mul_left (4 * Fintype.card K ^ 2) hcard
  nlinarith

end SeparableTrimming

section TrimmedGraphMoments

variable {E : Type*} [Fintype E] [DecidableEq E]
variable [Fintype α] [DecidableEq α] [Field K] [Fintype K] [DecidableEq K]

theorem trimmed_first_moment (left right : E → α → Bool)
    (hcross : ∀ e f, left e ≠ right f) (a b : K)
    (leftVertices rightVertices : Finset (α → Bool))
    (hL : ∀ e u, u ∈ leftVertices → u ≠ right e)
    (hR : ∀ e u, u ∈ rightVertices → u ≠ left e)
    (B : ℕ)
    (hBL : 4 * (Fintype.card K + leftVertices.card) ≤ B * Fintype.card K)
    (hBR : 4 * (Fintype.card K + rightVertices.card) ≤ B * Fintype.card K) :
    Fintype.card E * Fintype.card (α × Bool → K) ≤
      2 * Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices B) w) := by
  rw [sum_incidenceCount, Finset.mul_sum]
  calc
    _ = ∑ _e : E, Fintype.card (α × Bool → K) := by simp
    _ ≤ _ := Finset.sum_le_sum (fun e he =>
      trimmedPairEvent_bound (hcross e e) a b leftVertices rightVertices (hL e) (hR e) B hBL hBR)

theorem trimmed_second_moment (left right : E → α → Bool)
    (hinj : Function.Injective (fun e => (left e, right e)))
    (hcross : ∀ e f, left e ≠ right f)
    (Bbad : ℕ) (hB : ∀ e, (badPartners left right e).card ≤ Bbad)
    (hBp : Bbad ≤ 3 * Fintype.card K) (hEp : Fintype.card E ≤ Fintype.card K ^ 2)
    (a b : K) (leftVertices rightVertices : Finset (α → Bool)) (Bbucket : ℕ) :
    Fintype.card K ^ 2 * (∑ w, incidenceCount
        (fun e => trimmedPairEvent (left e) (right e) a b leftVertices rightVertices Bbucket) w ^ 2) ≤
      5 * Fintype.card E * Fintype.card (α × Bool → K) := by
  refine (Nat.mul_le_mul_left _ (Finset.sum_le_sum (fun w hw => ?_))).trans
    (raw_second_moment_five left right hinj hcross Bbad hB hBp hEp a b)
  exact Nat.pow_le_pow_left (incidenceCount_mono
    (fun e => trimmedPairEvent_subset (left e) (right e) a b leftVertices rightVertices Bbucket) w) 2

end TrimmedGraphMoments

end ThreeSum.HashFamily
