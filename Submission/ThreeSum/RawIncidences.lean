import Submission.ThreeSum.GlobalEncoding
import Submission.ThreeSum.Arithmetic
import Submission.ThreeSum.Histograms
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Tactic.FinCases

/-!
# Original-index incidences in the guarded global encoding

An incidence retains its original input indices, its complete sequence of
chosen-map occurrences and retained local edges, and its signed arithmetic
lift. Equal input values remain distinct original indices. The lift is
unique for a fixed original triple and representation, so it does not add
a factor of three to the representation bound.
-/

namespace ThreeSum.RawIncidences

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalCoverBounds

def lift (j : Fin 3) : ℤ := (j.val : ℤ) - 1

theorem lift_small (j : Fin 3) : Arithmetic.SmallLift (lift j) := by
  fin_cases j <;> simp [lift, Arithmetic.SmallLift]

theorem lift_injective : Function.Injective lift := by
  intro i j hij
  apply Fin.ext
  unfold lift at hij
  omega

theorem lift_complete {j : ℤ} (hj : Arithmetic.SmallLift j) : ∃ i : Fin 3, lift i = j := by
  rcases hj with rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩

abbrev ChoiceTuple (h J : ℕ) := Fin J → RetainedChoice h

instance retainedChoiceDecidableEq (h : ℕ) : DecidableEq (RetainedChoice h) := inferInstance

instance choiceTupleDecidableEq (h J : ℕ) : DecidableEq (ChoiceTuple h J) :=
  Fintype.decidablePiFintype

def tupleLeft {h J : ℕ} (t : ChoiceTuple h J) : ℤ :=
  Radix.positionalHash (localPrime h) rawLeft (List.ofFn t)

def tupleRight {h J : ℕ} (t : ChoiceTuple h J) : ℤ :=
  Radix.positionalHash (localPrime h) rawRight (List.ofFn t)

def tupleOutput {h J : ℕ} (t : ChoiceTuple h J) : GlobalOutput h J :=
  fun i => blockOfChoice (t i)

def tupleKey {h J : ℕ} (t : ChoiceTuple h J) : ℤ := globalKey (tupleOutput t)

theorem tupleKey_eq {h J : ℕ} (t : ChoiceTuple h J) :
    tupleKey t = tupleRight t - tupleLeft t := by
  rw [tupleKey, globalKey, tupleRight, tupleLeft, positionalHash_difference]
  congr 1
  exact List.map_ofFn.symm

def leftSignature {h J : ℕ} (t : ChoiceTuple h J) :=
  fun i : Fin J => (occurrence (t i), LocalGraph.left (edge (t i)))

def rightSignature {h J : ℕ} (t : ChoiceTuple h J) :=
  fun i : Fin J => (occurrence (t i), LocalGraph.right (edge (t i)))

private theorem positionalHash_map {α β : Type*} (p : ℤ) (f : α → β) (g : β → ℤ)
    (xs : List α) : Radix.positionalHash p g (xs.map f) =
      Radix.positionalHash p (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Radix.positionalHash, ih]

theorem tupleLeft_of_signature {h J : ℕ} {s t : ChoiceTuple h J}
    (he : leftSignature s = leftSignature t) : tupleLeft s = tupleLeft t := by
  have hraw : (fun i => rawLeft (s i)) = (fun i => rawLeft (t i)) := by
    funext i
    have hp := congrFun he i
    have ho := congrArg Prod.fst hp
    have hw := congrArg Prod.snd hp
    change occurrence (s i) = occurrence (t i) at ho
    change LocalGraph.left (edge (s i)) = LocalGraph.left (edge (t i)) at hw
    unfold rawLeft
    rw [ho, hw]
  have hl : (List.ofFn s).map rawLeft = (List.ofFn t).map rawLeft := by
    simpa only [List.map_ofFn, Function.comp_def] using congrArg List.ofFn hraw
  have hhash := congrArg (Radix.positionalHash (localPrime h) id) hl
  simpa only [positionalHash_map, id_eq, tupleLeft] using hhash

theorem tupleRight_of_signature {h J : ℕ} {s t : ChoiceTuple h J}
    (he : rightSignature s = rightSignature t) : tupleRight s = tupleRight t := by
  have hraw : (fun i => rawRight (s i)) = (fun i => rawRight (t i)) := by
    funext i
    have hp := congrFun he i
    have ho := congrArg Prod.fst hp
    have hw := congrArg Prod.snd hp
    change occurrence (s i) = occurrence (t i) at ho
    change LocalGraph.right (edge (s i)) = LocalGraph.right (edge (t i)) at hw
    unfold rawRight
    rw [ho, hw]
  have hl : (List.ofFn s).map rawRight = (List.ofFn t).map rawRight := by
    simpa only [List.map_ofFn, Function.comp_def] using congrArg List.ofFn hraw
  have hhash := congrArg (Radix.positionalHash (localPrime h) id) hl
  simpa only [positionalHash_map, id_eq, tupleRight] using hhash

def tupleOfList {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    ChoiceTuple h J := fun i => xs.get (Fin.cast hlen.symm i)

theorem ofFn_tupleOfList {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    List.ofFn (tupleOfList xs hlen) = xs := by
  subst J
  exact List.ofFn_get xs

theorem tuple_mem_representations {h J : ℕ} (t : ChoiceTuple h J) (b c : ℤ) :
    List.ofFn t ∈ representations h J b c ↔
      globalModulus h J ∣ b - tupleLeft t ∧ globalModulus h J ∣ c - tupleRight t := by
  rw [mem_representations]
  simp only [List.length_ofFn, true_and, tupleLeft, tupleRight]

theorem tuple_difference_congruence {h J : ℕ} {t : ChoiceTuple h J} {b c : ℤ}
    (ht : List.ofFn t ∈ representations h J b c) :
    globalModulus h J ∣ (c - b) - tupleKey t := by
  obtain ⟨hb, hc⟩ := (tuple_mem_representations t b c).mp ht
  rw [tupleKey_eq]
  rw [sub_sub_sub_comm]
  exact dvd_sub hc hb

abbrev Witness (h J : ℕ) := ChoiceTuple h J × Fin 3

instance witnessDecidableEq (h J : ℕ) : DecidableEq (Witness h J) := inferInstance

/-- Retained representations of a fixed original triple. The C target is
shifted by the common balancing offset, and the A key uses the same shift. -/
def witnesses (h J : ℕ) (P d a b c : ℤ) : Finset (Witness h J) :=
  Finset.univ.filter fun w : Witness h J =>
    List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
      globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1

theorem mem_witnesses {h J : ℕ} {P d a b c : ℤ} {w : Witness h J} :
    w ∈ witnesses h J P d a b c ↔
      List.ofFn w.1 ∈ representations h J (b % P) (c % P + d) ∧
        globalModulus h J ∣ (a % P + lift w.2 * P + d) - tupleKey w.1 := by
  simp only [witnesses, Finset.mem_filter, Finset.mem_univ, true_and]

theorem witness_sound {h J : ℕ} {P d a b c : ℤ} {w : Witness h J}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hw : w ∈ witnesses h J P d a b c) : P ∣ c - b - a := by
  obtain ⟨hrep, hquery⟩ := mem_witnesses.mp hw
  have hdiff := tuple_difference_congruence hrep
  have hkey : Int.ModEq (globalModulus h J)
      (a % P + lift w.2 * P + d) (c % P + d - b % P) := by
    apply Int.modEq_of_dvd
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hdiff hquery
  exact Arithmetic.guarded_remainder_lift_sound hP hguard (lift_small w.2) hkey

theorem witnesses_nonempty {h J : ℕ} {P d a b c : ℤ}
    (hh : 0 < h) (hP : 0 < P) (hdiv : P ∣ c - b - a) :
    (witnesses h J P d a b c).Nonempty := by
  have heq : Int.ModEq P (c % P - b % P - a % P) (c - b - a) :=
    ((Int.mod_modEq c P).sub (Int.mod_modEq b P)).sub (Int.mod_modEq a P)
  have hnorm : P ∣ c % P - b % P - a % P := heq.dvd_iff.mpr hdiv
  obtain ⟨j, hj, he⟩ := Arithmetic.small_lift_exists hP
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP)
    (Int.emod_nonneg _ hP.ne') (Int.emod_lt_of_pos _ hP) hnorm
  obtain ⟨l, hl⟩ := lift_complete hj
  obtain ⟨xs, hxs⟩ := representations_nonempty hh J (b % P) (c % P + d)
  let hlen := ((mem_representations h J (b % P) (c % P + d) xs).mp hxs).1
  let t := tupleOfList xs hlen
  have ht : List.ofFn t ∈ representations h J (b % P) (c % P + d) := by
    simpa only [t, ofFn_tupleOfList] using hxs
  refine ⟨(t, l), mem_witnesses.mpr ⟨ht, ?_⟩⟩
  have hd := tuple_difference_congruence ht
  have htarget : a % P + lift l * P + d = (c % P + d) - b % P := by
    rw [hl]
    linarith
  simpa only [htarget] using hd

theorem witnesses_nonempty_iff {h J : ℕ} {P d a b c : ℤ}
    (hh : 0 < h) (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).Nonempty ↔ P ∣ c - b - a := by
  constructor
  · rintro ⟨w, hw⟩
    exact witness_sound hP hguard hw
  · exact witnesses_nonempty hh hP

/-- Projection to the retained list is injective on the raw witnesses of
one original triple: the guard makes its lift unique. -/
theorem witness_projection_injective {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    Set.InjOn (fun w : Witness h J => List.ofFn w.1) (witnesses h J P d a b c) := by
  intro w hw v hv he
  have ht : w.1 = v.1 := List.ofFn_injective he
  have hwq := (mem_witnesses.mp hw).2
  have hvq := (mem_witnesses.mp hv).2
  have hd : globalModulus h J ∣
      (a % P + lift w.2 * P + d) - (a % P + lift v.2 * P + d) := by
    rw [ht] at hwq
    simpa only [sub_sub_sub_cancel_right] using dvd_sub hwq hvq
  have hj := Arithmetic.guarded_lift_unique hP hguard (lift_small w.2) (lift_small v.2) hd
  exact Prod.ext ht (lift_injective hj)

theorem witnesses_card_bound {h J : ℕ} {P d a b c : ℤ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) :
    (witnesses h J P d a b c).card ≤ representationCap h J := by
  calc
    _ ≤ (representations h J (b % P) (c % P + d)).card := by
      apply Finset.card_le_card_of_injOn (fun w : Witness h J => List.ofFn w.1)
      · intro w hw
        exact (mem_witnesses.mp hw).1
      · exact witness_projection_injective hP hguard
    _ ≤ _ := representations_card_bound h J (b % P) (c % P + d)

theorem witnesses_card_eq_sum (h J : ℕ) (P d a b c : ℤ) :
    (witnesses h J P d a b c).card =
      ∑ t : ChoiceTuple h J, ∑ j : Fin 3,
        if globalModulus h J ∣ b % P - tupleLeft t ∧
          globalModulus h J ∣ c % P + d - tupleRight t ∧
          globalModulus h J ∣ (a % P + lift j * P + d) - tupleKey t
        then 1 else 0 := by
  rw [witnesses, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]
  simp only [tuple_mem_representations, and_assoc]

private theorem sum_four_swap {α β γ δ : Type*}
    (A : Finset α) (B : Finset β) (C : Finset γ) (D : Finset δ)
    (f : α → β → γ → δ → ℕ) :
    (∑ a ∈ A, ∑ b ∈ B, ∑ c ∈ C, ∑ d ∈ D, f a b c d) =
      ∑ c ∈ C, ∑ d ∈ D, ∑ a ∈ A, ∑ b ∈ B, f a b c d := by
  calc
    _ = ∑ a ∈ A, ∑ c ∈ C, ∑ d ∈ D, ∑ b ∈ B, f a b c d := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro c _
      rw [Finset.sum_comm]

section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

abbrev Original (α β γ : Type*) := α × (β × γ)

def difference (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (t : Original α β γ) : ℤ :=
  c t.2.2 - b t.2.1 - a t.1

abbrev RawItem (h J : ℕ) (α β γ : Type*) := Σ _t : Original α β γ, Witness h J

/-- The band is a finite set of original index triples. It is part of the
owner data, rather than an additional representation choice. -/
def rawOn (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : Finset (RawItem h J α β γ) :=
  T.sigma fun t => witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)

theorem mem_rawOn {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ} :
    r ∈ rawOn h J P d T a b c ↔
      r.1 ∈ T ∧ r.2 ∈ witnesses h J P d (a r.1.1) (b r.1.2.1) (c r.1.2.2) :=
  Finset.mem_sigma

theorem raw_sound {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {r : RawItem h J α β γ}
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hr : r ∈ rawOn h J P d T a b c) : P ∣ difference a b c r.1 :=
  witness_sound hP hguard (mem_rawOn.mp hr).2

theorem raw_complete {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {t : Original α β γ}
    (hh : 0 < h) (hP : 0 < P) (ht : t ∈ T) (hd : P ∣ difference a b c t) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t := by
  obtain ⟨w, hw⟩ := witnesses_nonempty hh hP hd
  exact ⟨⟨t, w⟩, mem_rawOn.mpr ⟨ht, hw⟩, rfl⟩

theorem raw_true_triple_complete {h J : ℕ} {P d : ℤ} {T : Finset (Original α β γ)}
    {a : α → ℤ} {b : β → ℤ} {c : γ → ℤ} {t : Original α β γ}
    (hh : 0 < h) (hP : 0 < P) (ht : t ∈ T) (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t :=
  raw_complete hh hP ht (by rw [he]; exact dvd_zero _)

theorem raw_owner_fiber_bound {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) (t : Original α β γ) :
    ((rawOn h J P d T a b c).filter fun r => r.1 = t).card ≤ representationCap h J := by
  calc
    _ ≤ (witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card := by
      apply Finset.card_le_card_of_injOn (fun r : RawItem h J α β γ => r.2)
      · intro r hr
        obtain ⟨hr, ht⟩ := Finset.mem_filter.mp hr
        have hw := (mem_rawOn.mp hr).2
        simpa only [Finset.mem_coe, ht] using hw
      · intro r hr s hs he
        have hrt := (Finset.mem_filter.mp hr).2
        have hst := (Finset.mem_filter.mp hs).2
        exact Sigma.ext (hrt.trans hst.symm) (heq_of_eq he)
    _ ≤ _ := witnesses_card_bound hP hguard

theorem raw_owner_weight_bound {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J) (t : Original α β γ) :
    Arithmetic.fiberWeight (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t ≤
      representationCap h J := by
  have he : Arithmetic.fiberWeight (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) t =
      ((rawOn h J P d T a b c).filter fun r => r.1 = t).card := by
    simp only [Arithmetic.fiberWeight, Finset.card_eq_sum_ones, Finset.sum_filter]
  rw [he]
  exact raw_owner_fiber_bound T a b c hP hguard t

def rawMass (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : ℕ := (rawOn h J P d T a b c).card

theorem rawMass_eq_sum_witnesses (h J : ℕ) (P d : ℤ) (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    rawMass h J P d T a b c =
      ∑ t ∈ T, (witnesses h J P d (a t.1) (b t.2.1) (c t.2.2)).card :=
  Finset.card_sigma _ _

/-- Bucket multiplicity counts original B indices, including indices that
carry equal values. Only the left representation is inspected. -/
def leftBucket {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (t : ChoiceTuple h J) : ℕ :=
  ∑ j ∈ B, if globalModulus h J ∣ b j % P - tupleLeft t then 1 else 0

/-- The right bucket uses the same common offset as the A query keys. -/
def rightBucket {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ) (t : ChoiceTuple h J) : ℕ :=
  ∑ j ∈ C, if globalModulus h J ∣ c j % P + d - tupleRight t then 1 else 0

theorem leftBucket_of_signature {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {s t : ChoiceTuple h J} (he : leftSignature s = leftSignature t) :
    leftBucket P B b s = leftBucket P B b t := by
  simp only [leftBucket, tupleLeft_of_signature he]

theorem rightBucket_of_signature {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    {s t : ChoiceTuple h J} (he : rightSignature s = rightSignature t) :
    rightBucket P d C c s = rightBucket P d C c t := by
  simp only [rightBucket, tupleRight_of_signature he]

theorem bucket_product_eq_sum {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ∑ j ∈ B, ∑ k ∈ C,
        if globalModulus h J ∣ b j % P - tupleLeft t ∧
          globalModulus h J ∣ c k % P + d - tupleRight t then 1 else 0 := by
  unfold leftBucket rightBucket
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hL : globalModulus h J ∣ b j % P - tupleLeft t <;>
    by_cases hR : globalModulus h J ∣ c k % P + d - tupleRight t <;> simp [hL, hR]

theorem bucket_product_eq_card {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :
    leftBucket P B b t * rightBucket P d C c t =
      ((B ×ˢ C).filter fun p => globalModulus h J ∣ b p.1 % P - tupleLeft t ∧
        globalModulus h J ∣ c p.2 % P + d - tupleRight t).card := by
  rw [Finset.card_eq_sum_ones, Finset.sum_filter, Finset.sum_product]
  exact bucket_product_eq_sum P d B C b c t

/-- The mass computed by the product weights attached to retained disjoint
endpoint tuples and queried output keys. -/
def productMass (h J : ℕ) (P d : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) : ℕ :=
  ∑ i ∈ A, ∑ t : ChoiceTuple h J, ∑ j : Fin 3,
    if globalModulus h J ∣ (a i % P + lift j * P + d) - tupleKey t
    then leftBucket P B b t * rightBucket P d C c t else 0

/-- Exact expansion of all bucket products into original-index incidences.
No bucket-uniformity or multiplicity hypothesis is used. -/
theorem rawMass_eq_productMass (h J : ℕ) (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) :
    rawMass h J P d (A ×ˢ (B ×ˢ C)) a b c = productMass h J P d A B C a b c := by
  rw [rawMass_eq_sum_witnesses, Finset.sum_product]
  unfold productMass
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.sum_product, witnesses_card_eq_sum]
  rw [sum_four_swap]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro j _
  by_cases hq : globalModulus h J ∣ (a i % P + lift j * P + d) - tupleKey t
  · simp only [hq, and_true, ite_true]
    exact (bucket_product_eq_sum P d B C b c t).symm
  · simp only [hq, and_false, ite_false, Finset.sum_const_zero]

/-- The dense stopping rule uses the actual guarded incidences and the
actual radix multiplicity bound. Its score is the weighted false-count
quantity computed by the arithmetic histogram identities. -/
theorem dense_early_yes {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬l ∣ difference a b c t)
    (hlarge : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      rawMass h J P d T a b c) :
    ∃ t ∈ T, difference a b c t = 0 := by
  let good : Original α β γ → Prop :=
    fun t => t ∉ T ∨ ¬P ∣ difference a b c t ∨ difference a b c t = 0
  have hset : (Finset.univ.filter fun t : Original α β γ => ¬good t) =
      T.filter (fun t => P ∣ difference a b c t ∧ difference a b c t ≠ 0) := by
    ext t
    simp [good]
  have hcount : (Finset.univ.filter fun t : Original α β γ => ¬good t).card ≤
      Arithmetic.weightedFalseCount T (difference a b c) aux P := by
    rw [hset, Finset.card_eq_sum_ones, Finset.sum_filter]
    exact Arithmetic.falseCount_le_weightedFalseCount T (difference a b c) aux P hsep
  have hmass : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      ∑ _r ∈ rawOn h J P d T a b c, (1 : ℕ) := by
    simpa only [Finset.sum_const, smul_eq_mul, mul_one, rawMass] using hlarge
  obtain ⟨r, hr, _, hg⟩ := Arithmetic.early_yes
    (rawOn h J P d T a b c) Sigma.fst (fun _ => 1) good
    (representationCap h J) (Arithmetic.weightedFalseCount T (difference a b c) aux P)
    (fun t _ => raw_owner_weight_bound T a b c hP hguard t) hcount hmass
  have ht := (mem_rawOn.mp hr).1
  have hd := raw_sound hP hguard hr
  refine ⟨r.1, ht, ?_⟩
  rcases hg with hnot | hnot | hz
  · exact False.elim (hnot ht)
  · exact False.elim (hnot hd)
  · exact hz

theorem dense_early_yes_of_aux_product {h J : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (aux : Finset ℤ) (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hcop : (aux : Set ℤ).Pairwise (fun l r => IsCoprime l r))
    (hbound : ∀ t ∈ T, difference a b c t ≠ 0 →
      (difference a b c t).natAbs < (∏ l ∈ aux, l).natAbs)
    (hlarge : representationCap h J * Arithmetic.weightedFalseCount T (difference a b c) aux P <
      rawMass h J P d T a b c) :
    ∃ t ∈ T, difference a b c t = 0 := by
  apply dense_early_yes T a b c aux hP hguard _ hlarge
  intro t ht hn
  exact Arithmetic.exists_aux_not_dvd_of_prod_bound aux (difference a b c t)
    hcop hn (hbound t ht hn)

/-- The same stopping rule stated directly for the product-weight mass
computed for one band of A, B and C indices. -/
theorem productMass_early_yes {h J : ℕ} {P d : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (aux : Finset ℤ)
    (hP : 0 < P) (hguard : 4 * P ≤ globalModulus h J)
    (hsep : ∀ t ∈ A ×ˢ (B ×ˢ C), difference a b c t ≠ 0 →
      ∃ l ∈ aux, ¬l ∣ difference a b c t)
    (hlarge : representationCap h J *
      Arithmetic.weightedFalseCount (A ×ˢ (B ×ˢ C)) (difference a b c) aux P <
        productMass h J P d A B C a b c) :
    ∃ i ∈ A, ∃ j ∈ B, ∃ k ∈ C, a i + b j = c k := by
  have hm : representationCap h J *
      Arithmetic.weightedFalseCount (A ×ˢ (B ×ˢ C)) (difference a b c) aux P <
        rawMass h J P d (A ×ˢ (B ×ˢ C)) a b c := by
    simpa only [rawMass_eq_productMass] using hlarge
  obtain ⟨t, ht, he⟩ := dense_early_yes (A ×ˢ (B ×ˢ C)) a b c aux hP hguard hsep hm
  obtain ⟨ha, hb, hc⟩ := by simpa only [Finset.mem_product] using ht
  refine ⟨t.1, ha, t.2.1, hb, t.2.2, hc, ?_⟩
  unfold difference at he
  omega

end OriginalIndices

end ThreeSum.RawIncidences
