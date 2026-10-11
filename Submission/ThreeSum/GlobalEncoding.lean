import Submission.ThreeSum.LocalHashMoments
import Submission.ThreeSum.Radix
import Mathlib.Data.List.OfFn

/-!
# Concrete retained choices and the global radix encoding

The local choice type retains the occurrence of a map in the deterministic
schedule.  Repeated chosen maps therefore keep their representation
multiplicity.  Canonical integer lifts of their one-hot coefficients feed
the radix recursion, whose coverage and cap are instantiated here with no
local-cover assumptions.
-/

namespace ThreeSum.GlobalEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open LocalGraph LocalCoverBounds LocalHashMoments

def scheduleSize (h : ℕ) : ℕ := scheduleLength h (localPrime h)

theorem scheduleSize_eq_length (h : ℕ) : scheduleSize h = (localSchedule h).length := by
  rw [localSchedule_length]
  rfl

abbrev Occurrence (h : ℕ) := Fin (scheduleSize h)

def mapAt (h : ℕ) (i : Occurrence h) : Weight (512 * h) (LocalField h) :=
  (localSchedule h).get (Fin.cast (scheduleSize_eq_length h) i)

private theorem exists_list_index {α : Type*} (xs : List α) {n : ℕ}
    (hn : n = xs.length) (x : α) (hx : x ∈ xs) :
    ∃ i : Fin n, xs.get (Fin.cast hn i) = x := by
  subst n
  simpa only [Fin.cast_refl, id_eq] using List.mem_iff_get.mp hx

theorem mapAt_exists {h : ℕ} {w : Weight (512 * h) (LocalField h)}
    (hw : w ∈ localSchedule h) : ∃ i : Occurrence h, mapAt h i = w := by
  exact exists_list_index (localSchedule h) (scheduleSize_eq_length h) w hw

def Survives (h : ℕ) (i : Occurrence h) (e : Edge (512 * h) h) : Prop :=
  HashFamily.bucketSize (leftVertices (512 * h) h) (mapAt h i)
      (HashFamily.hashValue (mapAt h i) (left e)) ≤ localBucketCap h ∧
    HashFamily.bucketSize (rightVertices (512 * h) h) (mapAt h i)
      (HashFamily.hashValue (mapAt h i) (right e)) ≤ localBucketCap h

instance (h : ℕ) (i : Occurrence h) (e : Edge (512 * h) h) :
    Decidable (Survives h i e) := by unfold Survives; infer_instance

/-- A choice includes its schedule occurrence as well as its retained edge. -/
abbrev RetainedChoice (h : ℕ) :=
  {p : Occurrence h × Edge (512 * h) h // Survives h p.1 p.2}

def occurrence {h : ℕ} (c : RetainedChoice h) : Occurrence h := c.val.1
def edge {h : ℕ} (c : RetainedChoice h) : Edge (512 * h) h := c.val.2

theorem retained_survives {h : ℕ} (c : RetainedChoice h) :
    Survives h (occurrence c) (edge c) := c.property

/-- Sum of the canonical integer representatives of the selected symbol
weights. This is the raw integer sum before reduction modulo the prime. -/
def rawHash {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) : ℤ :=
  ∑ i, ((w (i, s i)).val : ℤ)

theorem rawHash_cast {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (rawHash w s : LocalField h) = HashFamily.hashValue w s := by
  simp [rawHash, HashFamily.hashValue]

theorem rawHash_nonnegative {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    0 ≤ rawHash w s := Finset.sum_nonneg (fun _ _ => Int.natCast_nonneg _)

theorem rawHash_upper {h L : ℕ} (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    rawHash w s ≤ (L : ℤ) * (localPrime h - 1) := by
  calc
    rawHash w s ≤ ∑ _i : Fin L, ((localPrime h : ℤ) - 1) := by
      unfold rawHash
      apply Finset.sum_le_sum
      intro i _
      have hi : ((w (i, s i)).val : ℤ) < (localPrime h : ℤ) := by
        exact_mod_cast (w (i, s i)).val_lt
      omega
    _ = _ := by simp [mul_sub]

theorem dvd_sub_rawHash_iff {h L : ℕ} (a : ℤ)
    (w : Weight L (LocalField h)) (s : Fin L → Bool) :
    (localPrime h : ℤ) ∣ a - rawHash w s ↔
      HashFamily.hashValue w s = (a : LocalField h) := by
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd, Int.cast_sub, rawHash_cast, sub_eq_zero]
  exact eq_comm

def rawLeft {h : ℕ} (c : RetainedChoice h) : ℤ :=
  rawHash (mapAt h (occurrence c)) (left (edge c))

def rawRight {h : ℕ} (c : RetainedChoice h) : ℤ :=
  rawHash (mapAt h (occurrence c)) (right (edge c))

theorem mem_localFiber {h : ℕ} (a b : ℤ) (c : RetainedChoice h) :
    c ∈ Radix.localFiber (localPrime h) rawLeft rawRight a b ↔
      HashFamily.hashValue (mapAt h (occurrence c)) (left (edge c)) = (a : LocalField h) ∧
      HashFamily.hashValue (mapAt h (occurrence c)) (right (edge c)) = (b : LocalField h) := by
  simp only [Radix.localFiber, Finset.mem_filter, Finset.mem_univ, true_and,
    rawLeft, rawRight, dvd_sub_rawHash_iff]

theorem localFiber_nonempty {h : ℕ} (hh : 0 < h) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).Nonempty := by
  obtain ⟨w, hw, e, ha, hb, hL, hR⟩ :=
    localSchedule_represents hh (a : LocalField h) (b : LocalField h)
  obtain ⟨i, hmap⟩ := mapAt_exists hw
  have hs : Survives h i e := by
    unfold Survives
    rw [hmap, ha, hb]
    exact ⟨hL, hR⟩
  refine ⟨⟨(i, e), hs⟩, (mem_localFiber a b _).mpr ?_⟩
  change HashFamily.hashValue (mapAt h i) (left e) = (a : LocalField h) ∧
    HashFamily.hashValue (mapAt h i) (right e) = (b : LocalField h)
  rw [hmap]
  exact ⟨ha, hb⟩

set_option maxHeartbeats 1000000 in
private theorem occurrence_fiber_bound (h : ℕ) (a b : ℤ) (i : Occurrence h) :
    ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
      (fun c => occurrence c = i)).card ≤ localBucketCap h ^ 2 := by
  let hits : Finset (Edge (512 * h) h) := Finset.univ.filter fun e =>
    mapAt h i ∈ HashFamily.trimmedPairEvent (left e) (right e)
      (a : LocalField h) (b : LocalField h)
      (leftVertices (512 * h) h) (rightVertices (512 * h) h) (localBucketCap h)
  have hcount : ((Radix.localFiber (localPrime h) rawLeft rawRight a b :
      Finset (RetainedChoice h)).filter (fun c => occurrence c = i)).card ≤ hits.card := by
    apply Finset.card_le_card_of_injOn edge
    · intro c hc
      obtain ⟨hc, hi⟩ := Finset.mem_filter.mp hc
      obtain ⟨ha, hb⟩ := (mem_localFiber a b c).mp hc
      simp only [hi] at ha hb
      have hs := retained_survives c
      simp only [Survives, hi, ha, hb] at hs
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      apply Finset.mem_filter.mpr
      refine ⟨?_, hs⟩
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _, by simpa only [hi] using And.intro ha hb⟩
    · intro c hc d hd he
      apply Subtype.ext
      apply Prod.ext
      · exact (Finset.mem_filter.mp hc).2.trans (Finset.mem_filter.mp hd).2.symm
      · exact he
  exact hcount.trans (local_representation_cap h (mapAt h i) (a, b))

/-- The exact local cap counts map occurrences separately, including
repetitions in the chosen greedy schedule. -/
theorem localFiber_card_bound (h : ℕ) (a b : ℤ) :
    (Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).card ≤
      scheduleSize h * localBucketCap h ^ 2 := by
  calc
    _ = ∑ i : Occurrence h,
        ((Radix.localFiber (localPrime h) rawLeft rawRight a b : Finset (RetainedChoice h)).filter
          (fun c => occurrence c = i)).card := by
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _i : Occurrence h, localBucketCap h ^ 2 := by
      apply Finset.sum_le_sum
      intro i _
      exact occurrence_fiber_bound h a b i
    _ = _ := by simp [Occurrence]

def representations (h J : ℕ) (a b : ℤ) : Finset (List (RetainedChoice h)) :=
  Radix.representations (localPrime h) rawLeft rawRight J a b

def globalModulus (h J : ℕ) : ℤ := (localPrime h : ℤ) ^ J

def representationCap (h J : ℕ) : ℕ :=
  (scheduleSize h * localBucketCap h ^ 2) ^ J

theorem mem_representations (h J : ℕ) (a b : ℤ) (xs : List (RetainedChoice h)) :
    xs ∈ representations h J a b ↔ xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs := by
  exact Radix.mem_representations (localPrime h)
    (by exact_mod_cast (localPrime_pos h).ne') rawLeft rawRight J a b xs

theorem representations_nonempty {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    (representations h J a b).Nonempty :=
  Radix.representations_nonempty (localPrime h) rawLeft rawRight
    (localFiber_nonempty hh) J a b

theorem representations_card_bound (h J : ℕ) (a b : ℤ) :
    (representations h J a b).card ≤ representationCap h J :=
  Radix.representations_card_le (localPrime h) rawLeft rawRight
    (scheduleSize h * localBucketCap h ^ 2) (localFiber_card_bound h) J a b

/-- Actual global coverage and multiplicity, with no probabilistic, graph,
prime, or local-cover assumptions. -/
theorem global_cover_and_cap {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    (∃ xs : List (RetainedChoice h), xs.length = J ∧
      globalModulus h J ∣ a - Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ b - Radix.positionalHash (localPrime h) rawRight xs) ∧
      (representations h J a b).card ≤ representationCap h J := by
  obtain ⟨xs, hxs⟩ := representations_nonempty hh J a b
  exact ⟨⟨xs, (mem_representations h J a b xs).mp hxs⟩,
    representations_card_bound h J a b⟩

/-- The integer difference contribution is determined by the equality
positions alone. Positions in the output subset contribute zero. -/
def rawOutput {h L : ℕ} (w : Weight L (LocalField h)) (Q : Finset (Fin L)) : ℤ :=
  ∑ i, if i ∈ Q then 0 else ((w (i, true)).val : ℤ) - ((w (i, false)).val : ℤ)

theorem rawHash_difference {h L k : ℕ} (w : Weight L (LocalField h))
    (e : Edge L k) :
    rawHash w (right e) - rawHash w (left e) = rawOutput w (output e) := by
  unfold rawHash rawOutput
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hd := Finset.disjoint_left.mp (edge_data e).2.2
  by_cases hs : i ∈ e.val.1 <;> by_cases hv : i ∈ e.val.2 <;>
    simp_all [left, right, leftWord, rightWord, output]

/-- An output record retains the chosen-map occurrence and the union of the
two disjoint endpoint subsets. It forgets the internal partition. -/
abbrev OutputBlock (h : ℕ) :=
  Occurrence h × {Q // Q ∈ LayerCounts.vertices (512 * h) (2 * h)}

def blockOfChoice {h : ℕ} (c : RetainedChoice h) : OutputBlock h :=
  (occurrence c, ⟨output (edge c), LayerCounts.mem_vertices.mpr (output_card (edge c))⟩)

def blockKey {h : ℕ} (b : OutputBlock h) : ℤ := rawOutput (mapAt h b.1) b.2.val

theorem blockKey_choice {h : ℕ} (c : RetainedChoice h) :
    blockKey (blockOfChoice c) = rawRight c - rawLeft c :=
  (rawHash_difference (mapAt h (occurrence c)) (edge c)).symm

theorem outputBlock_card (h : ℕ) :
    Fintype.card (OutputBlock h) = scheduleSize h * outputCount (512 * h) h := by
  simp only [OutputBlock, Fintype.card_prod, Occurrence, Fintype.card_fin,
    Fintype.card_coe, LayerCounts.vertices_card, outputCount]

abbrev GlobalOutput (h J : ℕ) := Fin J → OutputBlock h

theorem globalOutput_card (h J : ℕ) :
    Fintype.card (GlobalOutput h J) =
      scheduleSize h ^ J * outputCount (512 * h) h ^ J := by
  simp only [GlobalOutput, Fintype.card_fun, Fintype.card_fin, outputBlock_card, mul_pow]

def globalKey {h J : ℕ} (q : GlobalOutput h J) : ℤ :=
  Radix.positionalHash (localPrime h) blockKey (List.ofFn q)

theorem positionalHash_difference {h : ℕ} (xs : List (RetainedChoice h)) :
    Radix.positionalHash (localPrime h) rawRight xs -
      Radix.positionalHash (localPrime h) rawLeft xs =
        Radix.positionalHash (localPrime h) blockKey (xs.map blockOfChoice) := by
  induction xs with
  | nil => simp [Radix.positionalHash]
  | cons c xs ih =>
      simp only [List.map_cons, Radix.positionalHash, blockKey_choice]
      rw [← ih]
      ring

def outputOfChoices {h J : ℕ} (xs : List (RetainedChoice h)) (hlen : xs.length = J) :
    GlobalOutput h J :=
  fun i => blockOfChoice (xs.get (Fin.cast hlen.symm i))

theorem ofFn_outputOfChoices {h J : ℕ} (xs : List (RetainedChoice h))
    (hlen : xs.length = J) :
    List.ofFn (outputOfChoices xs hlen) = xs.map blockOfChoice := by
  subst J
  exact List.ofFn_getElem_eq_map xs blockOfChoice

/-- The exact, unreduced global hash difference depends only on the
occurrence/output tuple, and hence is independent of every internal split. -/
theorem globalKey_outputOfChoices {h J : ℕ} (xs : List (RetainedChoice h))
    (hlen : xs.length = J) :
    globalKey (outputOfChoices xs hlen) =
      Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs := by
  rw [globalKey, ofFn_outputOfChoices, positionalHash_difference]

theorem output_key_congruence {h J : ℕ} {a b : ℤ}
    {xs : List (RetainedChoice h)} (hxs : xs ∈ representations h J a b) :
    globalModulus h J ∣ (b - a) -
      globalKey (outputOfChoices xs ((mem_representations h J a b xs).mp hxs).1) := by
  obtain ⟨hlen, ha, hb⟩ := (mem_representations h J a b xs).mp hxs
  rw [globalKey_outputOfChoices]
  have he : (b - a) -
      (Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs) =
      (b - Radix.positionalHash (localPrime h) rawRight xs) -
        (a - Radix.positionalHash (localPrime h) rawLeft xs) := by ring
  rw [he]
  exact dvd_sub hb ha

/-- For every integer target pair there is a retained representation whose
output belongs to the explicitly bounded occurrence/output product and
whose output key is the target difference modulo the global modulus. -/
theorem global_output_cover {h : ℕ} (hh : 0 < h) (J : ℕ) (a b : ℤ) :
    ∃ xs ∈ representations h J a b, ∃ q : GlobalOutput h J,
      globalKey q = Radix.positionalHash (localPrime h) rawRight xs -
        Radix.positionalHash (localPrime h) rawLeft xs ∧
      globalModulus h J ∣ (b - a) - globalKey q := by
  obtain ⟨xs, hxs⟩ := representations_nonempty hh J a b
  let hlen := ((mem_representations h J a b xs).mp hxs).1
  exact ⟨xs, hxs, outputOfChoices xs hlen, globalKey_outputOfChoices xs hlen,
    output_key_congruence hxs⟩

end ThreeSum.GlobalEncoding
