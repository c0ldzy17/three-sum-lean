import Submission.ThreeSum.HashFamily
import Submission.ThreeSum.LocalGraph
import Submission.ThreeSum.LocalCoverBounds
import Submission.ThreeSum.Greedy
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.List.Pi
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod

/-!
# Actual local one-hot covers

This module instantiates the hash moment and separable trimming proofs with
the disjoint-subset graph. The sample space consists of all assignments to
the two actual symbols at every coordinate. The resulting deterministic
greedy schedule covers every ordered field target, including equal targets.
-/

namespace ThreeSum.LocalHashMoments

open Finset
open scoped BigOperators

open LocalGraph LocalCoverBounds

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]
variable {L h : ℕ}

abbrev Weight (L : ℕ) (K : Type*) := Fin L × Bool → K

/-- Exact light-bucket threshold, with integer rounding built in. -/
def bucketBound (L h p : ℕ) : ℕ := bucketCap (vertexCount L h) p

theorem bucketBound_threshold (L h p : ℕ) (hp : 0 < p) :
    4 * (p + vertexCount L h) ≤ bucketBound L h p * p := by
  exact bucketCap_threshold hp

/-- The number of represented edges after retaining both endpoint buckets. -/
def hitCount (L h : ℕ) (B : ℕ) (w : Weight L K) (target : K × K) : ℕ :=
  HashFamily.incidenceCount (fun e : Edge L h =>
    HashFamily.trimmedPairEvent (left e) (right e) target.1 target.2
      (leftVertices L h) (rightVertices L h) B) w

def Covers (L h : ℕ) (B : ℕ) (w : Weight L K) (target : K × K) : Prop :=
  hitCount L h B w target ≠ 0

instance instDecidableCovers (L h B : ℕ) :
    DecidableRel (Covers (K := K) L h B) := fun _ _ =>
  inferInstanceAs (Decidable (_ ≠ (0 : ℕ)))

theorem bad_partner_bound (e : Edge L h) :
    (HashFamily.badPartners left right e).card ≤ 2 * degree L h + groupSize h := by
  apply HashFamily.badPartners_card_le
  · simpa only [eq_comm, degree] using (endpoint_fiber_bounds e).1
  · simpa only [eq_comm, degree] using (endpoint_fiber_bounds e).2
  · change (univ.filter (fun f : Edge L h =>
      (fun i => left e i == right e i) = (fun i => left f i == right f i))).card ≤
      (2 * h).choose h
    simpa only [eq_comm] using mask_fiber_bound e

theorem first_moment (hsep : 2 * h < L) (target : K × K) :
    Fintype.card (Edge L h) * Fintype.card (Weight L K) ≤
      2 * Fintype.card K ^ 2 *
        ∑ w, hitCount L h (bucketBound L h (Fintype.card K)) w target := by
  apply HashFamily.trimmed_first_moment left right (cross_separated hsep)
  · intro e u hu
    exact vertex_sets_separated hsep u hu (right e) (right_mem_vertices e)
  · intro e u hu
    exact Ne.symm (vertex_sets_separated hsep (left e) (left_mem_vertices e) u hu)
  · simpa only [leftVertices_card, vertexCount] using
      bucketBound_threshold L h (Fintype.card K) Fintype.card_pos
  · simpa only [rightVertices_card, vertexCount] using
      bucketBound_threshold L h (Fintype.card K) Fintype.card_pos

theorem second_moment (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    Fintype.card K ^ 2 * (∑ w, hitCount L h B w target ^ 2) ≤
      5 * Fintype.card (Edge L h) * Fintype.card (Weight L K) := by
  apply HashFamily.trimmed_second_moment left right endpoint_injective
    (cross_separated hsep) (2 * degree L h + groupSize h) bad_partner_bound
  · omega
  · simpa only [edge_card, outputCount, groupSize] using hE

theorem first_moment_real (hsep : 2 * h < L) (target : K × K) :
    mean L h (Fintype.card K) * Fintype.card (Weight L K) / 2 ≤
      ∑ w, (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) := by
  have hm := first_moment (K := K) hsep target
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have he : (Fintype.card (Edge L h) : ℝ) =
      (outputCount L h : ℝ) * groupSize h := by
    exact_mod_cast edge_card L h
  have hmR : (Fintype.card (Edge L h) : ℝ) * Fintype.card (Weight L K) ≤
      2 * (Fintype.card K : ℝ) ^ 2 *
        ∑ w, (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) := by
    exact_mod_cast hm
  rw [he] at hmR
  unfold mean
  apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (pow_pos hp 2)).mpr
  nlinarith

theorem second_moment_real (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (target : K × K) (B : ℕ) :
    (∑ w, (hitCount L h B w target : ℝ) ^ 2) ≤
      5 * mean L h (Fintype.card K) * Fintype.card (Weight L K) := by
  have hm := second_moment (K := K) hsep hDelta hG hE target B
  have hp : (0 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.card_pos
  have hmR : (Fintype.card K : ℝ) ^ 2 *
        (∑ w, (hitCount L h B w target : ℝ) ^ 2) ≤
      5 * (Fintype.card (Edge L h) : ℝ) * Fintype.card (Weight L K) := by
    exact_mod_cast hm
  have he : (Fintype.card (Edge L h) : ℝ) =
      (outputCount L h : ℝ) * groupSize h := by
    exact_mod_cast edge_card L h
  rw [he] at hmR
  calc
    _ ≤ (5 * ((outputCount L h : ℝ) * groupSize h) *
        Fintype.card (Weight L K)) / (Fintype.card K : ℝ) ^ 2 := by
      apply (le_div_iff₀ (pow_pos hp 2)).mpr
      nlinarith
    _ = _ := by unfold mean; ring

/-- Every target is covered by a polynomial fraction of the actual weight
assignments. All probabilistic premises are discharged by counting the
one-hot hashes on the concrete graph. -/
theorem cover_frequency (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    Fintype.card (Weight L K) ≤ 320 * (2 * h + 1) *
      (univ.filter fun w => Covers L h (bucketBound L h (Fintype.card K)) w target).card := by
  have hl := mean_lower (Nat.le_of_lt hsep) (p := Fintype.card K)
    Fintype.card_pos hupper
  have hm : 0 < mean L h (Fintype.card K) :=
    mean_positive (Nat.le_of_lt hsep) Fintype.card_pos
  have hscale : 1 ≤ 16 * (2 * h + 1 : ℝ) * mean L h (Fintype.card K) := by
    have hd : (0 : ℝ) < 16 * (2 * (h : ℝ) + 1) := by positivity
    have ht := (div_le_iff₀ hd).mp hl
    nlinarith
  have hs := Cover.trimmed_support_fraction
    (fun w => (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ))
    (2 * h) hm (by simpa using hscale)
    (first_moment_real hsep target)
    (second_moment_real hsep hDelta hG hE target _)
  have hf : (univ.filter fun w =>
      (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) ≠ 0) =
      (univ.filter fun w => Covers L h (bucketBound L h (Fintype.card K)) w target) := by
    apply Finset.filter_congr
    intro w hw
    change (hitCount L h (bucketBound L h (Fintype.card K)) w target : ℝ) ≠ 0 ↔
      hitCount L h (bucketBound L h (Fintype.card K)) w target ≠ 0
    exact Nat.cast_ne_zero
  rw [hf] at hs
  exact_mod_cast hs

/-- Each retained target has at most `B^2` graph representations. This is an
actual endpoint injection into two light buckets, not a moment bound. -/
theorem hitCount_cap (B : ℕ) (w : Weight L K) (target : K × K) :
    hitCount L h B w target ≤ B ^ 2 := by
  classical
  let F : Finset (Edge L h) := univ.filter (fun e => w ∈
    HashFamily.trimmedPairEvent (left e) (right e) target.1 target.2
      (leftVertices L h) (rightVertices L h) B)
  change F.card ≤ B ^ 2
  by_cases hz : F.card = 0
  · simp only [hz, Nat.zero_le]
  have hn : F.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  obtain ⟨e, he⟩ := hn
  have hlight : HashFamily.bucketSize (leftVertices L h) w target.1 ≤ B ∧
      HashFamily.bucketSize (rightVertices L h) w target.2 ≤ B :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp he).2).2
  let VL := (leftVertices L h).filter (fun s => HashFamily.hashValue w s = target.1)
  let VR := (rightVertices L h).filter (fun s => HashFamily.hashValue w s = target.2)
  have hcount : F.card ≤ (VL ×ˢ VR).card := by
    apply Finset.card_le_card_of_injOn (fun e : Edge L h => (left e, right e))
    · intro f hf
      have hh := (Finset.mem_filter.mp (Finset.mem_filter.mp hf).2).1
      have hv : HashFamily.hashValue w (left f) = target.1 ∧
          HashFamily.hashValue w (right f) = target.2 := (Finset.mem_filter.mp hh).2
      exact Finset.mem_product.mpr
        ⟨Finset.mem_filter.mpr ⟨left_mem_vertices f, hv.1⟩,
         Finset.mem_filter.mpr ⟨right_mem_vertices f, hv.2⟩⟩
    · intro e he f hf hef
      exact endpoint_injective hef
  calc
    F.card ≤ VL.card * VR.card := by simpa only [Finset.card_product] using hcount
    _ ≤ B * B := Nat.mul_le_mul hlight.1 hlight.2
    _ = B ^ 2 := by rw [pow_two]

instance weightInhabited : Inhabited (Weight L K) := ⟨fun _ => 0⟩

def coordinates (L : ℕ) : List (Fin L × Bool) :=
  (List.finRange L).flatMap (fun i => [(i, false), (i, true)])

theorem mem_coordinates (i : Fin L × Bool) : i ∈ coordinates L := by
  obtain ⟨i, b⟩ := i
  cases b <;> simp [coordinates]

/-- Explicit list enumeration; it does not use the noncomputable choice of
an ordering of a `Finset`. -/
def allWeights (L : ℕ) (values : List K) : List (Weight L K) :=
  (List.pi (coordinates L) (fun _ => values)).map
    (fun f i => f i (mem_coordinates i))

theorem mem_allWeights (values : List K) (hvalues : ∀ x, x ∈ values)
    (w : Weight L K) : w ∈ allWeights L values := by
  apply List.mem_map.mpr
  refine ⟨(fun i _ => w i), ?_, rfl⟩
  exact (List.mem_pi _ _).mpr (fun i hi => hvalues (w i))

def scheduleLength (h p : ℕ) : ℕ :=
  320 * (2 * h + 1) * (Nat.log2 (p ^ 2) + 1)

/-- Exhaustive argmax selection with a fully specified finite stopping time. -/
def schedule (L h : ℕ) (values : List K) :
    List (Weight L K) :=
  Cover.greedyChoices (allWeights L values)
    (Covers L h (bucketBound L h (Fintype.card K)))
    (univ : Finset (K × K)) (scheduleLength h (Fintype.card K))

theorem schedule_length (values : List K) :
    (schedule L h values).length = scheduleLength h (Fintype.card K) :=
  Cover.greedyChoices_length ..

/-- The deterministic, actually defined schedule covers all ordered targets. -/
theorem schedule_covers (values : List K) (hvalues : ∀ x, x ∈ values)
    (hsep : 2 * h < L)
    (hDelta : degree L h ≤ Fintype.card K)
    (hG : groupSize h ≤ Fintype.card K)
    (hE : outputCount L h * groupSize h ≤ Fintype.card K ^ 2)
    (hupper : Fintype.card K ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h)))
    (target : K × K) :
    ∃ w ∈ schedule L h values,
      Covers L h (bucketBound L h (Fintype.card K)) w target := by
  have hfreq : ∀ u ∈ (univ : Finset (K × K)), Fintype.card (Weight L K) ≤
      (320 * (2 * h + 1)) * (univ.filter fun w =>
        Covers L h (bucketBound L h (Fintype.card K)) w u).card := by
    intro u hu
    exact cover_frequency hsep hDelta hG hE hupper u
  have hc := Cover.greedy_cover (allWeights L values) (mem_allWeights values hvalues)
    (Covers L h (bucketBound L h (Fintype.card K)))
    (univ : Finset (K × K)) (320 * (2 * h + 1)) (by omega) hfreq target (mem_univ _)
  simpa only [schedule, scheduleLength, Finset.card_univ, Fintype.card_prod, pow_two] using hc

theorem cover_has_edge {B : ℕ} {w : Weight L K} {target : K × K}
    (hc : Covers L h B w target) :
    ∃ e : Edge L h, HashFamily.hashValue w (left e) = target.1 ∧
      HashFamily.hashValue w (right e) = target.2 ∧
      HashFamily.bucketSize (leftVertices L h) w target.1 ≤ B ∧
      HashFamily.bucketSize (rightVertices L h) w target.2 ≤ B := by
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hc)
  have ht := (Finset.mem_filter.mp he).2
  have hp := (Finset.mem_filter.mp ht).1
  have hl := (Finset.mem_filter.mp ht).2
  exact ⟨e, (Finset.mem_filter.mp hp).2.1, (Finset.mem_filter.mp hp).2.2, hl⟩

/-! ## The selected local prime and its actual finite schedule -/

instance localPrimeFact (h : ℕ) : Fact (Nat.Prime (localPrime h)) :=
  ⟨localPrime_prime h⟩

abbrev LocalField (h : ℕ) := ZMod (localPrime h)

def localValues (h : ℕ) : List (LocalField h) :=
  (List.range (localPrime h)).map (fun x : ℕ => (x : LocalField h))

theorem mem_localValues (h : ℕ) (x : LocalField h) : x ∈ localValues h := by
  unfold localValues
  have hv := List.mem_map_of_mem (f := fun n : ℕ => (n : LocalField h))
    (List.mem_range.mpr x.val_lt)
  simpa only [ZMod.natCast_zmod_val] using hv

def localSchedule (h : ℕ) : List (Weight (512 * h) (LocalField h)) :=
  schedule (512 * h) h (localValues h)

theorem localSchedule_length (h : ℕ) :
    (localSchedule h).length =
      320 * (2 * h + 1) * (Nat.log2 (localPrime h ^ 2) + 1) := by
  simpa only [localSchedule, scheduleLength, ZMod.card] using
    schedule_length (L := 512 * h) (h := h) (localValues h)

/-- Main concrete local-cover theorem. There are no moment, probability,
rank, prime-size, or coverage assumptions: the sole premise is `h>0`.
Every ordered residue pair, including an equal pair, is represented by a
retained edge under a member of the specified deterministic schedule. -/
theorem localSchedule_covers {h : ℕ} (hh : 0 < h) (target : LocalField h × LocalField h) :
    ∃ w ∈ localSchedule h, Covers (512 * h) h (localBucketCap h) w target := by
  have hs := schedule_covers (localValues h) (mem_localValues h)
    (L := 512 * h) (h := h) (by omega)
    (by simpa only [ZMod.card] using (degree_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using (groupSize_lt_localPrime hh).le)
    (by simpa only [ZMod.card] using edgeCount_le_localPrime_sq h)
    (by simpa only [ZMod.card] using localPrime_sq_upper h) target
  simpa only [localSchedule, bucketBound, localBucketCap, ZMod.card] using hs

theorem localSchedule_represents {h : ℕ} (hh : 0 < h) (a b : LocalField h) :
    ∃ w ∈ localSchedule h, ∃ e : Edge (512 * h) h,
      HashFamily.hashValue w (left e) = a ∧ HashFamily.hashValue w (right e) = b ∧
      HashFamily.bucketSize (leftVertices (512 * h) h) w a ≤ localBucketCap h ∧
      HashFamily.bucketSize (rightVertices (512 * h) h) w b ≤ localBucketCap h := by
  obtain ⟨w, hw, hc⟩ := localSchedule_covers hh (a, b)
  exact ⟨w, hw, cover_has_edge hc⟩

theorem local_representation_cap (h : ℕ) (w : Weight (512 * h) (LocalField h))
    (target : LocalField h × LocalField h) :
    hitCount (512 * h) h (localBucketCap h) w target ≤ localBucketCap h ^ 2 :=
  hitCount_cap _ _ _

/-- The whole selected schedule has an explicit local representation cap,
counting repeated chosen maps with their list multiplicity. -/
theorem local_schedule_representation_cap (h : ℕ) (target : LocalField h × LocalField h) :
    ((localSchedule h).map (fun w => hitCount (512 * h) h (localBucketCap h) w target)).sum ≤
      (320 * (2 * h + 1) * (Nat.log2 (localPrime h ^ 2) + 1)) * localBucketCap h ^ 2 := by
  have hs : ∀ ws : List (Weight (512 * h) (LocalField h)),
      (ws.map (fun w => hitCount (512 * h) h (localBucketCap h) w target)).sum ≤
        ws.length * localBucketCap h ^ 2 := by
    intro ws
    induction ws with
    | nil => simp
    | cons w ws ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      have hw := local_representation_cap h w target
      nlinarith
  simpa only [localSchedule_length] using hs (localSchedule h)

end ThreeSum.LocalHashMoments
