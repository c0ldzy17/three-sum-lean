import Submission.ThreeSum.BlockRows
import Submission.ThreeSum.RawPrefixCounts

/-!
# Independent trimmed endpoint histograms on the flattened block ground set

A histogram only inspects one endpoint and the occurrence vector. Its support
is exactly on independently retained balanced block subsets. Compatible
opposite endpoints reconstruct an actual retained choice tuple.
-/

namespace ThreeSum.BlockEncoding

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences BlockRows

abbrev Occurrences (h J : ℕ) := Fin J → Occurrence h

def outputOccurrences {h J : ℕ} (q : GlobalOutput h J) : Occurrences h J := fun i => (q i).1

def leftSubset {h J : ℕ} (t : ChoiceTuple h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (edge (t i)).val.1

def rightSubset {h J : ℕ} (t : ChoiceTuple h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (edge (t i)).val.2

def outputSubset {h J : ℕ} (q : GlobalOutput h J) : Finset (Coord J (512 * h)) :=
  flat fun i => (q i).2.val

@[simp] theorem row_leftSubset {h J : ℕ} (t : ChoiceTuple h J) (i : Fin J) :
    row (leftSubset t) i = (edge (t i)).val.1 := row_flat _ _

@[simp] theorem row_rightSubset {h J : ℕ} (t : ChoiceTuple h J) (i : Fin J) :
    row (rightSubset t) i = (edge (t i)).val.2 := row_flat _ _

@[simp] theorem row_outputSubset {h J : ℕ} (q : GlobalOutput h J) (i : Fin J) :
    row (outputSubset q) i = (q i).2.val := row_flat _ _

theorem leftSubset_card {h J : ℕ} (t : ChoiceTuple h J) :
    (leftSubset t).card = J * h := flat_card_of_balance _ (fun i => (edge_data (edge (t i))).1)

theorem rightSubset_card {h J : ℕ} (t : ChoiceTuple h J) :
    (rightSubset t).card = J * h :=
  flat_card_of_balance _ (fun i => (edge_data (edge (t i))).2.1)

theorem outputSubset_card {h J : ℕ} (q : GlobalOutput h J) :
    (outputSubset q).card = J * (2 * h) :=
  flat_card_of_balance _ (fun i => LayerCounts.mem_vertices.mp (q i).2.property)

theorem leftSubset_disjoint_right {h J : ℕ} (t : ChoiceTuple h J) :
    Disjoint (leftSubset t) (rightSubset t) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, x⟩ hL hR
  exact Finset.disjoint_left.mp (edge_data (edge (t i))).2.2
    (mem_flat.mp hL) (mem_flat.mp hR)

theorem leftSubset_union_right {h J : ℕ} (t : ChoiceTuple h J) :
    leftSubset t ∪ rightSubset t = outputSubset (tupleOutput t) := by
  ext ⟨i, x⟩
  simp only [Finset.mem_union, leftSubset, rightSubset, outputSubset, mem_flat,
    tupleOutput, blockOfChoice, output]

theorem rightSubset_eq_sdiff {h J : ℕ} (t : ChoiceTuple h J) :
    rightSubset t = outputSubset (tupleOutput t) \ leftSubset t := by
  rw [← leftSubset_union_right]
  have hd := Finset.disjoint_left.mp (leftSubset_disjoint_right t)
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop

/-- The occurrence and union tuple together with the left subset determine
both endpoints, including all schedule multiplicity tags. -/
theorem tuple_eq_of_output_leftSubset {h J : ℕ} {s t : ChoiceTuple h J}
    (hq : tupleOutput s = tupleOutput t) (hL : leftSubset s = leftSubset t) : s = t := by
  have hR : rightSubset s = rightSubset t := by
    rw [rightSubset_eq_sdiff, rightSubset_eq_sdiff, hq, hL]
  funext i
  apply Subtype.ext
  apply Prod.ext
  · exact congrArg (fun q => (q i).1) hq
  · apply Subtype.ext
    exact Prod.ext (by simpa only [row_leftSubset, edge] using congrArg (fun S => row S i) hL)
      (by simpa only [row_rightSubset, edge] using congrArg (fun S => row S i) hR)

def LeftAllowed {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : Prop :=
  ∀ i, (row S i).card = h ∧
    HashFamily.bucketSize (leftVertices (512 * h) h) (mapAt h (o i))
      (HashFamily.hashValue (mapAt h (o i)) (leftWord (row S i))) ≤ localBucketCap h

def RightAllowed {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : Prop :=
  ∀ i, (row S i).card = h ∧
    HashFamily.bucketSize (rightVertices (512 * h) h) (mapAt h (o i))
      (HashFamily.hashValue (mapAt h (o i)) (rightWord (row S i))) ≤ localBucketCap h

instance {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) :
    Decidable (LeftAllowed o S) := by unfold LeftAllowed; infer_instance

instance {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) :
    Decidable (RightAllowed o S) := by unfold RightAllowed; infer_instance

def endpointLeft {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : ℤ :=
  Radix.positionalHash (localPrime h) id
    (List.ofFn fun i => rawHash (mapAt h (o i)) (leftWord (row S i)))

def endpointRight {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512 * h))) : ℤ :=
  Radix.positionalHash (localPrime h) id
    (List.ofFn fun i => rawHash (mapAt h (o i)) (rightWord (row S i)))

private theorem positionalHash_map {α β : Type*} (p : ℤ) (f : α → β) (g : β → ℤ)
    (xs : List α) : Radix.positionalHash p g (xs.map f) =
      Radix.positionalHash p (fun a => g (f a)) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.map_cons, Radix.positionalHash, ih]

theorem leftAllowed_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : LeftAllowed (outputOccurrences q) (leftSubset t) := by
  intro i
  have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [row_leftSubset] using (edge_data (edge (t i))).1, ?_⟩
  have hs := (retained_survives (t i)).1
  simpa only [row_leftSubset, left, ho] using hs

theorem rightAllowed_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : RightAllowed (outputOccurrences q) (rightSubset t) := by
  intro i
  have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
  refine ⟨by simpa only [row_rightSubset] using (edge_data (edge (t i))).2.1, ?_⟩
  have hs := (retained_survives (t i)).2
  simpa only [row_rightSubset, right, ho] using hs

theorem endpointLeft_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : endpointLeft (outputOccurrences q) (leftSubset t) = tupleLeft t := by
  have hl : (List.ofFn fun i => rawHash (mapAt h (outputOccurrences q i))
      (leftWord (row (leftSubset t) i))) = (List.ofFn t).map rawLeft := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, row_leftSubset, rawLeft, left, ho]
  rw [endpointLeft, hl, positionalHash_map]
  rfl

theorem endpointRight_choice {h J : ℕ} (t : ChoiceTuple h J) (q : GlobalOutput h J)
    (hq : tupleOutput t = q) : endpointRight (outputOccurrences q) (rightSubset t) = tupleRight t := by
  have hl : (List.ofFn fun i => rawHash (mapAt h (outputOccurrences q i))
      (rightWord (row (rightSubset t) i))) = (List.ofFn t).map rawRight := by
    rw [List.map_ofFn]
    apply congrArg List.ofFn
    funext i
    have ho : occurrence (t i) = outputOccurrences q i := congrArg (fun q => (q i).1) hq
    simp only [Function.comp_apply, row_rightSubset, rawRight, right, ho]
  rw [endpointRight, hl, positionalHash_map]
  rfl

/-- Actual retained pairs can be reconstructed from independently trimmed
opposite block subsets. No shared-edge trimming premise is required. -/
def fromSubsets {h J : ℕ} (o : Occurrences h J) (S V : Finset (Coord J (512 * h)))
    (hS : LeftAllowed o S) (hV : RightAllowed o V) (hd : Disjoint S V) : ChoiceTuple h J :=
  fun i => ⟨(o i, ⟨(row S i, row V i), LayerCounts.mem_edgeSet.mpr
    ⟨(hS i).1, (hV i).1, Finset.disjoint_left.mpr (fun _ hx hy =>
      Finset.disjoint_left.mp hd (mem_row.mp hx) (mem_row.mp hy))⟩⟩),
    ⟨(hS i).2, (hV i).2⟩⟩

@[simp] theorem leftSubset_fromSubsets {h J : ℕ} (o : Occurrences h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed o S)
    (hV : RightAllowed o V) (hd : Disjoint S V) :
    leftSubset (fromSubsets o S V hS hV hd) = S := flat_row S

@[simp] theorem rightSubset_fromSubsets {h J : ℕ} (o : Occurrences h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed o S)
    (hV : RightAllowed o V) (hd : Disjoint S V) :
    rightSubset (fromSubsets o S V hS hV hd) = V := flat_row V

theorem output_fromSubsets {h J : ℕ} (q : GlobalOutput h J)
    (S V : Finset (Coord J (512 * h))) (hS : LeftAllowed (outputOccurrences q) S)
    (hV : RightAllowed (outputOccurrences q) V) (hd : Disjoint S V)
    (hu : S ∪ V = outputSubset q) :
    tupleOutput (fromSubsets (outputOccurrences q) S V hS hV hd) = q := by
  funext i
  dsimp only [tupleOutput, blockOfChoice, fromSubsets, occurrence, edge]
  apply Prod.ext
  · rfl
  · apply Subtype.ext
    simpa only [row_union, row_outputSubset, output] using congrArg (fun S => row S i) hu

section Histograms

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftWeights {h J : ℕ} (o : Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ)
    (S : Finset (Coord J (512 * h))) : ℕ :=
  if LeftAllowed o S then
    ∑ j ∈ B, if globalModulus h J ∣ b j % P - endpointLeft o S then 1 else 0
  else 0

def rightWeights {h J : ℕ} (o : Occurrences h J) (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (V : Finset (Coord J (512 * h))) : ℕ :=
  if RightAllowed o V then
    ∑ j ∈ C, if globalModulus h J ∣ c j % P + d - endpointRight o V then 1 else 0
  else 0

theorem leftWeights_cardinality {h J : ℕ} (o : Occurrences h J) (P : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (Coord J (512 * h)))
    (hS : (leftWeights o P B b S : ℤ) ≠ 0) : S.card = J * h := by
  have ha : LeftAllowed o S := by
    by_contra hn
    exact hS (by simp only [leftWeights, hn, ite_false, Nat.cast_zero])
  exact card_of_balanced_rows S (fun i => (ha i).1)

theorem rightWeights_cardinality {h J : ℕ} (o : Occurrences h J) (P d : ℤ)
    (C : Finset γ) (c : γ → ℤ) (V : Finset (Coord J (512 * h)))
    (hV : (rightWeights o P d C c V : ℤ) ≠ 0) : V.card = J * h := by
  have ha : RightAllowed o V := by
    by_contra hn
    exact hV (by simp only [rightWeights, hn, ite_false, Nat.cast_zero])
  exact card_of_balanced_rows V (fun i => (ha i).1)

theorem leftWeights_choice {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    (t : ChoiceTuple h J) (q : GlobalOutput h J) (hq : tupleOutput t = q) :
    leftWeights (outputOccurrences q) P B b (leftSubset t) = leftBucket P B b t := by
  simp only [leftWeights, leftAllowed_choice t q hq, ite_true, endpointLeft_choice t q hq,
    leftBucket]

theorem rightWeights_choice {h J : ℕ} (P d : ℤ) (C : Finset γ) (c : γ → ℤ)
    (t : ChoiceTuple h J) (q : GlobalOutput h J) (hq : tupleOutput t = q) :
    rightWeights (outputOccurrences q) P d C c (rightSubset t) = rightBucket P d C c t := by
  simp only [rightWeights, rightAllowed_choice t q hq, ite_true, endpointRight_choice t q hq,
    rightBucket]

end Histograms

end ThreeSum.BlockEncoding
