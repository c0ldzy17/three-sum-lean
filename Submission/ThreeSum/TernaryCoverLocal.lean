import Submission.ThreeSum.TernaryJointType
import Submission.ThreeSum.TernaryCoverTrimming
import Submission.ThreeSum.TernaryCoverFibers
import Submission.ThreeSum.TernaryCoverRetained

/-!
# The genuine fixed-type trinary graph and its tagged hash experiment

Edges contain the two endpoint words and their ordinary, coordinatewise
sum.  Their sum is uniquely determined by the endpoints.  In particular,
the graph retains every partition admitted by the endpoint/output types.
This module instantiates the proved tagged-hash first moment.  It does not
claim the still-separate higher-rank moment or good-map frequency theorem.
-/

noncomputable section

namespace ThreeSum.TernaryCoverLocal

open Finset TernaryJointType TernaryCoverHashes
open scoped BigOperators

variable {L p : ℕ}

def edgeSet (L : ℕ) (α π : DigitType) : Finset (TritWord L × TritWord L × TritWord L) := by
  classical
  exact univ.filter fun e => Edge α π e.1 e.2.1 e.2.2

abbrev LocalEdge (L : ℕ) (α π : DigitType) := {e // e ∈ edgeSet L α π}

def left {α π : DigitType} (e : LocalEdge L α π) : TritWord L := e.val.1
def right {α π : DigitType} (e : LocalEdge L α π) : TritWord L := e.val.2.1
def output {α π : DigitType} (e : LocalEdge L α π) : TritWord L := e.val.2.2

theorem edge_data {α π : DigitType} (e : LocalEdge L α π) :
    Edge α π (left e) (right e) (output e) := by
  classical
  exact (mem_filter.mp e.property).2

theorem endpoint_injective (α π : DigitType) :
    Function.Injective (fun e : LocalEdge L α π => (left e, right e)) := by
  intro e f he
  have hl : left e = left f := congrArg (fun z : TritWord L × TritWord L => z.1) he
  have hr : right e = right f := congrArg (fun z : TritWord L × TritWord L => z.2) he
  have hq : output e = output f := by
    funext i
    apply Fin.ext
    have hs := (edge_data e).2.2.2 i
    have ht := (edge_data f).2.2.2 i
    rw [hl, hr] at hs
    exact hs.symm.trans ht
  apply Subtype.ext
  exact Prod.ext hl (Prod.ext hr hq)

def vertices (L : ℕ) (α : DigitType) : Finset (TritWord L) := by
  classical
  exact univ.filter fun w => HasType w α

theorem left_mem_vertices {α π : DigitType} (e : LocalEdge L α π) :
    left e ∈ vertices L α := by
  classical
  exact mem_filter.mpr ⟨mem_univ _, (edge_data e).1⟩

theorem right_mem_vertices {α π : DigitType} (e : LocalEdge L α π) :
    right e ∈ vertices L α := by
  classical
  exact mem_filter.mpr ⟨mem_univ _, (edge_data e).2.1⟩

def fieldVertices (L p : ℕ) (α : DigitType) : Finset (Fin L → ZMod p) := by
  classical
  exact (vertices L α).image (fieldWord p)

theorem fieldVertices_card (α : DigitType) (hp : 2 < p) :
    (fieldVertices L p α).card = (vertices L α).card := by
  classical
  exact card_image_of_injective _ (fieldWord_injective hp)

def fieldLeft {α π : DigitType} (e : LocalEdge L α π) : Fin L → ZMod p :=
  fieldWord p (left e)

def fieldRight {α π : DigitType} (e : LocalEdge L α π) : Fin L → ZMod p :=
  fieldWord p (right e)

theorem fieldLeft_mem {α π : DigitType} (e : LocalEdge L α π) :
    fieldLeft (p := p) e ∈ fieldVertices L p α := by
  exact mem_image.mpr ⟨left e, left_mem_vertices e, rfl⟩

theorem fieldRight_mem {α π : DigitType} (e : LocalEdge L α π) :
    fieldRight (p := p) e ∈ fieldVertices L p α := by
  exact mem_image.mpr ⟨right e, right_mem_vertices e, rfl⟩

theorem field_endpoint_injective (α π : DigitType) (hp : 2 < p) :
    Function.Injective (fun e : LocalEdge L α π => (fieldLeft (p := p) e, fieldRight (p := p) e)) := by
  intro e f he
  apply endpoint_injective α π
  exact Prod.ext (fieldWord_injective hp (congrArg Prod.fst he))
    (fieldWord_injective hp (congrArg Prod.snd he))

variable [Fact (Nat.Prime p)]

def leftHash {α π : DigitType} (w : Coordinate (Fin L) → ZMod p)
    (e : LocalEdge L α π) : ZMod p :=
  linearHash (leftVector (fieldLeft e)) w

def rightHash {α π : DigitType} (w : Coordinate (Fin L) → ZMod p)
    (e : LocalEdge L α π) : ZMod p :=
  linearHash (rightVector (fieldRight e)) w

def outputHash (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) : ZMod p :=
  linearHash (outputVector (fieldWord p q)) w

theorem hashes_add {α π : DigitType} (w : Coordinate (Fin L) → ZMod p)
    (e : LocalEdge L α π) : leftHash w e + rightHash w e = outputHash w (output e) := by
  have hv := vector_sum (fieldWord_sum (p := p) (edge_data e).2.2.2)
  unfold leftHash rightHash outputHash linearHash fieldLeft fieldRight
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro i _
  have hi := congrFun hv i
  dsimp at hi
  rw [← hi, add_mul]

def trimmedEvents (α π : DigitType) (B : ℕ) (a b : ZMod p)
    (e : LocalEdge L α π) : Finset (Coordinate (Fin L) → ZMod p) :=
  TernaryCoverTrimming.trimmedPairEvent (fieldLeft e) (fieldRight e) a b
    (fieldVertices L p α) (fieldVertices L p α) B

def hitCount (α π : DigitType) (B : ℕ) (w : Coordinate (Fin L) → ZMod p)
    (a b : ZMod p) : ℕ :=
  HashFamily.incidenceCount (trimmedEvents α π B a b) w

/-- The actual fixed-type graph retains at least three quarters of its
raw first moment.  No joint-type or graph independence hypothesis occurs. -/
theorem first_moment (α π : DigitType) (B : ℕ) (a b : ZMod p)
    (hB : 8 * (p + (fieldVertices L p α).card) ≤ B * p) :
    3 * Fintype.card (LocalEdge L α π) * Fintype.card (Coordinate (Fin L) → ZMod p) ≤
      4 * p ^ 2 * (∑ w : Coordinate (Fin L) → ZMod p, hitCount α π B w a b) := by
  unfold hitCount
  rw [HashFamily.sum_incidenceCount, mul_sum]
  calc
    _ = ∑ _e : LocalEdge L α π,
        3 * Fintype.card (Coordinate (Fin L) → ZMod p) := by simp; ring
    _ ≤ _ := by
      apply sum_le_sum
      intro e _
      have h := TernaryCoverTrimming.trimmedPairEvent_bound
        (fieldLeft (p := p) e) (fieldRight (p := p) e) a b
        (fieldVertices L p α) (fieldVertices L p α) B
        (by simpa using hB) (by simpa using hB)
      simpa [trimmedEvents] using h

/-- The retained fiber cap is obtained from actual light endpoint buckets. -/
theorem hitCount_cap (α π : DigitType) (B : ℕ)
    (w : Coordinate (Fin L) → ZMod p) (a b : ZMod p) (hp : 2 < p) :
    hitCount α π B w a b ≤ B ^ 2 := by
  classical
  let F : Finset (LocalEdge L α π) := univ.filter fun e => w ∈ trimmedEvents α π B a b e
  change F.card ≤ B ^ 2
  by_cases hz : F.card = 0
  · simp [hz]
  obtain ⟨e, he⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero hz)
  have hlights :
      TernaryCoverTrimming.bucketSize (fieldVertices L p α) leftVector w a ≤ B ∧
      TernaryCoverTrimming.bucketSize (fieldVertices L p α) rightVector w b ≤ B :=
    (mem_filter.mp (mem_filter.mp he).2).2
  have hsub : F ⊆ TernaryCoverRetained.hits (fieldLeft (p := p)) (fieldRight (p := p))
      (fun x => linearHash (leftVector x) w) (fun y => linearHash (rightVector y) w) a b := by
    intro f hf
    have ht := (mem_filter.mp hf).2
    have hh := (mem_filter.mp (mem_filter.mp ht).1).2
    exact mem_filter.mpr ⟨mem_univ _, hh⟩
  exact (card_le_card hsub).trans
    (TernaryCoverRetained.hits_card_le_sq (fieldLeft (p := p)) (fieldRight (p := p))
      (fun x => linearHash (leftVector x) w) (fun y => linearHash (rightVector y) w)
      (fieldVertices L p α) (fieldVertices L p α) (field_endpoint_injective α π hp)
      fieldLeft_mem fieldRight_mem a b B hlights.1 hlights.2)

/-- This is the maximum full ordered fiber over all literal target pairs.
The definition is finite; no claim about its size is made here. -/
def rawCap (α π : DigitType) (w : Coordinate (Fin L) → ZMod p) : ℕ := by
  classical
  exact (univ : Finset (ZMod p × ZMod p)).sup fun t =>
    TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) t.1 t.2

theorem rawPairCount_le_rawCap (α π : DigitType)
    (w : Coordinate (Fin L) → ZMod p) (a b : ZMod p) :
    TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) a b ≤
      rawCap α π w := by
  classical
  unfold rawCap
  exact Finset.le_sup (f := fun t : ZMod p × ZMod p =>
    TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) t.1 t.2)
    (mem_univ (a,b))

theorem rawCap_le_iff (α π : DigitType) (w : Coordinate (Fin L) → ZMod p) (τ : ℕ) :
    rawCap α π w ≤ τ ↔ ∀ a b : ZMod p,
      TernaryCoverFibers.rawPairCount (leftHash (α := α) (π := π) w) (rightHash w) a b ≤ τ := by
  classical
  constructor
  · intro h a b
    exact (rawPairCount_le_rawCap α π w a b).trans h
  · intro h
    unfold rawCap
    apply Finset.sup_le
    intro t _
    exact h t.1 t.2

end ThreeSum.TernaryCoverLocal
