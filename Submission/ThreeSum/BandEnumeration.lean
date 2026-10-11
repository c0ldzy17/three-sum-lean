import Submission.ThreeSum.Bands
import Submission.ThreeSum.BinarySearch
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup

/-!
# Enumeration of sorted-band triples through their quadratic owner set

Each owner is inverted with one binary interval lookup.  A final constant-size
test checks relevance and ownership.  No cubic list of triples is formed.
-/

namespace ThreeSum.BandEnumeration

structure Family where
  size : ℕ
  lower : ℕ → ℤ
  upper : ℕ → ℤ
  nonempty : ∀ i < size, lower i ≤ upper i
  sorted : ∀ i j, i ≤ j → j < size → lower i ≤ lower j
  separated : ∀ i j, i < j → j < size → upper i < lower j

namespace Family

abbrev Index (A : Family) := Fin A.size

def lo (A : Family) (i : A.Index) : ℤ := A.lower i
def hi (A : Family) (i : A.Index) : ℤ := A.upper i

def lookup (A : Family) (x : ℤ) : Option A.Index := do
  let i ← BinarySearch.locate A.lower A.upper A.size x
  if h : i < A.size then some ⟨i, h⟩ else none

theorem lookup_complete (A : Family) (x : ℤ) (i : A.Index)
    (hl : A.lo i ≤ x) (hh : x ≤ A.hi i) : A.lookup x = some i := by
  have hlc := BinarySearch.locate_complete A.lower A.upper A.size x
    A.sorted A.separated i.isLt hl hh
  simp [lookup, hlc]

theorem lookup_sound (A : Family) (x : ℤ) (i : A.Index)
    (h : A.lookup x = some i) : A.lo i ≤ x ∧ x ≤ A.hi i := by
  unfold lookup at h
  cases he : BinarySearch.locate A.lower A.upper A.size x with
  | none => simp [he] at h
  | some j =>
      simp only [he] at h
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · have hij : (⟨j, ‹j < A.size›⟩ : A.Index) = i := Option.some.inj h
        subst i
        exact (BinarySearch.locate_sound A.lower A.upper A.size x A.sorted he).2
      · cases h

end Family

open Family

abbrev Triple (A B C : Family) := A.Index × (B.Index × C.Index)
abbrev Owner (A B C : Family) := (B.Index × C.Index) ⊕ (A.Index × (B.Index ⊕ C.Index))

def relevant (A B C : Family) (t : Triple A B C) : Prop :=
  Bands.Relevant A.lo A.hi B.lo B.hi C.lo C.hi t

instance (A B C : Family) (t : Triple A B C) : Decidable (relevant A B C t) :=
  inferInstanceAs (Decidable (Bands.Relevant A.lo A.hi B.lo B.hi C.lo C.hi t))

def owner (A B C : Family) (t : Triple A B C) : Owner A B C :=
  Bands.tripleOwner A.lo B.lo B.hi C.lo t

/-- Exactly one interval lookup for every candidate owner. -/
def candidate (A B C : Family) : Owner A B C → Option (Triple A B C)
  | .inl (j, k) => (A.lookup (C.lo k - B.hi j)).map fun i => (i, j, k)
  | .inr (i, .inl j) => (C.lookup (A.lo i + B.lo j)).map fun k => (i, j, k)
  | .inr (i, .inr k) => (B.lookup (C.lo k - A.lo i)).map fun j => (i, j, k)

theorem candidate_owner (A B C : Family) (t : Triple A B C)
    (ht : relevant A B C t) : candidate A B C (owner A B C t) = some t := by
  rcases t with ⟨i, j, k⟩
  change A.lo i ≤ C.hi k - B.lo j ∧ C.lo k - B.hi j ≤ A.hi i at ht
  unfold owner Bands.tripleOwner
  dsimp only
  by_cases hfirst : A.lo i < C.lo k - B.hi j
  · rw [if_pos hfirst]
    simp only [candidate]
    rw [lookup_complete A _ i (by omega) ht.2]
    rfl
  · rw [if_neg hfirst]
    unfold Bands.overlapOwner
    dsimp only
    by_cases hsecond : A.lo i + B.lo j ≤ C.lo k
    · rw [if_pos hsecond]
      simp only [candidate]
      rw [lookup_complete B _ j (by omega) (by omega)]
      rfl
    · rw [if_neg hsecond]
      simp only [candidate]
      rw [lookup_complete C _ k (by omega) (by omega)]
      rfl

def checkedCandidate (A B C : Family) (o : Owner A B C) : Option (Triple A B C) := do
  let t ← candidate A B C o
  if relevant A B C t ∧ owner A B C t = o then some t else none

theorem checkedCandidate_sound (A B C : Family) (o : Owner A B C)
    {t : Triple A B C} (h : checkedCandidate A B C o = some t) :
    relevant A B C t ∧ owner A B C t = o := by
  unfold checkedCandidate at h
  cases hc : candidate A B C o with
  | none => simp [hc] at h
  | some u =>
      simp only [hc] at h
      dsimp only [Bind.bind, Option.bind] at h
      split at h
      · rename_i hu
        have heq := Option.some.inj h
        subst u
        exact hu
      · cases h

theorem checkedCandidate_complete (A B C : Family) (t : Triple A B C)
    (ht : relevant A B C t) : checkedCandidate A B C (owner A B C t) = some t := by
  simp [checkedCandidate, candidate_owner A B C t ht, ht]

def owners (A B C : Family) : List (Owner A B C) :=
  (List.finRange B.size ×ˢ List.finRange C.size).map
    (fun p => (Sum.inl p : Owner A B C)) ++
  (List.finRange A.size ×ˢ
    ((List.finRange B.size).map (fun j => (Sum.inl j : B.Index ⊕ C.Index)) ++
      (List.finRange C.size).map Sum.inr)).map (fun p => (Sum.inr p : Owner A B C))

theorem mem_owners (A B C : Family) (o : Owner A B C) : o ∈ owners A B C := by
  rcases o with ⟨j, k⟩ | ⟨i, j | k⟩ <;> simp [owners]

theorem owners_length (A B C : Family) :
    (owners A B C).length = B.size * C.size + A.size * (B.size + C.size) := by
  simp [owners, List.length_product]

theorem owners_nodup (A B C : Family) : (owners A B C).Nodup := by
  have hinner : (((List.finRange B.size).map (fun j => (Sum.inl j : B.Index ⊕ C.Index))) ++
      (List.finRange C.size).map Sum.inr).Nodup := by
    apply ((List.nodup_finRange _).map Sum.inl_injective).append
      ((List.nodup_finRange _).map Sum.inr_injective)
    apply List.disjoint_left.mpr
    intro x hx hy
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
    obtain ⟨j, _, heq⟩ := List.mem_map.mp hy
    cases heq
  unfold owners
  apply (((List.nodup_finRange _).product (List.nodup_finRange _)).map
    Sum.inl_injective).append
    (((List.nodup_finRange _).product hinner).map Sum.inr_injective)
  apply List.disjoint_left.mpr
  intro x hx hy
  obtain ⟨i, _, rfl⟩ := List.mem_map.mp hx
  obtain ⟨j, _, heq⟩ := List.mem_map.mp hy
  cases heq

def enumerate (A B C : Family) : List (Triple A B C) :=
  (owners A B C).filterMap (checkedCandidate A B C)

theorem mem_enumerate_iff (A B C : Family) (t : Triple A B C) :
    t ∈ enumerate A B C ↔ relevant A B C t := by
  constructor
  · intro h
    obtain ⟨o, _, heq⟩ := List.mem_filterMap.mp h
    exact (checkedCandidate_sound A B C o heq).1
  · intro h
    exact List.mem_filterMap.mpr ⟨owner A B C t, mem_owners A B C _,
      checkedCandidate_complete A B C t h⟩

theorem enumerate_length_le (A B C : Family) :
    (enumerate A B C).length ≤ B.size * C.size + A.size * (B.size + C.size) := by
  rw [← owners_length A B C]
  exact List.length_filterMap_le _ _

theorem enumerate_nodup (A B C : Family) : (enumerate A B C).Nodup := by
  apply List.Nodup.filterMap _ (owners_nodup A B C)
  intro o o' t ho ho'
  have h := checkedCandidate_sound A B C o (by simpa only [Option.mem_def] using ho)
  have h' := checkedCandidate_sound A B C o' (by simpa only [Option.mem_def] using ho')
  exact h.2.symm.trans h'.2

/-- Every candidate performs one binary lookup of at most this many comparisons. -/
def lookupComparisons (A B C : Family) : Owner A B C → ℕ
  | .inl (j, k) => BinarySearch.comparisons A.lower (C.lo k - B.hi j)
      (Nat.log 2 A.size + 1) 0 A.size
  | .inr (i, .inl j) => BinarySearch.comparisons C.lower (A.lo i + B.lo j)
      (Nat.log 2 C.size + 1) 0 C.size
  | .inr (i, .inr k) => BinarySearch.comparisons B.lower (C.lo k - A.lo i)
      (Nat.log 2 B.size + 1) 0 B.size

theorem lookupComparisons_le (A B C : Family) (o : Owner A B C) :
    lookupComparisons A B C o ≤
      Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1 := by
  rcases o with ⟨j, k⟩ | ⟨i, j | k⟩
  · exact (BinarySearch.comparisons_le _ _ _ _ _).trans (by omega)
  · exact (BinarySearch.comparisons_le _ _ _ _ _).trans (by omega)
  · exact (BinarySearch.comparisons_le _ _ _ _ _).trans (by omega)

/-- The actual lookups over the enumerated owners take O(m² log m)
comparisons.  Constant-size candidate tests add only O(m²) operations. -/
theorem total_lookupComparisons_le (A B C : Family) :
    ((owners A B C).map (lookupComparisons A B C)).sum ≤
      (B.size * C.size + A.size * (B.size + C.size)) *
        (Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1) := by
  let budget := Nat.log 2 A.size + Nat.log 2 B.size + Nat.log 2 C.size + 1
  have hlist : ∀ os : List (Owner A B C),
      (os.map (lookupComparisons A B C)).sum ≤ os.length * budget := by
    intro os
    induction os with
    | nil => simp
    | cons o os ih =>
        have ho := lookupComparisons_le A B C o
        simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.add_mul, Nat.one_mul]
        exact Nat.add_le_add ho ih |>.trans (by omega)
  simpa only [owners_length, budget] using hlist (owners A B C)

end ThreeSum.BandEnumeration
