import Submission.ThreeSum.BlockEncoding

/-!
# Actual forced-prefix endpoint decompositions

Fixing completed blocks partitions each full retained tuple into its fixed
left/right subsets and its remaining left subset. The reconstruction is a
bijection, which identifies every prefix bucket sum with the subset formula.
-/

namespace ThreeSum.BlockForced

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding

section FiniteRows

variable {J L : ℕ}

def prefixLeft (I : Finset (Fin J)) (u : Fin J → Finset (Fin L)) := join I u

def prefixRight (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L)) :=
  join I fun i => Q i \ u i

def remaining (I : Finset (Fin J)) (Q : Fin J → Finset (Fin L)) := join Iᶜ Q

def suffixDomain (I : Finset (Fin J)) : Finset (Coord J L) := join Iᶜ fun _ => univ

private theorem suffix_not_prefix {I : Finset (Fin J)} {Q : Fin J → Finset (Fin L)}
    {x : Finset (Coord J L)} (hx : x ⊆ remaining I Q) {i : Fin J} (hi : i ∈ I)
    (a : Fin L) : Sigma.mk i a ∉ x := by
  intro ha
  exact (Finset.mem_compl.mp (mem_join.mp (hx ha)).1) hi

theorem forced_union (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (hu : ∀ i ∈ I, u i ⊆ Q i) (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    (prefixLeft I u ∪ x) ∪ (prefixRight I Q u ∪ (remaining I Q \ x)) = flat Q := by
  ext ⟨i, a⟩
  by_cases hi : i ∈ I
  · have hn := suffix_not_prefix hx hi a
    have hs := hu i hi
    simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, mem_flat, hi, not_true_eq_false,
      true_and, false_and, or_false, false_or, hn]
    constructor
    · rintro (ha | ⟨ha, _⟩)
      · exact hs ha
      · exact ha
    · intro ha
      by_cases hau : a ∈ u i
      · exact Or.inl hau
      · exact Or.inr ⟨ha, hau⟩
  · have hs : Sigma.mk i a ∈ x → a ∈ Q i := fun ha => (mem_join.mp (hx ha)).2
    simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, mem_flat, hi, not_false_eq_true,
      true_and, false_and, or_false, false_or]
    constructor
    · rintro (ha | ⟨ha, _⟩)
      · exact hs ha
      · exact ha
    · intro ha
      by_cases hax : Sigma.mk i a ∈ x
      · exact Or.inl hax
      · exact Or.inr ⟨ha, hax⟩

theorem forced_disjoint (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    Disjoint (prefixLeft I u ∪ x) (prefixRight I Q u ∪ (remaining I Q \ x)) := by
  apply Finset.disjoint_left.mpr
  intro ⟨i, a⟩ hL hR
  by_cases hi : i ∈ I
  · have hn := suffix_not_prefix hx hi a
    simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, hi, not_true_eq_false, true_and,
      false_and, or_false, false_or, hn] at hL hR
    exact hR.2 hL
  · simp only [prefixLeft, prefixRight, remaining, mem_join, Finset.mem_union,
      Finset.mem_sdiff, Finset.mem_compl, hi, not_false_eq_true, true_and,
      false_and, or_false, false_or] at hL hR
    exact hR.2 hL

theorem row_forced_prefix (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) {i : Fin J} (hi : i ∈ I) :
    row (prefixLeft I u ∪ x) i = u i := by
  ext a
  simp only [mem_row, Finset.mem_union, prefixLeft, mem_join, hi, true_and,
    suffix_not_prefix hx hi a, or_false]

theorem suffix_forced_prefix (I : Finset (Fin J)) (Q u : Fin J → Finset (Fin L))
    (x : Finset (Coord J L)) (hx : x ⊆ remaining I Q) :
    join Iᶜ (row (prefixLeft I u ∪ x)) = x := by
  ext ⟨i, a⟩
  by_cases hi : i ∈ I
  · simp only [mem_join, Finset.mem_compl, hi, not_true_eq_false, false_and,
      suffix_not_prefix hx hi a]
  · simp only [mem_join, Finset.mem_compl, hi, not_false_eq_true, true_and,
      mem_row, Finset.mem_union, prefixLeft, mem_join, false_and, false_or]

theorem forced_left_of_agreement (I : Finset (Fin J)) (u v : Fin J → Finset (Fin L))
    (hv : ∀ i ∈ I, v i = u i) :
    prefixLeft I u ∪ join Iᶜ v = flat v := by
  have he : join I u = join I v := by
    ext ⟨i, a⟩
    by_cases hi : i ∈ I
    · simp only [mem_join, hi, true_and, hv i hi]
    · simp only [mem_join, hi, false_and]
  rw [prefixLeft, he]
  exact join_union_compl I v

private theorem sdiff_of_disjoint_union {S V Q : Finset (Coord J L)}
    (hd : Disjoint S V) (hu : S ∪ V = Q) : V = Q \ S := by
  rw [← hu]
  have hd' := Finset.disjoint_left.mp hd
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_union]
  aesop

end FiniteRows

def outputRows {h J : ℕ} (q : GlobalOutput h J) : Fin J → Finset (Fin (512 * h)) :=
  fun i => (q i).2.val

def completedTuples {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : Finset (ChoiceTuple h J) :=
  univ.filter fun t => tupleOutput t = q ∧ ∀ i ∈ I, (edge (t i)).val.1 = u i

def residual {h J : ℕ} (I : Finset (Fin J)) (t : ChoiceTuple h J) :=
  join Iᶜ fun i => (edge (t i)).val.1

theorem residual_subset {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (t : ChoiceTuple h J) (hq : tupleOutput t = q) : residual I t ⊆ remaining I (outputRows q) := by
  have hL : leftSubset t ⊆ outputSubset q := by
    rw [← hq, ← leftSubset_union_right]
    exact Finset.subset_union_left
  intro ⟨i, a⟩ hx
  obtain ⟨hi, ha⟩ := mem_join.mp hx
  apply mem_join.mpr
  refine ⟨hi, ?_⟩
  have hh := row_subset hL i
  simp only [row_leftSubset, row_outputSubset] at hh
  exact hh ha

theorem forced_left_completion {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) : prefixLeft I u ∪ residual I t = leftSubset t :=
  forced_left_of_agreement I u _ (Finset.mem_filter.mp ht).2.2

theorem forced_right_completion {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) :
    prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ residual I t) =
      rightSubset t := by
  have hq := (Finset.mem_filter.mp ht).2.1
  have hx := residual_subset q I t hq
  have he := sdiff_of_disjoint_union (forced_disjoint I (outputRows q) u (residual I t) hx)
    (forced_union I (outputRows q) u hu (residual I t) hx)
  rw [he, forced_left_completion q I u t ht, rightSubset_eq_sdiff, hq]
  rfl

def admissibleResiduals {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : Finset (Finset (Coord J (512 * h))) :=
  (remaining I (outputRows q)).powerset.filter fun x =>
    LeftAllowed (outputOccurrences q) (prefixLeft I u ∪ x) ∧
    RightAllowed (outputOccurrences q)
      (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x))

theorem residual_mem {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i) (t : ChoiceTuple h J)
    (ht : t ∈ completedTuples q I u) : residual I t ∈ admissibleResiduals q I u := by
  have hq := (Finset.mem_filter.mp ht).2.1
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_powerset.mpr (residual_subset q I t hq), ?_⟩
  rw [forced_left_completion q I u t ht, forced_right_completion q I u hu t ht]
  exact ⟨leftAllowed_choice t q hq, rightAllowed_choice t q hq⟩

theorem residual_injective {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) :
    Set.InjOn (residual (h := h) I) (↑(completedTuples q I u) : Set (ChoiceTuple h J)) := by
  intro s hs t ht he
  apply tuple_eq_of_output_leftSubset
  · exact (Finset.mem_filter.mp hs).2.1.trans (Finset.mem_filter.mp ht).2.1.symm
  · rw [← forced_left_completion q I u s hs, ← forced_left_completion q I u t ht, he]

theorem residual_surjective {h J : ℕ} (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (hu : ∀ i ∈ I, u i ⊆ outputRows q i)
    (x : Finset (Coord J (512 * h))) (hx : x ∈ admissibleResiduals q I u) :
    ∃ t ∈ completedTuples q I u, residual I t = x := by
  obtain ⟨hx, hL, hR⟩ := Finset.mem_filter.mp hx
  have hxs := Finset.mem_powerset.mp hx
  let S := prefixLeft I u ∪ x
  let V := prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)
  have hd : Disjoint S V := forced_disjoint I (outputRows q) u x hxs
  let t := fromSubsets (outputOccurrences q) S V hL hR hd
  have hq : tupleOutput t = q := output_fromSubsets q S V hL hR hd
    (forced_union I (outputRows q) u hu x hxs)
  have hleft : leftSubset t = S := leftSubset_fromSubsets _ _ _ _ _ _
  refine ⟨t, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, ?_⟩, ?_⟩
  · intro i hi
    have he := congrArg (fun S => row S i) hleft
    simpa only [row_leftSubset, S, row_forced_prefix I (outputRows q) u x hxs hi] using he
  · change join Iᶜ (fun i => (edge (t i)).val.1) = x
    have he : (fun i => (edge (t i)).val.1) = row S := by
      funext i
      simpa only [row_leftSubset] using congrArg (fun S => row S i) hleft
    rw [he]
    exact suffix_forced_prefix I (outputRows q) u x hxs

section WeightedCounts

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

theorem completed_bucket_sum {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) (hu : ∀ i ∈ I, u i ⊆ outputRows q i) :
    (∑ t ∈ completedTuples q I u, leftBucket P B b t * rightBucket P d C c t) =
      ∑ x ∈ (remaining I (outputRows q)).powerset,
        leftWeights (outputOccurrences q) P B b (prefixLeft I u ∪ x) *
        rightWeights (outputOccurrences q) P d C c
          (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)) := by
  calc
    _ = ∑ x ∈ admissibleResiduals q I u,
        leftWeights (outputOccurrences q) P B b (prefixLeft I u ∪ x) *
        rightWeights (outputOccurrences q) P d C c
          (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x)) := by
      apply Finset.sum_bij (fun t _ => residual I t)
      · exact residual_mem q I u hu
      · intro s hs t ht he
        exact residual_injective q I u hs ht he
      · intro x hx
        obtain ⟨t, ht, he⟩ := residual_surjective q I u hu x hx
        exact ⟨t, ht, he⟩
      · intro t ht
        have hq := (Finset.mem_filter.mp ht).2.1
        rw [forced_left_completion q I u t ht, forced_right_completion q I u hu t ht,
          leftWeights_choice P B b t q hq, rightWeights_choice P d C c t q hq]
    _ = _ := by
      rw [admissibleResiduals, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hL : LeftAllowed (outputOccurrences q) (prefixLeft I u ∪ x)
      · by_cases hR : RightAllowed (outputOccurrences q)
            (prefixRight I (outputRows q) u ∪ (remaining I (outputRows q) \ x))
        · simp only [hL, hR, and_self, ite_true]
        · simp only [hL, hR, and_false, ite_false, rightWeights, mul_zero]
      · simp only [hL, false_and, ite_false, leftWeights, zero_mul]

/-- The stored suffix stages evaluated by the signed subset query. -/
def transformPrefixValue {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h))) : ℤ :=
  Subset.mobius (fun z =>
    Subset.partialZeta (suffixDomain I)
      (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ)) (prefixLeft I u ∪ z) *
    Subset.partialZeta (suffixDomain I)
      (fun V => (rightWeights (outputOccurrences q) P d C c V : ℤ))
      (prefixRight I (outputRows q) u ∪ z))
    (remaining I (outputRows q))

/-- This is the actual forced-prefix identity: all support, size and
reconstruction hypotheses are discharged by the concrete block encoding. -/
theorem transformPrefixValue_eq_bucket_sum {h J : ℕ} (P d : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalOutput h J) (I : Finset (Fin J))
    (u : Fin J → Finset (Fin (512 * h)))
    (hu : ∀ i ∈ I, u i ⊆ outputRows q i ∧ (u i).card = h) :
    transformPrefixValue P d B C b c q I u =
      (∑ t ∈ completedTuples q I u, leftBucket P B b t * rightBucket P d C c t : ℕ) := by
  have hQ : ∀ i, (outputRows q i).card = 2 * h :=
    fun i => LayerCounts.mem_vertices.mp (q i).2.property
  have he := Subset.forced_prefix_identity
    (fun S => (leftWeights (outputOccurrences q) P B b S : ℤ))
    (fun V => (rightWeights (outputOccurrences q) P d C c V : ℤ))
    (prefixLeft I u) (prefixRight I (outputRows q) u) (suffixDomain I)
    (remaining I (outputRows q)) (J * h) (J * h)
    (leftWeights_cardinality (outputOccurrences q) P B b)
    (rightWeights_cardinality (outputOccurrences q) P d C c)
    (join_disjoint_compl I u (fun _ => univ))
    (join_disjoint_compl I (fun i => outputRows q i \ u i) (fun _ => univ))
    (join_subset Iᶜ (fun _ _ => Finset.subset_univ _))
    (forced_sizes I (outputRows q) u hQ hu)
  rw [transformPrefixValue, he]
  exact_mod_cast (completed_bucket_sum P d B C b c q I u (fun i hi => (hu i hi).1)).symm

end WeightedCounts

end ThreeSum.BlockForced
