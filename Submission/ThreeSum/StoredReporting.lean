import Submission.ThreeSum.BlockForced

/-!
# Exact stored-subset queries for the concrete reporting tree

A malformed prefix has zero mass. Every valid prefix is evaluated by the
stored suffix-zeta stages and the signed subset formula. These values are
proved to equal the natural raw-incidence fiber counts at every tree node.
-/

namespace ThreeSum.StoredReporting

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding LocalGraph LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open BlockRows BlockEncoding BlockForced

private theorem ofFn_take_eq_iff {α : Type*} {J k : ℕ} (f g : Fin J → α) :
    (List.ofFn f).take k = (List.ofFn g).take k ↔ ∀ i : Fin J, i.val < k → f i = g i := by
  constructor
  · intro he i hi
    have hh := congrArg (fun xs => xs[i.val]?) he
    simpa only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos i.isLt,
      Option.some.injEq] using hh
  · intro h
    apply List.ext_getElem?
    intro i
    by_cases hi : i < k
    · rw [List.getElem?_take_of_lt hi, List.getElem?_take_of_lt hi]
      by_cases hiJ : i < J
      · simp only [List.getElem?_ofFn, dif_pos hiJ, h ⟨i, hiJ⟩ hi]
      · simp only [List.getElem?_ofFn, dif_neg hiJ]
    · simp only [List.getElem?_take, hi, ite_false]

def prefixRows {J L : ℕ} (pre : List (Finset (Fin L))) : Fin J → Finset (Fin L) :=
  fun i => pre[i.val]?.getD ∅

theorem prefixRows_take {J L k : ℕ} (u : Fin J → Finset (Fin L)) (i : Fin J)
    (hi : i.val < k) : prefixRows ((List.ofFn u).take k) i = u i := by
  simp only [prefixRows, List.getElem?_take_of_lt hi, List.getElem?_ofFn,
    dif_pos i.isLt, Option.getD_some]

theorem take_prefixRows {J L k : ℕ} (pre : List (Finset (Fin L)))
    (hp : pre.length = k) (hk : k ≤ J) : (List.ofFn (prefixRows (J := J) pre)).take k = pre := by
  apply List.ext_getElem?
  intro i
  by_cases hi : i < k
  · have hiJ : i < J := hi.trans_le hk
    have hip : i < pre.length := hp ▸ hi
    simp only [List.getElem?_take_of_lt hi, List.getElem?_ofFn, dif_pos hiJ, prefixRows,
      List.getElem?_eq_getElem hip, Option.getD_some]
  · rw [List.getElem?_take_eq_none (Nat.le_of_not_lt hi),
      List.getElem?_eq_none (by omega)]

theorem completions_eq_completedTuples {h J k : ℕ} (q : GlobalOutput h J)
    (u : Fin J → Finset (Fin (512 * h))) :
    completions q k ((List.ofFn u).take k) = completedTuples q (prefixIndices J k) u := by
  ext t
  simp only [completions, completedTuples, Finset.mem_filter, Finset.mem_univ, true_and,
    partitionWord, ofFn_take_eq_iff, mem_prefixIndices]

def ValidPrefix {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Prop :=
  pre.length = k ∧ ∀ i : Fin J, i.val < k →
    prefixRows pre i ⊆ outputRows q i ∧ (prefixRows pre i).card = h

instance {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Decidable (ValidPrefix q k pre) := by
  unfold ValidPrefix
  infer_instance

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem positivePrefix_valid {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J)
    (hp : 0 < prefixQuery I w k pre) : ValidPrefix w.2.2 k pre := by
  obtain ⟨r, hr, hpre, _⟩ := (Reporting.mass_pos_iff (domain I w) word (fun _ => 1) k pre).mp hp
  have hw := (Finset.mem_filter.mp hr).2
  have hq : tupleOutput r.2.1 = w.2.2 := congrArg (fun w => w.2.2) hw
  constructor
  · rw [← hpre, List.length_take, word, partitionWord_length, Nat.min_eq_left hk]
  · intro i hi
    have hrows : prefixRows pre i = (edge (r.2.1 i)).val.1 := by
      rw [← hpre]
      exact prefixRows_take (fun j => (edge (r.2.1 j)).val.1) i hi
    rw [hrows]
    refine ⟨?_, (edge_data (edge (r.2.1 i))).1⟩
    have he : output (edge (r.2.1 i)) = outputRows w.2.2 i :=
      congrArg (fun q => (q i).2.val) hq
    rw [← he]
    exact Finset.subset_union_left

/-- A signed subset query, with the inexpensive validity and fixed A-key
checks displayed explicitly. Its natural value is established below. -/
def storedQueryValue {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℤ :=
  if ValidPrefix w.2.2 k pre then
    if w.1 ∈ A ∧ globalModulus h J ∣
        (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2 then
      transformPrefixValue P d B C b c w.2.2 (prefixIndices J k) (prefixRows pre)
    else 0
  else 0

theorem storedQueryValue_eq_prefixQuery {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    storedQueryValue P d A B C a b c w k pre =
      (prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) := by
  unfold storedQueryValue
  split
  next hp =>
    have hpre := take_prefixRows (J := J) pre hp.1 hk
    have he := transformPrefixValue_eq_bucket_sum P d B C b c w.2.2
      (prefixIndices J k) (prefixRows pre) (fun i hi => hp.2 i (mem_prefixIndices.mp hi))
    rw [prefixQuery_eq_bucketPrefixMass, bucketPrefixMass]
    by_cases hkey : w.1 ∈ A ∧ globalModulus h J ∣
        (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2
    · simp only [hkey, ite_true]
      rw [← completions_eq_completedTuples, hpre] at he
      exact he
    · simp only [hkey, ite_false, Nat.cast_zero]
  next hp =>
    have hz : prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre = 0 := by
      by_contra hn
      exact hp (positivePrefix_valid _ w pre hk (Nat.pos_of_ne_zero hn))
    simp only [hz, Nat.cast_zero]

def storedQuery {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  (storedQueryValue P d A B C a b c w k pre).toNat

theorem storedQuery_eq_prefixQuery {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    storedQuery P d A B C a b c w k pre =
      prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre := by
  rw [storedQuery, storedQueryValue_eq_prefixQuery P d A B C a b c w pre hk]
  exact Int.toNat_natCast _

private theorem frontier_congr_query {δ : Type*} (children : ℕ → List δ)
    (Q R : ℕ → List δ → ℕ) (k : ℕ)
    (h : ∀ j ≤ k, ∀ pre, Q j pre = R j pre) :
    Reporting.frontier children Q k = Reporting.frontier children R k := by
  induction k with
  | zero => simp only [Reporting.frontier, h 0 le_rfl []]
  | succ k ih =>
    simp only [Reporting.frontier]
    rw [ih (fun j hj pre => h j (by omega) pre)]
    congr 1
    funext pre
    rw [h (k + 1) le_rfl pre]

def storedFrontier {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α) (k : ℕ) :=
  Reporting.frontier (children w.2.2) (storedQuery P d A B C a b c w) k

theorem storedFrontier_eq {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α) (hk : k ≤ J) :
    storedFrontier P d A B C a b c w k =
      RawReporting.frontier (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k := by
  apply frontier_congr_query
  intro j hj pre
  exact storedQuery_eq_prefixQuery P d A B C a b c w pre (hj.trans hk)

theorem storedFrontier_mem_iff {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512 * h)))) (hk : k ≤ J) :
    pre ∈ storedFrontier P d A B C a b c w k ↔
      ∃ r ∈ rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c,
        wantedOf r = w ∧ (word r).take k = pre := by
  rw [storedFrontier_eq P d A B C a b c w hk]
  exact RawReporting.mem_frontier_iff _ w hk pre

/-- The actual query formula discharges the reporting interface. Summed
positive frontiers, over every A/lift/occurrence/Q wanted key, cost at most
the original raw mass at each depth. -/
theorem total_storedFrontier_length_le_rawMass {h J k : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hk : k ≤ J) :
    (∑ w : Wanted h J α, (storedFrontier P d A B C a b c w k).length) ≤
      rawMass h J P d (A ×ˢ (B ×ˢ C)) a b c := by
  simpa only [storedFrontier_eq P d A B C a b c _ hk] using
    RawReporting.total_frontier_length_le_rawMass P d (A ×ˢ (B ×ˢ C)) a b c hk

theorem true_original_stored_reported {h J : ℕ} {P d : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (hh : 0 < h) (hP : 0 < P)
    (t : Original α β γ) (ht : t ∈ A ×ˢ (B ×ˢ C)) (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c, r.1 = t ∧
      word r ∈ storedFrontier P d A B C a b c (wantedOf r) J := by
  obtain ⟨r, hr, hrt, hp⟩ := RawReporting.true_original_reported
    (A ×ˢ (B ×ˢ C)) a b c hh hP t ht he
  exact ⟨r, hr, hrt, (storedFrontier_eq P d A B C a b c (wantedOf r) le_rfl).symm ▸ hp⟩

end Indices

end ThreeSum.StoredReporting
