import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Push
import Mathlib.Tactic.ByContra
import Lean.Elab.Tactic.Omega

/-!
# Finite sparse-query boxes

The largest-missing-element partition and the reusable box recurrence are proved
here as exact finite identities.  The accompanying cardinalities concern the
actual canonical box family, not the family of all arbitrary free-coordinate
subsets.
-/

namespace ThreeSum.SparseBoxes

open scoped BigOperators

variable {α : Type*} [LinearOrder α]

/-- A deterministic selection of the `t` largest elements, by successive maxima. -/
def largest : ℕ → Finset α → Finset α
  | 0, _ => ∅
  | t + 1, m =>
      if hm : m.Nonempty then
        insert (m.max' hm) (largest t (m.erase (m.max' hm)))
      else ∅

/-- A selected set consists of exactly the `t` largest elements of `m`. -/
def IsLargest (t : ℕ) (m u : Finset α) : Prop :=
  u ⊆ m ∧ u.card = t ∧ ∀ a ∈ u, ∀ b ∈ m, b ∉ u → b < a

theorem largest_spec (t : ℕ) (m : Finset α) (h : t ≤ m.card) :
    IsLargest t m (largest t m) := by
  induction t generalizing m with
  | zero => simp [largest, IsLargest]
  | succ t ih =>
      have hm : m.Nonempty := Finset.card_pos.mp (by omega)
      let a := m.max' hm
      have ha : a ∈ m := Finset.max'_mem m hm
      have hcard : (m.erase a).card = m.card - 1 := Finset.card_erase_of_mem ha
      have ht : t ≤ (m.erase a).card := by omega
      obtain ⟨hsub, hsize, horder⟩ := ih (m.erase a) ht
      have hnot : a ∉ largest t (m.erase a) := by
        intro hx
        exact Finset.notMem_erase a m (hsub hx)
      simp only [largest, dif_pos hm]
      change IsLargest (t + 1) m (insert a (largest t (m.erase a)))
      refine ⟨Finset.insert_subset ha (hsub.trans (Finset.erase_subset a m)), ?_, ?_⟩
      · rw [Finset.card_insert_of_notMem hnot, hsize]
      · intro u hu x hx hnx
        have hxa : x ≠ a := by
          intro he
          apply hnx
          simp [he]
        have hxe : x ∈ m.erase a := Finset.mem_erase.mpr ⟨hxa, hx⟩
        rcases Finset.mem_insert.mp hu with hua | hut
        · subst u
          exact Finset.lt_max'_of_mem_erase_max' m hm hxe
        · apply horder u hut x hxe
          intro hxt
          exact hnx (Finset.mem_insert_of_mem hxt)

theorem IsLargest.unique {t : ℕ} {m u v : Finset α}
    (hu : IsLargest t m u) (hv : IsLargest t m v) : u = v := by
  obtain ⟨hum, huc, huo⟩ := hu
  obtain ⟨hvm, hvc, hvo⟩ := hv
  apply Finset.eq_of_subset_of_card_le
  · intro a hau
    by_contra hav
    have hex : ∃ b ∈ v, b ∉ u := by
      by_contra hn
      push Not at hn
      have he : v = u := Finset.eq_of_subset_of_card_le hn (by omega)
      exact hav (he.symm ▸ hau)
    obtain ⟨b, hbv, hbu⟩ := hex
    exact (lt_asymm (huo a hau b (hvm hbv) hbu)) (hvo b hbv a (hum hau) hav)
  · omega

/-- A box contains exactly the subsets between its required and allowed sets. -/
def BoxMember (flags free leaf : Finset α) : Prop :=
  leaf ⊆ flags ∧ flags \ free ⊆ leaf

/-- For a query set and a proposed largest-missing set, free positions lie below
every chosen missing position. -/
def queryFree (q u : Finset α) : Finset α :=
  (q \ u).filter (fun x => ∀ y ∈ u, x < y)

def QueryBox (q u leaf : Finset α) : Prop :=
  BoxMember (q \ u) (queryFree q u) leaf

theorem queryFree_eq_filter_min (q u : Finset α) (hu : u.Nonempty) :
    queryFree q u = (q \ u).filter (fun x => x < u.min' hu) := by
  ext x
  simp only [queryFree, Finset.mem_filter]
  constructor
  · rintro ⟨hx, ho⟩
    exact ⟨hx, ho _ (Finset.min'_mem u hu)⟩
  · rintro ⟨hx, ho⟩
    refine ⟨hx, ?_⟩
    intro y hy
    exact ho.trans_le (Finset.min'_le u y hy)

theorem queryBox_iff_separator (q u leaf : Finset α) (huq : u ⊆ q) :
    QueryBox q u leaf ↔
      leaf ⊆ q ∧ u ⊆ q \ leaf ∧
        ∀ a ∈ u, ∀ x ∈ q \ leaf, x ∉ u → x < a := by
  constructor
  · rintro ⟨hleaf, hrequired⟩
    refine ⟨hleaf.trans Finset.sdiff_subset, ?_, ?_⟩
    · intro a hau
      refine Finset.mem_sdiff.mpr ⟨huq hau, ?_⟩
      intro hal
      exact (Finset.mem_sdiff.mp (hleaf hal)).2 hau
    · intro a hau x hxm hxu
      have hxf : x ∈ q \ u :=
        Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxm).1, hxu⟩
      have hxFree : x ∈ queryFree q u := by
        by_contra hn
        have hxl := hrequired (Finset.mem_sdiff.mpr ⟨hxf, hn⟩)
        exact (Finset.mem_sdiff.mp hxm).2 hxl
      exact (Finset.mem_filter.mp hxFree).2 a hau
  · rintro ⟨hlq, hum, ho⟩
    refine ⟨?_, ?_⟩
    · intro x hxl
      refine Finset.mem_sdiff.mpr ⟨hlq hxl, ?_⟩
      intro hxu
      exact (Finset.mem_sdiff.mp (hum hxu)).2 hxl
    · intro x hx
      obtain ⟨hxf, hxn⟩ := Finset.mem_sdiff.mp hx
      by_contra hxl
      apply hxn
      apply Finset.mem_filter.mpr
      refine ⟨hxf, ?_⟩
      intro a hau
      exact ho a hau x
        (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hxf).1, hxl⟩)
        (Finset.mem_sdiff.mp hxf).2

theorem queryBox_iff_isLargest (q u leaf : Finset α) (t : ℕ)
    (huq : u ⊆ q) (huc : u.card = t) (hlq : leaf ⊆ q) :
    QueryBox q u leaf ↔ IsLargest t (q \ leaf) u := by
  rw [queryBox_iff_separator q u leaf huq]
  simp only [IsLargest, huc, true_and, and_true]
  exact and_iff_right hlq

/-- Every leaf with at least `t` missing coordinates belongs to exactly one
query box, namely the one indexed by its largest `t` missing coordinates. -/
theorem queryBox_partition (q leaf : Finset α) (t : ℕ) (hlq : leaf ⊆ q)
    (ht : t ≤ (q \ leaf).card) :
    ∃! u, u ∈ q.powersetCard t ∧ QueryBox q u leaf := by
  let u := largest t (q \ leaf)
  have hs := largest_spec t (q \ leaf) ht
  have huq : u ⊆ q := hs.1.trans Finset.sdiff_subset
  refine ⟨u, ⟨Finset.mem_powersetCard.mpr ⟨huq, hs.2.1⟩, ?_⟩, ?_⟩
  · exact (queryBox_iff_isLargest q u leaf t huq hs.2.1 hlq).mpr hs
  · intro v hv
    obtain ⟨hvq, hvc⟩ := Finset.mem_powersetCard.mp hv.1
    exact IsLargest.unique
      ((queryBox_iff_isLargest q v leaf t hvq hvc hlq).mp hv.2) hs

/-- Leaves with fewer than `t` missing coordinates occur in no query box. -/
theorem no_queryBox_of_few_missing (q leaf u : Finset α) (t : ℕ)
    (hu : u ∈ q.powersetCard t) (hsmall : (q \ leaf).card < t) :
    ¬ QueryBox q u leaf := by
  intro hb
  obtain ⟨huq, huc⟩ := Finset.mem_powersetCard.mp hu
  have hsub := ((queryBox_iff_separator q u leaf huq).mp hb).2.1
  have hc := Finset.card_le_card hsub
  omega

/-! ## Canonical free prefixes and the finite preprocessing family -/

/-- Free coordinates form an initial segment of the flagged coordinates. -/
def IsInitial (flags free : Finset α) : Prop :=
  free ⊆ flags ∧ ∀ a ∈ free, ∀ b ∈ flags, b < a → b ∈ free

/-- The deterministic initial segment of the indicated size. -/
def smallest (t : ℕ) (flags : Finset α) : Finset α :=
  @largest (OrderDual α) _ t flags

theorem smallest_spec (t : ℕ) (flags : Finset α) (h : t ≤ flags.card) :
    smallest t flags ⊆ flags ∧ (smallest t flags).card = t ∧
      IsInitial flags (smallest t flags) := by
  have hs := @largest_spec (OrderDual α) _ t flags h
  refine ⟨hs.1, hs.2.1, hs.1, ?_⟩
  intro a ha b hb hba
  by_contra hbn
  have hab : a < b := hs.2.2 a ha b hb hbn
  exact (lt_asymm hba) hab

theorem IsInitial.unique {flags u v : Finset α}
    (hu : IsInitial flags u) (hv : IsInitial flags v) (hc : u.card = v.card) :
    u = v := by
  apply Finset.eq_of_subset_of_card_le
  · intro a hau
    by_contra hav
    have hex : ∃ b ∈ v, b ∉ u := by
      by_contra hn
      push Not at hn
      have he : v = u := Finset.eq_of_subset_of_card_le hn (by omega)
      exact hav (he.symm ▸ hau)
    obtain ⟨b, hbv, hbu⟩ := hex
    rcases lt_trichotomy a b with hab | hab | hba
    · exact hav (hv.2 b hbv a (hu.1 hau) hab)
    · subst b
      exact hbu hau
    · exact hbu (hu.2 a hau b (hv.1 hbv) hba)
  · omega

/-- Thus a canonical free set is encoded solely by its cardinality. -/
theorem IsInitial.eq_smallest {flags free : Finset α}
    (h : IsInitial flags free) : free = smallest free.card flags := by
  have hs := smallest_spec free.card flags (Finset.card_le_card h.1)
  exact h.unique hs.2.2 hs.2.1.symm

theorem queryFree_initial (q u : Finset α) :
    IsInitial (q \ u) (queryFree q u) := by
  refine ⟨Finset.filter_subset _ _, ?_⟩
  intro a ha b hb hba
  refine Finset.mem_filter.mpr ⟨hb, ?_⟩
  intro x hx
  exact hba.trans ((Finset.mem_filter.mp ha).2 x hx)

/-- Removing the greatest free coordinate preserves the canonical-family
condition in the included child. -/
theorem IsInitial.erase_max_included {flags free : Finset α}
    (h : IsInitial flags free) (hn : free.Nonempty) :
    IsInitial flags (free.erase (free.max' hn)) := by
  let a := free.max' hn
  refine ⟨(Finset.erase_subset a free).trans h.1, ?_⟩
  intro x hx y hy hyx
  have hxf := Finset.mem_of_mem_erase hx
  have hyf := h.2 x hxf y hy hyx
  have hya : y ≠ a := by
    intro he
    subst y
    have hxa : x ≤ a := Finset.le_max' free x hxf
    exact (not_lt_of_ge hxa) hyx
  exact Finset.mem_erase.mpr ⟨hya, hyf⟩

/-- The excluded child removes that same coordinate from its flags. -/
theorem IsInitial.erase_max_excluded {flags free : Finset α}
    (h : IsInitial flags free) (hn : free.Nonempty) :
    IsInitial (flags.erase (free.max' hn)) (free.erase (free.max' hn)) := by
  let a := free.max' hn
  refine ⟨Finset.erase_subset_erase a h.1, ?_⟩
  intro x hx y hy hyx
  exact Finset.mem_erase.mpr
    ⟨(Finset.mem_erase.mp hy).1,
      h.2 x (Finset.mem_of_mem_erase hx) y (Finset.mem_of_mem_erase hy) hyx⟩

/-- Enumerate only the relevant cardinality layers of subsets. -/
def boundedSubsets (ambient : Finset α) (cut : ℕ) : Finset (Finset α) :=
  (Finset.range (cut + 1)).biUnion (fun j => ambient.powersetCard j)

theorem mem_boundedSubsets (ambient s : Finset α) (cut : ℕ) :
    s ∈ boundedSubsets ambient cut ↔ s ⊆ ambient ∧ s.card ≤ cut := by
  simp only [boundedSubsets, Finset.mem_biUnion, Finset.mem_range, Finset.mem_powersetCard]
  constructor
  · rintro ⟨j, hj, hs, hc⟩
    exact ⟨hs, by omega⟩
  · rintro ⟨hs, hc⟩
    exact ⟨s.card, by omega, hs, rfl⟩

theorem boundedSubsets_eq_filter (ambient : Finset α) (cut : ℕ) :
    boundedSubsets ambient cut = ambient.powerset.filter (fun s => s.card ≤ cut) := by
  ext s
  simp only [mem_boundedSubsets, Finset.mem_filter, Finset.mem_powerset]

/-- Actual record indices: a flagged set of at most `cut` elements, and an
integer from zero to its size. Its free set is constructed by `smallest`. -/
def records (ambient : Finset α) (cut : ℕ) :
    Finset (Sigma (fun _ : Finset α => ℕ)) :=
  (boundedSubsets ambient cut).sigma
    (fun flags => Finset.range (flags.card + 1))

theorem mem_records (ambient flags : Finset α) (cut e : ℕ) :
    (⟨flags, e⟩ : Sigma (fun _ : Finset α => ℕ)) ∈ records ambient cut ↔
      flags ⊆ ambient ∧ flags.card ≤ cut ∧ e ≤ flags.card := by
  simp [records, boundedSubsets_eq_filter, Finset.mem_powerset, Nat.lt_succ_iff, and_assoc]

theorem records_card (ambient : Finset α) (cut : ℕ) :
    (records ambient cut).card =
      ∑ flags ∈ ambient.powerset with flags.card ≤ cut, (flags.card + 1) := by
  simp only [records, boundedSubsets_eq_filter, Finset.card_sigma, Finset.card_range]

theorem records_card_layers (ambient : Finset α) (cut : ℕ) :
    (records ambient cut).card =
      ∑ j ∈ Finset.range (ambient.card + 1),
        if j ≤ cut then (j + 1) * ambient.card.choose j else 0 := by
  rw [records_card, Finset.sum_filter, Finset.sum_powerset]
  apply Finset.sum_congr rfl
  intro j hj
  have hconst :
      (∑ flags ∈ ambient.powersetCard j,
        if flags.card ≤ cut then flags.card + 1 else 0) =
      ∑ _flags ∈ ambient.powersetCard j, if j ≤ cut then j + 1 else 0 := by
    apply Finset.sum_congr rfl
    intro flags hf
    rw [(Finset.mem_powersetCard.mp hf).2]
  rw [hconst]
  by_cases hjc : j ≤ cut
  · simp [hjc, Nat.mul_comm]
  · simp [hjc]

private theorem choose_mono_below_half {n i j : ℕ}
    (hij : i ≤ j) (hj : j ≤ n / 2) : n.choose i ≤ n.choose j := by
  induction j generalizing i with
  | zero =>
      have hi : i = 0 := by omega
      simp [hi]
  | succ j ih =>
      by_cases he : i = j + 1
      · simp [he]
      · have hij' : i ≤ j := by omega
        have hj' : j ≤ n / 2 := by omega
        exact (ih hij' hj').trans (Nat.choose_le_succ_of_lt_half_left (by omega))

/-- The complete box-family size is a polynomial factor times its final
binomial layer, as used in the written preprocessing bound. -/
theorem records_card_bound (ambient : Finset α) (cut : ℕ)
    (hcut : cut ≤ ambient.card / 2) :
    (records ambient cut).card ≤
      (ambient.card + 1) ^ 2 * ambient.card.choose cut := by
  rw [records_card_layers]
  calc
    _ ≤ ∑ _j ∈ Finset.range (ambient.card + 1),
          (ambient.card + 1) * ambient.card.choose cut := by
      apply Finset.sum_le_sum
      intro j hj
      by_cases hjc : j ≤ cut
      · simp only [hjc, ite_true]
        exact Nat.mul_le_mul
          (by have hh := Nat.div_le_self ambient.card 2; omega)
          (choose_mono_below_half hjc hcut)
      · simp only [hjc, ite_false]
        exact Nat.zero_le _
    _ = _ := by simp [pow_two, Nat.mul_assoc]

/-! ## The exact addition recurrence and query sum -/

instance (flags free leaf : Finset α) : Decidable (BoxMember flags free leaf) := by
  unfold BoxMember
  infer_instance

instance (q u leaf : Finset α) : Decidable (QueryBox q u leaf) := by
  unfold QueryBox
  infer_instance

/-- The signed sum stored in one box record. -/
def boxSum (flags free : Finset α) (weight : Finset α → ℤ) : ℤ :=
  ∑ leaf ∈ flags.powerset, if flags \ free ⊆ leaf then weight leaf else 0

theorem boxSum_extend (ambient flags free : Finset α) (weight : Finset α → ℤ)
    (hf : flags ⊆ ambient) :
    boxSum flags free weight =
      ∑ leaf ∈ ambient.powerset,
        if BoxMember flags free leaf then weight leaf else 0 := by
  unfold boxSum
  calc
    _ = ∑ leaf ∈ flags.powerset,
          if BoxMember flags free leaf then weight leaf else 0 := by
      apply Finset.sum_congr rfl
      intro leaf hl
      simp only [BoxMember, Finset.mem_powerset.mp hl, true_and]
    _ = _ := by
      apply Finset.sum_subset
      · intro leaf hl
        exact Finset.mem_powerset.mpr ((Finset.mem_powerset.mp hl).trans hf)
      · intro leaf hl hnl
        have hn : ¬ BoxMember flags free leaf := by
          intro h
          exact hnl (Finset.mem_powerset.mpr h.1)
        simp only [hn, ite_false]

/-- A record with no free positions is the original leaf value. -/
theorem boxSum_empty (flags : Finset α) (weight : Finset α → ℤ) :
    boxSum flags ∅ weight = weight flags := by
  unfold boxSum
  simp only [Finset.sdiff_empty]
  rw [Finset.sum_eq_single flags]
  · simp
  · intro leaf hl hne
    have hn : ¬ flags ⊆ leaf := by
      intro hfl
      apply hne
      ext x
      exact ⟨fun hx => (Finset.mem_powerset.mp hl) hx, fun hx => hfl hx⟩
    simp only [hn, ite_false]
  · intro h
    exact False.elim (h (Finset.mem_powerset.mpr (Finset.Subset.refl flags)))

/-- Resolving one free flag is exactly one addition of an included child and an
excluded child. The theorem applies to arbitrary signed leaf values. -/
theorem boxSum_resolve (flags free : Finset α) (weight : Finset α → ℤ)
    (a : α) (hfree : free ⊆ flags) (ha : a ∈ free) :
    boxSum flags free weight =
      boxSum flags (free.erase a) weight +
      boxSum (flags.erase a) (free.erase a) weight := by
  have haf : a ∈ flags := hfree ha
  have hdinc : flags \ free.erase a = insert a (flags \ free) := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [haf]
    · simp [hxa]
  have hdexc : flags.erase a \ free.erase a = flags \ free := by
    ext x
    by_cases hxa : x = a
    · subst x
      simp [ha]
    · simp [hxa]
  have hinc : boxSum flags (free.erase a) weight =
      ∑ leaf ∈ flags.powerset,
        if flags \ free ⊆ leaf ∧ a ∈ leaf then weight leaf else 0 := by
    unfold boxSum
    rw [hdinc]
    apply Finset.sum_congr rfl
    intro leaf hl
    simp only [Finset.insert_subset_iff, and_comm]
  have hexc : boxSum (flags.erase a) (free.erase a) weight =
      ∑ leaf ∈ flags.powerset,
        if flags \ free ⊆ leaf ∧ a ∉ leaf then weight leaf else 0 := by
    unfold boxSum
    rw [hdexc]
    calc
      _ = ∑ leaf ∈ (flags.erase a).powerset,
            if flags \ free ⊆ leaf ∧ a ∉ leaf then weight leaf else 0 := by
        apply Finset.sum_congr rfl
        intro leaf hl
        have han : a ∉ leaf := by
          intro hal
          exact Finset.notMem_erase a flags ((Finset.mem_powerset.mp hl) hal)
        simp only [han, not_false_eq_true, and_true]
      _ = _ := by
        apply Finset.sum_subset
        · intro leaf hl
          exact Finset.mem_powerset.mpr
            ((Finset.mem_powerset.mp hl).trans (Finset.erase_subset a flags))
        · intro leaf hl hnl
          have hal : a ∈ leaf := by
            by_contra han
            apply hnl
            apply Finset.mem_powerset.mpr
            intro x hx
            refine Finset.mem_erase.mpr ⟨?_, (Finset.mem_powerset.mp hl) hx⟩
            intro he
            subst x
            exact han hx
          simp only [hal, not_true_eq_false, and_false, ite_false]
  rw [hinc, hexc, ← Finset.sum_add_distrib]
  unfold boxSum
  apply Finset.sum_congr rfl
  intro leaf hl
  by_cases hr : flags \ free ⊆ leaf <;> by_cases hal : a ∈ leaf <;> simp [hr, hal]

theorem resolved_children_in_records (ambient flags free : Finset α) (cut : ℕ)
    (hfa : flags ⊆ ambient) (hcut : flags.card ≤ cut)
    (hinit : IsInitial flags free) (hn : free.Nonempty) :
    let a := free.max' hn
    (⟨flags, (free.erase a).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈ records ambient cut ∧
    (⟨flags.erase a, (free.erase a).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈
      records ambient cut ∧
    (free.erase a).card < free.card := by
  dsimp
  have hi := hinit.erase_max_included hn
  have he := hinit.erase_max_excluded hn
  refine ⟨(mem_records ambient flags cut _).mpr ⟨hfa, hcut, Finset.card_le_card hi.1⟩,
    (mem_records ambient (flags.erase _) cut _).mpr
      ⟨(Finset.erase_subset _ flags).trans hfa,
        (Finset.card_le_card (Finset.erase_subset _ flags)).trans hcut,
        Finset.card_le_card he.1⟩, ?_⟩
  rw [Finset.card_erase_of_mem (Finset.max'_mem free hn)]
  have hp := Finset.card_pos.mpr hn
  omega

/-- Every box generated by a query belongs to the preprocessed canonical family
at cutoff `q.card-t`. Its free coordinates are reconstructed from their size. -/
theorem query_record (ambient q u : Finset α) (t : ℕ)
    (hqa : q ⊆ ambient) (hu : u ∈ q.powersetCard t) :
    (⟨q \ u, (queryFree q u).card⟩ : Sigma (fun _ : Finset α => ℕ)) ∈
      records ambient (q.card - t) ∧
    queryFree q u = smallest (queryFree q u).card (q \ u) := by
  obtain ⟨huq, huc⟩ := Finset.mem_powersetCard.mp hu
  have hi := queryFree_initial q u
  refine ⟨(mem_records ambient (q \ u) (q.card - t) _).mpr
    ⟨Finset.sdiff_subset.trans hqa, ?_, Finset.card_le_card hi.1⟩, hi.eq_smallest⟩
  rw [Finset.card_sdiff_of_subset huq, huc]

private theorem query_fiber_sum (q leaf : Finset α) (t : ℕ)
    (weight : Finset α → ℤ) (hl : leaf ∈ q.powerset) :
    (∑ u ∈ q.powersetCard t, if QueryBox q u leaf then weight leaf else 0) =
      if (q \ leaf).card < t then 0 else weight leaf := by
  by_cases hs : (q \ leaf).card < t
  · simp only [hs, ite_true]
    apply Finset.sum_eq_zero
    intro u hu
    simp only [no_queryBox_of_few_missing q leaf u t hu hs, ite_false]
  · have ht : t ≤ (q \ leaf).card := by omega
    obtain ⟨u, hu, huniq⟩ := queryBox_partition q leaf t (Finset.mem_powerset.mp hl) ht
    rw [Finset.sum_eq_single u]
    · simp [hu.2, hs]
    · intro v hv hvn
      have hn : ¬ QueryBox q v leaf := by
        intro hb
        exact hvn (huniq v ⟨hv, hb⟩)
      simp only [hn, ite_false]
    · intro h
      exact False.elim (h hu.1)

/-- The full query partition as an exact signed-sum identity: explicit leaves
with fewer than `t` missing positions, plus one lookup per `t`-subset. -/
theorem sparse_query_identity (q : Finset α) (t : ℕ) (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ q.powerset with (q \ leaf).card < t, weight leaf) +
      ∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight := by
  have hboxes :
      (∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight) =
      ∑ leaf ∈ q.powerset, if (q \ leaf).card < t then 0 else weight leaf := by
    calc
      _ = ∑ u ∈ q.powersetCard t, ∑ leaf ∈ q.powerset,
            if QueryBox q u leaf then weight leaf else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact boxSum_extend q (q \ u) (queryFree q u) weight Finset.sdiff_subset
      _ = ∑ leaf ∈ q.powerset, ∑ u ∈ q.powersetCard t,
            if QueryBox q u leaf then weight leaf else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro leaf hl
        exact query_fiber_sum q leaf t weight hl
  rw [hboxes, Finset.sum_filter, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro leaf hl
  by_cases h : (q \ leaf).card < t <;> simp [h]

/-! ## Number of query accesses -/

def explicitLeaves (q : Finset α) (t : ℕ) : Finset (Finset α) :=
  ((Finset.range t).biUnion (fun j => q.powersetCard j)).image (fun missing => q \ missing)

theorem mem_explicitLeaves (q leaf : Finset α) (t : ℕ) :
    leaf ∈ explicitLeaves q t ↔ leaf ⊆ q ∧ (q \ leaf).card < t := by
  constructor
  · intro hl
    obtain ⟨missing, hm, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨j, hj, hmj⟩ := Finset.mem_biUnion.mp hm
    obtain ⟨hmq, hmc⟩ := Finset.mem_powersetCard.mp hmj
    refine ⟨Finset.sdiff_subset, ?_⟩
    rw [Finset.sdiff_sdiff_eq_self hmq, hmc]
    exact Finset.mem_range.mp hj
  · rintro ⟨hlq, hsmall⟩
    apply Finset.mem_image.mpr
    refine ⟨q \ leaf, ?_, Finset.sdiff_sdiff_eq_self hlq⟩
    exact Finset.mem_biUnion.mpr
      ⟨(q \ leaf).card, Finset.mem_range.mpr hsmall,
        Finset.mem_powersetCard.mpr ⟨Finset.sdiff_subset, rfl⟩⟩

theorem explicitLeaves_eq_filter (q : Finset α) (t : ℕ) :
    explicitLeaves q t = q.powerset.filter (fun leaf => (q \ leaf).card < t) := by
  ext leaf
  simp only [mem_explicitLeaves, Finset.mem_filter, Finset.mem_powerset]

private theorem explicitLeaves_card_le_records (q : Finset α) (t : ℕ) :
    (explicitLeaves q t).card ≤ (records q t).card := by
  apply Finset.card_le_card_of_injOn
    (fun leaf => (⟨q \ leaf, 0⟩ : Sigma (fun _ : Finset α => ℕ)))
  · intro leaf hl
    obtain ⟨hlq, hsmall⟩ := (mem_explicitLeaves q leaf t).mp hl
    exact (mem_records q (q \ leaf) t 0).mpr
      ⟨Finset.sdiff_subset, Nat.le_of_lt hsmall, Nat.zero_le _⟩
  · intro a ha b hb he
    have hqa := ((mem_explicitLeaves q a t).mp ha).1
    have hqb := ((mem_explicitLeaves q b t).mp hb).1
    have hc : q \ a = q \ b := congrArg (fun r : Sigma (fun _ : Finset α => ℕ) => r.1) he
    calc
      a = q \ (q \ a) := (Finset.sdiff_sdiff_eq_self hqa).symm
      _ = q \ (q \ b) := congrArg (fun s => q \ s) hc
      _ = b := Finset.sdiff_sdiff_eq_self hqb

/-- The exact query identity uses at most a polynomial factor times `choose(mu,t)`
leaf evaluations and box lookups. The work-item domains above enumerate just
the required cardinality layers. -/
theorem sparse_query_access_bound (q : Finset α) (t : ℕ) (ht : t ≤ q.card / 2) :
    (explicitLeaves q t).card + (q.powersetCard t).card ≤
      ((q.card + 1) ^ 2 + 1) * q.card.choose t := by
  have hsmall := (explicitLeaves_card_le_records q t).trans (records_card_bound q t ht)
  rw [Finset.card_powersetCard]
  calc
    _ ≤ (q.card + 1) ^ 2 * q.card.choose t + q.card.choose t :=
      Nat.add_le_add_right hsmall _
    _ = _ := by rw [Nat.add_mul, one_mul]

/-- Query identity using the cardinality-layer enumeration of explicit leaves. -/
theorem sparse_query_identity_enumerated (q : Finset α) (t : ℕ)
    (weight : Finset α → ℤ) :
    (∑ leaf ∈ q.powerset, weight leaf) =
      (∑ leaf ∈ explicitLeaves q t, weight leaf) +
      ∑ u ∈ q.powersetCard t, boxSum (q \ u) (queryFree q u) weight := by
  simpa only [explicitLeaves_eq_filter] using sparse_query_identity q t weight

end ThreeSum.SparseBoxes
