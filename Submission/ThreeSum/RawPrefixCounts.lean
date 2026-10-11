import Submission.ThreeSum.RawReporting

/-!
# Exact bucket products at a wanted reporting prefix

The raw fiber used by the reporting theorem is here expanded into independently
counted B and C buckets. The wanted query fixes its original A index, lift,
and all chosen-map occurrences and output subsets.
-/

namespace ThreeSum.RawPrefixCounts

set_option maxRecDepth 8000

open Finset
open scoped BigOperators
open GlobalEncoding RawIncidences RawReporting

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def prefixItems {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :=
  (domain I w).filter fun r => (word r).take k = pre

theorem prefixQuery_eq_card {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :
    prefixQuery I w k pre = (prefixItems I w k pre).card := by
  simp only [prefixQuery, Reporting.mass, Subset.fiberMass, prefixItems,
    Finset.sum_const, smul_eq_mul, mul_one]

def compatiblePairs {h J : ℕ} (P d : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (t : ChoiceTuple h J) :=
  (B ×ˢ C).filter fun p => globalModulus h J ∣ b p.1 % P - tupleLeft t ∧
    globalModulus h J ∣ c p.2 % P + d - tupleRight t

def completions {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512 * h)))) : Finset (ChoiceTuple h J) :=
  Finset.univ.filter fun t => tupleOutput t = q ∧ (partitionWord t).take k = pre

private def pack {h J : ℕ} (w : Wanted h J α)
    (s : Σ _t : ChoiceTuple h J, β × γ) : RawItem h J α β γ :=
  ⟨(w.1, s.2), (s.1, w.2.1)⟩

private theorem pack_injective {h J : ℕ} (w : Wanted h J α) :
    Function.Injective (pack (β := β) (γ := γ) w) := by
  intro s t he
  apply Sigma.ext
  · exact congrArg (fun r => r.2.1) he
  · exact heq_of_eq (congrArg (fun r => r.1.2) he)

private theorem pack_unpack {h J : ℕ} (w : Wanted h J α) (r : RawItem h J α β γ)
    (hw : wantedOf r = w) : pack w ⟨r.2.1, r.1.2⟩ = r := by
  rw [← hw]
  rfl

private theorem pack_mem_prefixItems {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h))))
    (s : Σ _t : ChoiceTuple h J, β × γ) :
    pack w s ∈ prefixItems (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre ↔
      (w.1 ∈ A ∧ globalModulus h J ∣
        (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2) ∧
      s.1 ∈ completions w.2.2 k pre ∧ s.2 ∈ compatiblePairs P d B C b c s.1 := by
  constructor
  · intro hr
    obtain ⟨hd, hpre⟩ := Finset.mem_filter.mp hr
    obtain ⟨hraw, hw⟩ := Finset.mem_filter.mp hd
    obtain ⟨hm, hrep, hkey⟩ := (mem_rawOn.mp hraw).imp_right mem_witnesses.mp
    have hq : tupleOutput s.1 = w.2.2 := congrArg (fun z => z.2.2) hw
    have hke : tupleKey s.1 = globalKey w.2.2 := congrArg globalKey hq
    have hpair := (tuple_mem_representations s.1 (b s.2.1 % P)
      (c s.2.2 % P + d)).mp hrep
    have hm' : w.1 ∈ A ∧ s.2 ∈ B ×ˢ C := Finset.mem_product.mp hm
    refine ⟨⟨hm'.1, ?_⟩, ?_, ?_⟩
    · simpa only [pack, hke] using hkey
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq, hpre⟩
    · exact Finset.mem_filter.mpr ⟨hm'.2, hpair⟩
  · rintro ⟨⟨ha, hkey⟩, ht, hp⟩
    obtain ⟨_, hq, hpre⟩ := Finset.mem_filter.mp ht
    obtain ⟨hm, hpair⟩ := Finset.mem_filter.mp hp
    have hke : tupleKey s.1 = globalKey w.2.2 := congrArg globalKey hq
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_filter.mpr ⟨?_, ?_⟩, hpre⟩
    · apply mem_rawOn.mpr
      refine ⟨Finset.mem_product.mpr ⟨ha, hm⟩, mem_witnesses.mpr ⟨?_, ?_⟩⟩
      · exact (tuple_mem_representations s.1 _ _).mpr hpair
      · simpa only [pack, hke] using hkey
    · exact Prod.ext rfl (Prod.ext rfl hq)

/-- The query first checks the fixed A key. Its remaining natural mass is
exactly a sum of products of the original-index B and C bucket sizes. -/
def bucketPrefixMass {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) : ℕ :=
  if w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % P + lift w.2.1 * P + d) - globalKey w.2.2 then
    ∑ t ∈ completions w.2.2 k pre, leftBucket P B b t * rightBucket P d C c t
  else 0

theorem prefixQuery_eq_bucketPrefixMass {h J : ℕ} (P d : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (k : ℕ) (pre : List (Finset (Fin (512 * h)))) :
    prefixQuery (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre =
      bucketPrefixMass P d A B C a b c w k pre := by
  rw [prefixQuery_eq_card, bucketPrefixMass]
  split
  next hguard =>
    let pairs := (completions w.2.2 k pre).sigma fun t => compatiblePairs P d B C b c t
    have he : pairs.card =
        (prefixItems (rawOn h J P d (A ×ˢ (B ×ˢ C)) a b c) w k pre).card := by
      apply Finset.card_bij (fun s _ => pack w s)
      · intro s hs
        exact (pack_mem_prefixItems P d A B C a b c w k pre s).mpr
          ⟨hguard, (Finset.mem_sigma.mp hs).1, (Finset.mem_sigma.mp hs).2⟩
      · intro s _ t _ he
        exact pack_injective w he
      · intro r hr
        have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
        let s : Σ _t : ChoiceTuple h J, β × γ := ⟨r.2.1, r.1.2⟩
        have he : pack w s = r := pack_unpack w r hw
        refine ⟨s, ?_, he⟩
        have hs := (pack_mem_prefixItems P d A B C a b c w k pre s).mp (he ▸ hr)
        exact Finset.mem_sigma.mpr hs.2
    rw [← he, Finset.card_sigma]
    apply Finset.sum_congr rfl
    intro t _
    exact (bucket_product_eq_card P d B C b c t).symm
  next hguard =>
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro r hr
    have hw := (Finset.mem_filter.mp (Finset.mem_filter.mp hr).1).2
    have he := pack_unpack w r hw
    have hs := (pack_mem_prefixItems P d A B C a b c w k pre ⟨r.2.1, r.1.2⟩).mp
      (he ▸ hr)
    exact hguard hs.1

end Indices

end ThreeSum.RawPrefixCounts
