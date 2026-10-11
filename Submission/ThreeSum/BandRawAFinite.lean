import Submission.ThreeSum.BandRawAScore

/-!
# Bounded finite index types for the same physical owner products

The A type is the complete flattened incidence array; B and C are the
retained sorted arrays. Coordinate transport is injective and preserves
both each owner's product and its exact weighted collision score.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset
open scoped BigOperators

set_option maxHeartbeats 2000000
set_option maxRecDepth 8000

def coordinates {a b c : ℕ} (t : Fin a × Fin b × Fin c) : ℕ × ℕ × ℕ :=
  (t.1.val,t.2.1.val,t.2.2.val)

def finiteAIndices (n g : ℕ) (rs : List Record) (s : ℕ) :
    Finset (Fin (items n g rs).length) :=
  univ.filter fun i => i.val ∈ aIndices n g rs s

def finiteBandPositions (n g a : ℕ) : Finset (Fin n) :=
  univ.filter fun i => i.val ∈ bandPositions n g a

def finiteOwnerProduct (nA nB nC g : ℕ) (rs : List Record) (s : ℕ) :
    Finset (Fin (items nA g rs).length × Fin nB × Fin nC) :=
  finiteAIndices nA g rs s ×ˢ (finiteBandPositions nB g (rs.getD s default).b ×ˢ
    finiteBandPositions nC g (rs.getD s default).c)

def finiteAllProducts (nA nB nC g : ℕ) (rs : List Record) :
    Finset (Fin (items nA g rs).length × Fin nB × Fin nC) :=
  univ.filter fun t => coordinates t ∈ allProducts nA nB nC g rs

theorem coordinates_injective {a b c : ℕ} :
    Function.Injective (@coordinates a b c) := by
  rintro ⟨i,j,k⟩ ⟨i',j',k'⟩ he
  simp only [coordinates,Prod.mk.injEq] at he
  exact Prod.ext (Fin.ext he.1) (Prod.ext (Fin.ext he.2.1) (Fin.ext he.2.2))

@[simp] theorem mem_finiteAIndices {n g s : ℕ} {rs : List Record}
    {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ i.val ∈ aIndices n g rs s := by
  simp only [finiteAIndices,mem_filter,mem_univ,true_and]

@[simp] theorem mem_finiteBandPositions {n g a : ℕ} {i : Fin n} :
    i ∈ finiteBandPositions n g a ↔ i.val ∈ bandPositions n g a := by
  simp only [finiteBandPositions,mem_filter,mem_univ,true_and]

@[simp] theorem mem_finiteOwnerProduct {nA nB nC g s : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteOwnerProduct nA nB nC g rs s ↔
      coordinates t ∈ ownerProduct nA nB nC g rs s := by
  simp only [finiteOwnerProduct,ownerProduct,mem_product,mem_finiteAIndices,
    mem_finiteBandPositions,coordinates]

@[simp] theorem mem_finiteAllProducts {nA nB nC g : ℕ} {rs : List Record}
    {t : Fin (items nA g rs).length × Fin nB × Fin nC} :
    t ∈ finiteAllProducts nA nB nC g rs ↔
      coordinates t ∈ allProducts nA nB nC g rs := by
  simp only [finiteAllProducts,mem_filter,mem_univ,true_and]

theorem finiteAIndices_owner {n g s : ℕ} {rs : List Record}
    (hs : s < rs.length) {i : Fin (items n g rs).length} :
    i ∈ finiteAIndices n g rs s ↔ (labelAt n g rs i.val).owner=s := by
  rw [mem_finiteAIndices,mem_aIndices_iff_owner hs]
  simp only [i.isLt,true_and]

theorem ownerProduct_bounds {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) (ht : t ∈ ownerProduct nA nB nC g rs s) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,_,hb,hc⟩ := (mem_ownerProduct hs).mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩

theorem allProducts_bounds {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    t.1 < (items nA g rs).length ∧ t.2.1 < nB ∧ t.2.2 < nC := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  exact ⟨ha,bandPositions_lt hb,bandPositions_lt hc⟩

theorem finite_owner_lift {nA nB nC g s : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hs : s < rs.length) (ht : t ∈ ownerProduct nA nB nC g rs s) :
    ∃ u ∈ finiteOwnerProduct nA nB nC g rs s, coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := ownerProduct_bounds hs ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact mem_finiteOwnerProduct.mpr ht

theorem finite_lift {nA nB nC g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts nA nB nC g rs) :
    ∃ u ∈ finiteAllProducts nA nB nC g rs, coordinates u=t := by
  obtain ⟨ha,hb,hc⟩ := allProducts_bounds ht
  refine ⟨(⟨t.1,ha⟩,⟨t.2.1,hb⟩,⟨t.2.2,hc⟩),?_,rfl⟩
  exact mem_finiteAllProducts.mpr ht

theorem sum_finiteOwnerProduct (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    (∑ u ∈ finiteOwnerProduct nA nB nC g rs s, F (coordinates u))=
      ∑ t ∈ ownerProduct nA nB nC g rs s, F t := by
  refine sum_bij (fun u _ => coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact mem_finiteOwnerProduct.mp hu
  · intro u hu v hv he
    exact coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := finite_owner_lift hs ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl

theorem sum_finiteAllProducts (F : (ℕ × ℕ × ℕ) → ℕ) (nA nB nC g : ℕ)
    (rs : List Record) :
    (∑ u ∈ finiteAllProducts nA nB nC g rs, F (coordinates u))=
      ∑ t ∈ allProducts nA nB nC g rs, F t := by
  refine sum_bij (fun u _ => coordinates u) ?_ ?_ ?_ ?_
  · intro u hu
    exact mem_finiteAllProducts.mp hu
  · intro u hu v hv he
    exact coordinates_injective he
  · intro t ht
    obtain ⟨u,hu,he⟩ := finite_lift ht
    exact ⟨u,hu,he⟩
  · intro u hu
    rfl

theorem finiteOwner_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) {s : ℕ} (hs : s < rs.length) :
    Arithmetic.weightedFalseCount (finiteOwnerProduct nA nB nC g rs s)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.block primes aux q nA nB nC g A B C (rs.getD s default) := by
  rw [← owner_weightedFalseCount primes aux q nA nB nC g A B C rs hs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteOwnerProduct
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs hs

theorem finiteAll_weightedFalseCount (primes : ℕ → ℕ) (aux q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    Arithmetic.weightedFalseCount (finiteAllProducts nA nB nC g rs)
      (fun t => C t.2.2.val-B t.2.1.val-valueAt nA g rs A t.1.val)
      (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux)) q=
      BandWeightedScore.score primes aux q nA nB nC g A B C rs := by
  rw [← all_weightedFalseCount primes aux q nA nB nC g A B C rs]
  unfold Arithmetic.weightedFalseCount
  exact sum_finiteAllProducts
    (fun t => if (q : ℤ) ∣ ModuloCounts.difference (valueAt nA g rs A) B C t then
      Arithmetic.missWeight (Auxiliary.moduli (WeightedScore.auxiliarySet primes aux))
        (ModuloCounts.difference (valueAt nA g rs A) B C t) else 0) nA nB nC g rs

theorem finiteAllProducts_eq_union (nA nB nC g : ℕ) (rs : List Record) :
    finiteAllProducts nA nB nC g rs=
      (range rs.length).biUnion (finiteOwnerProduct nA nB nC g rs) := by
  ext t
  simp only [mem_finiteAllProducts,allProducts,mem_biUnion,mem_finiteOwnerProduct]

theorem finiteOwnerProduct_disjoint {nA nB nC g s t : ℕ} {rs : List Record}
    (hs : s < rs.length) (ht : t < rs.length) (hne : s ≠ t) :
    Disjoint (finiteOwnerProduct nA nB nC g rs s) (finiteOwnerProduct nA nB nC g rs t) := by
  apply disjoint_left.mpr
  intro u hu hv
  exact disjoint_left.mp (ownerProduct_disjoint hs ht hne)
    (mem_finiteOwnerProduct.mp hu) (mem_finiteOwnerProduct.mp hv)

end ThreeSum.BandRawA
