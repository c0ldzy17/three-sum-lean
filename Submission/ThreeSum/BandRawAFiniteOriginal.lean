import Submission.ThreeSum.BandRawAFiniteSlices
import Submission.ThreeSum.BandRawAOriginal

/-! # Original-value soundness and completeness on the bounded reporting domain -/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset

set_option maxHeartbeats 1200000
set_option maxRecDepth 7000

theorem finite_product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record}
    {t : Fin (items A.length g rs).length × Fin B.length × Fin C.length}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ finiteAllProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1.val ∈ originalA ∧
      B.getD t.2.1.val 0 ∈ originalB ∧ C.getD t.2.2.val 0 ∈ originalC :=
  product_original_values hA hB hC (mem_finiteAllProducts.mp ht)

theorem finite_original_equation_complete {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ finiteAllProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1.val=a ∧ B.getD t.2.1.val 0=b ∧ C.getD t.2.2.val 0=c := by
  obtain ⟨t,ht,hvalues⟩ := original_equation_complete hg hsA hsB hsC hA hB hC ha hb hc heq
  obtain ⟨u,hu,he⟩ := finite_lift ht
  refine ⟨u,hu,?_⟩
  change valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
    (fun i => A.getD i 0) (coordinates u).1=a ∧
      B.getD (coordinates u).2.1 0=b ∧ C.getD (coordinates u).2.2 0=c
  rw [he]
  exact hvalues

theorem finite_original_equation_sound {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record}
    {t : Fin (items A.length g rs).length × Fin B.length × Fin C.length}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ finiteAllProducts A.length B.length C.length g rs)
    (heq : valueAt A.length g rs (fun i => A.getD i 0) t.1.val+
      B.getD t.2.1.val 0=C.getD t.2.2.val 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c :=
  original_equation_sound hA hB hC (mem_finiteAllProducts.mp ht) heq

end ThreeSum.BandRawA
