import Submission.ThreeSum.BandRawAFiniteOriginal
import Submission.ThreeSum.ColorClassLists

/-!
# Distinct original-position semantics of the finite owner catalog

Incidence coordinates remain physical coordinates in the flattened A row.
Original input indices are recovered from retained class membership. Their
different colors prove that the three recovered positions are distinct,
even when the input contains repeated values.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows ColorClassLists

set_option maxHeartbeats 1500000
set_option maxRecDepth 8000

def finiteEquation (A B C : List ℤ) (g : ℕ) (rs : List Record) : Prop :=
  ∃ t ∈ finiteAllProducts A.length B.length C.length g rs,
    valueAt A.length g rs (fun i => A.getD i 0) t.1.val+
      B.getD t.2.1.val 0=C.getD t.2.2.val 0

theorem finite_color_positions {n W g : ℕ} {A B C : List ℤ} {rs : List Record}
    (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hA : ∀ z, z ∈ A ↔ z ∈ classList p x 0 1)
    (hB : ∀ z, z ∈ B ↔ z ∈ classList p x 1 1)
    (hC : ∀ z, z ∈ C ↔ z ∈ classList p x 2 (-1))
    {t : Fin (items A.length g rs).length × Fin B.length × Fin C.length}
    (ht : t ∈ finiteAllProducts A.length B.length C.length g rs)
    (heq : valueAt A.length g rs (fun i => A.getD i 0) t.1.val+
      B.getD t.2.1.val 0=C.getD t.2.2.val 0) :
    ∃ i j k : Fin n, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      indexColor p i=0 ∧ indexColor p j=1 ∧ indexColor p k=2 ∧
      x i=valueAt A.length g rs (fun q => A.getD q 0) t.1.val ∧
      x j=B.getD t.2.1.val 0 ∧ -x k=C.getD t.2.2.val 0 ∧
      x i+x j+x k=0 := by
  obtain ⟨ha,hb,hc⟩ := finite_product_original_values hA hB hC ht
  obtain ⟨i,hi,hxi⟩ := (Coloring.mem_values x (indexColor p) 0 _).mp
    ((mem_classList p x (0 : Fin 3) _).mp ha)
  obtain ⟨j,hj,hxj⟩ := (Coloring.mem_values x (indexColor p) 1 _).mp
    ((mem_classList p x (1 : Fin 3) _).mp hb)
  obtain ⟨k,hk,hxk⟩ := (Coloring.mem_negValues x (indexColor p) _).mp
    ((mem_negClassList p x _).mp hc)
  refine ⟨i,j,k,?_,?_,?_,hi,hj,hk,hxi,hxj,hxk,?_⟩
  · intro he; subst j; simp_all
  · intro he; subst k; simp_all
  · intro he; subst k; simp_all
  · omega

theorem finite_color_sound {n W g : ℕ} {A B C : List ℤ} {rs : List Record}
    (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hA : ∀ z, z ∈ A ↔ z ∈ classList p x 0 1)
    (hB : ∀ z, z ∈ B ↔ z ∈ classList p x 1 1)
    (hC : ∀ z, z ∈ C ↔ z ∈ classList p x 2 (-1))
    (he : finiteEquation A B C g rs) : Coloring.DistinctZeroSum x := by
  obtain ⟨t,ht,heq⟩ := he
  obtain ⟨i,j,k,hij,hik,hjk,_,_,_,_,_,_,hsum⟩ := finite_color_positions p x hA hB hC ht heq
  exact ⟨i,j,k,hij,hik,hjk,hsum⟩

theorem finite_color_iff {n W g : ℕ} {A B C : List ℤ}
    (p : Coloring.Parameter W) (x : Fin n → ℤ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ classList p x 0 1)
    (hB : ∀ z, z ∈ B ↔ z ∈ classList p x 1 1)
    (hC : ∀ z, z ∈ C ↔ z ∈ classList p x 2 (-1)) :
    finiteEquation A B C g (sortedRecords A B C g hg hsA hsB hsC) ↔ witness p x := by
  constructor
  · rintro ⟨t,ht,heq⟩
    exact finite_original_equation_sound hA hB hC ht heq
  · rintro ⟨a,ha,b,hb,c,hc,heq⟩
    obtain ⟨t,ht,hav,hbv,hcv⟩ :=
      finite_original_equation_complete hg hsA hsB hsC hA hB hC ha hb hc heq
    refine ⟨t,ht,?_⟩
    rw [hav,hbv,hcv]
    exact heq

theorem finite_color_reduction_correct {n W g : ℕ} (x : Fin n → ℤ)
    (hn : n ≤ 2^W) (hg : 0 < g) (A B C : Coloring.Parameter W → List ℤ)
    (hsA : ∀ p, (A p).Pairwise (· < ·))
    (hsB : ∀ p, (B p).Pairwise (· < ·))
    (hsC : ∀ p, (C p).Pairwise (· < ·))
    (hA : ∀ p z, z ∈ A p ↔ z ∈ classList p x 0 1)
    (hB : ∀ p z, z ∈ B p ↔ z ∈ classList p x 1 1)
    (hC : ∀ p z, z ∈ C p ↔ z ∈ classList p x 2 (-1)) :
    Coloring.DistinctZeroSum x ↔ ∃ p : Coloring.Parameter W,
      finiteEquation (A p) (B p) (C p) g
        (sortedRecords (A p) (B p) (C p) g hg (hsA p) (hsB p) (hsC p)) := by
  rw [ColorClassLists.reduction_correct x hn]
  exact exists_congr fun p =>
    (finite_color_iff p x hg (hsA p) (hsB p) (hsC p) (hA p) (hB p) (hC p)).symm

end ThreeSum.BandRawA
