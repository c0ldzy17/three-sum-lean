import Mathlib.FieldTheory.Finiteness
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Tactic

/-! Finite paired support selection over singleton source hash buckets.

The two maps in the greedy lemma must actually be injective: the physical
mode map and the source-key map on one chosen pair per physical mode. The
second injectivity follows only after nonsingleton source buckets are removed.
This module does not assert a complete running-time or benchmark theorem.
-/

noncomputable section
namespace ThreeSum.TernaryPairedSupport

open Finset

attribute [local instance] Classical.propDecidable

variable {K E V W : Type*} [Field K] [Fintype K]
  [AddCommGroup V] [Module K V] [Fintype V]
  [AddCommGroup W] [Module K W] [Fintype W]
  [Fintype E]

theorem span_card_eq {j : ℕ} (v : Fin j → V) (hv : LinearIndependent K v) :
    Nat.card (Submodule.span K (Set.range v)) = Fintype.card K ^ j := by
  classical
  rw [Module.natCard_eq_pow_finrank (K := K)]
  rw [Nat.card_eq_fintype_card]
  rw [finrank_span_eq_card hv]
  simp

theorem forbidden_card_le {j : ℕ} (f : E → V) (hf : Function.Injective f)
    (v : Fin j → V) (hv : LinearIndependent K v) :
    (univ.filter fun e => f e ∈ Submodule.span K (Set.range v)).card ≤
      Fintype.card K ^ j := by
  classical
  letI := Fintype.ofFinite (Submodule.span K (Set.range v))
  let S := univ.filter fun e => f e ∈ Submodule.span K (Set.range v)
  let g : S → Submodule.span K (Set.range v) := fun e =>
    ⟨f e.val, (mem_filter.mp e.property).2⟩
  have hg : Function.Injective g := by
    intro a b h
    apply Subtype.ext
    exact hf (congrArg Subtype.val h)
  have hc := Fintype.card_le_of_injective g hg
  have hc' : Nat.card S ≤ Nat.card (Submodule.span K (Set.range v)) := by
    simpa only [Nat.card_eq_fintype_card] using hc
  rw [span_card_eq v hv] at hc'
  change S.card ≤ _
  simpa only [Nat.card_eq_fintype_card,Fintype.card_coe] using hc'

/-- Greedy simultaneous independence. The deliberately coarse threshold
`2*p^m` avoids an off-by-one affine-span convention and is a fixed constant
when the moment order and native prime are fixed. -/
theorem exists_joint_independent (f : E → V) (g : E → W)
    (hf : Function.Injective f) (hg : Function.Injective g) (m : ℕ)
    (hcard : 2 * Fintype.card K ^ m < Fintype.card E) :
    ∃ e : Fin m → E, LinearIndependent K (fun i => f (e i)) ∧
      LinearIndependent K (fun i => g (e i)) := by
  classical
  have haux : ∀ j ≤ m, ∃ e : Fin j → E,
      LinearIndependent K (fun i => f (e i)) ∧
      LinearIndependent K (fun i => g (e i)) := by
    intro j
    induction j with
    | zero =>
      intro hj
      refine ⟨Fin.elim0, ?_, ?_⟩ <;> exact linearIndependent_empty_type
    | succ j ih =>
      intro hj
      obtain ⟨e,hef,heg⟩ := ih (by omega)
      let A := univ.filter fun x => f x ∈ Submodule.span K (Set.range (fun i => f (e i)))
      let B := univ.filter fun x => g x ∈ Submodule.span K (Set.range (fun i => g (e i)))
      have hA : A.card ≤ Fintype.card K ^ j := forbidden_card_le f hf _ hef
      have hB : B.card ≤ Fintype.card K ^ j := forbidden_card_le g hg _ heg
      have hpow : Fintype.card K ^ j ≤ Fintype.card K ^ m :=
        Nat.pow_le_pow_right Fintype.card_pos (by omega)
      have hAB : (A ∪ B).card < (univ : Finset E).card := by
        have hu := card_union_le A B
        simp only [card_univ]
        omega
      obtain ⟨x,hx,hout⟩ := exists_mem_notMem_of_card_lt_card hAB
      have hfa : f x ∉ Submodule.span K (Set.range (fun i => f (e i))) := by
        intro h
        exact hout (mem_union_left B (mem_filter.mpr ⟨mem_univ _,h⟩))
      have hgb : g x ∉ Submodule.span K (Set.range (fun i => g (e i))) := by
        intro h
        exact hout (mem_union_right A (mem_filter.mpr ⟨mem_univ _,h⟩))
      refine ⟨Fin.cons x e, ?_, ?_⟩
      · change LinearIndependent K (f ∘ Fin.cons x e)
        rw [Fin.comp_cons]
        exact hef.finCons hfa
      · change LinearIndependent K (g ∘ Fin.cons x e)
        rw [Fin.comp_cons]
        exact heg.finCons hgb
  exact haux m le_rfl

section Endpoints

variable {ι : Type*} [Fintype ι]

def taggedEndpoints (L R : ι → V) : Sum ι ι → V × (K × K) :=
  Sum.elim (fun i => (L i,(1,0))) (fun i => (R i,(0,1)))

/-- The two independent affine families and the two endpoint tags force
full paired rank. This is the exact implication needed by the determinant
potential; untagged or separately marginal rank claims do not suffice. -/
theorem taggedEndpoints_independent (L R : ι → V) (H : V →ₗ[K] W) (o : W)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : LinearIndependent K (fun i => (L i+R i,(1 : K))))
    (hleft : LinearIndependent K (fun i => (H (L i),(1 : K)))) :
    LinearIndependent K (taggedEndpoints (K := K) L R) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  let a : ι → K := fun i => c (Sum.inl i)
  let b : ι → K := fun i => c (Sum.inr i)
  have hv : (∑ i, a i • L i)+(∑ i, b i • R i)=0 := by
    have hh := congrArg Prod.fst hc
    simpa [taggedEndpoints,Fintype.sum_sum_type,a,b,Prod.fst_sum,Prod.snd_sum] using hh
  have ha : ∑ i, a i=0 := by
    have hh := congrArg (fun z : V × (K × K) => z.2.1) hc
    simpa [taggedEndpoints,Fintype.sum_sum_type,a,b,Prod.fst_sum,Prod.snd_sum] using hh
  have hb : ∑ i, b i=0 := by
    have hh := congrArg (fun z : V × (K × K) => z.2.2) hc
    simpa [taggedEndpoints,Fintype.sum_sum_type,a,b,Prod.fst_sum,Prod.snd_sum] using hh
  have hr (i : ι) : H (R i)=o-H (L i) := by
    have h := hroot i
    rw [map_add] at h
    exact eq_sub_of_add_eq' h
  have hd : ∑ i, (a i-b i) • (H (L i),(1 : K))=0 := by
    apply Prod.ext
    · have hh := congrArg H hv
      simp only [map_add,map_sum,map_smul,map_zero,hr] at hh
      have ho : (∑ i, b i • o)=0 := by rw [← sum_smul,hb,zero_smul]
      simp only [smul_sub,sum_sub_distrib,ho,zero_sub] at hh
      simpa [sub_smul,sum_sub_distrib,Prod.fst_sum,sub_eq_add_neg,add_smul,sum_add_distrib] using hh
    · simp [Prod.snd_sum,sum_sub_distrib,ha,hb]
  have hab : ∀ i, a i=b i := by
    have hh := Fintype.linearIndependent_iff.mp hleft (fun i => a i-b i) hd
    intro i
    exact sub_eq_zero.mp (hh i)
  have hm : ∑ i, b i • (L i+R i,(1 : K))=0 := by
    apply Prod.ext
    · simpa [smul_add,sum_add_distrib,hab,Prod.fst_sum] using hv
    · simpa [Prod.snd_sum] using hb
  have hb0 := Fintype.linearIndependent_iff.mp hmode b hm
  cases i with
  | inl i => exact (hab i).trans (hb0 i)
  | inr i => exact hb0 i

end Endpoints

section PhysicalSupport

variable {P D : Type*} [Fintype P] [DecidableEq D]

def physicalSupport (mode : P → D) : Finset D := univ.image mode

/-- One representative per physical mode is enough. The two injectivity
premises are stated on the actual original pair records, not on local words.
In particular the left-hash premise needs singleton ORIGINAL source buckets. -/
theorem physical_support_cap (L R : P → V) (H : V →ₗ[K] W) (o : W)
    (mode : P → D) (m : ℕ)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : ∀ a b, L a+R a=L b+R b → mode a=mode b)
    (hhash : ∀ a b, H (L a)=H (L b) → mode a=mode b)
    (hno : ∀ e : Fin m → P,
      ¬ LinearIndependent K (taggedEndpoints (K := K) (L ∘ e) (R ∘ e))) :
    (physicalSupport mode).card ≤ 2 * Fintype.card K ^ m := by
  classical
  let S := physicalSupport mode
  have hrep : ∀ d : S, ∃ i : P, mode i=d.val := by
    intro d
    obtain ⟨i,hi,he⟩ := mem_image.mp d.property
    exact ⟨i,he⟩
  let rep : S → P := fun d => Classical.choose (hrep d)
  have hr : ∀ d : S, mode (rep d)=d.val := fun d => Classical.choose_spec (hrep d)
  let f : S → V × K := fun d => (L (rep d)+R (rep d),1)
  let g : S → W × K := fun d => (H (L (rep d)),1)
  have hf : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    have hh := hmode (rep a) (rep b) (congrArg Prod.fst he)
    simpa only [hr] using hh
  have hg : Function.Injective g := by
    intro a b he
    apply Subtype.ext
    have hh := hhash (rep a) (rep b) (congrArg Prod.fst he)
    simpa only [hr] using hh
  by_contra! hlarge
  have hc : 2 * Fintype.card K ^ m < Fintype.card S := by
    simpa only [Fintype.card_coe] using hlarge
  obtain ⟨e,hef,heg⟩ := exists_joint_independent f g hf hg m hc
  have he := taggedEndpoints_independent (fun i => L (rep (e i)))
    (fun i => R (rep (e i))) H o (fun i => hroot (rep (e i))) hef heg
  exact hno (rep ∘ e) he

/-- A zero nonnegative tuple potential supplies the no-full-rank premise.
The caller must prove the actual full-rank tuple gives positive weight;
the theorem does not substitute a marginal score for the paired potential. -/
theorem physical_support_cap_of_zero_potential
    (L R : P → V) (H : V →ₗ[K] W) (o : W) (mode : P → D) (m : ℕ)
    (weight : (Fin m → P) → ℕ)
    (hroot : ∀ i, H (L i+R i)=o)
    (hmode : ∀ a b, L a+R a=L b+R b → mode a=mode b)
    (hhash : ∀ a b, H (L a)=H (L b) → mode a=mode b)
    (hpos : ∀ e, LinearIndependent K
      (taggedEndpoints (K := K) (L ∘ e) (R ∘ e)) → 0 < weight e)
    (hzero : (∑ e : Fin m → P, weight e)=0) :
    (physicalSupport mode).card ≤ 2 * Fintype.card K ^ m := by
  apply physical_support_cap L R H o mode m hroot hmode hhash
  intro e he
  have hz : weight e=0 := by
    have hh := single_le_sum (f := weight) (fun _ _ => Nat.zero_le _) (mem_univ e)
    rw [hzero] at hh
    omega
  exact (Nat.ne_of_gt (hpos e he)) hz

end PhysicalSupport
end ThreeSum.TernaryPairedSupport
