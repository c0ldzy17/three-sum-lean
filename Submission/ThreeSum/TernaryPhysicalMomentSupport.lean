import Submission.ThreeSum.FiniteMomentZeroDetector
import Mathlib.Data.Finset.Sort

noncomputable section
namespace ThreeSum.TernaryPhysicalMomentSupport
open Finset FiniteMomentZeroDetector
open scoped BigOperators
variable {P : Type*} [Fintype P]
set_option maxHeartbeats 3000000

def support (mode : P → ℤ) : Finset ℤ := univ.image mode

def enumeration (mode : P → ℤ) : Fin (support mode).card ≃o {d : ℤ // d∈support mode} :=
  (support mode).orderIsoOfFin rfl

def values (mode : P → ℤ) (i : Fin (support mode).card) : ℤ := (enumeration mode i).val

def weights (mode mass : P → ℤ) (i : Fin (support mode).card) : ℤ :=
  ∑ a, if mode a=values mode i then mass a else 0

theorem values_injective (mode : P → ℤ) : Function.Injective (values mode) := by
  intro i j hij
  apply (enumeration mode).injective
  exact Subtype.ext hij

theorem values_coverage (mode : P → ℤ) (a : P) : ∃ i, values mode i=mode a := by
  let d : {d : ℤ // d∈support mode} := ⟨mode a,mem_image.mpr ⟨a,mem_univ _,rfl⟩⟩
  refine ⟨(enumeration mode).symm d,?_⟩
  exact congrArg Subtype.val ((enumeration mode).apply_symm_apply d)

theorem weights_positive (mode mass : P → ℤ) (hm : ∀ a, 0<mass a)
    (i : Fin (support mode).card) : 0<weights mode mass i := by
  unfold weights
  apply sum_pos'
  · intro a ha
    split_ifs <;> first | exact (hm a).le | rfl
  · have hmem := (enumeration mode i).property
    obtain ⟨a,ha,he⟩ := mem_image.mp hmem
    refine ⟨a,mem_univ _,?_⟩
    have hv : mode a=values mode i := he
    simpa only [if_pos hv] using hm a

theorem grouped_moment (mode mass : P → ℤ) (k : ℕ) :
    moment (values mode) (weights mode mass) k=∑ a, mass a*mode a^k := by
  classical
  unfold moment weights
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a ha
  obtain ⟨i,hi⟩ := values_coverage mode a
  rw [sum_eq_single i]
  · simp [hi]
  · intro j hj hji
    have hn : mode a≠values mode j := by
      intro h
      apply hji
      exact values_injective mode (h.symm.trans hi.symm)
    simp [hn]
  · simp

theorem target_iff (mode : P → ℤ) (target : ℤ) :
    (∃ i, values mode i=target) ↔ ∃ a, mode a=target := by
  constructor
  · rintro ⟨i,hi⟩
    have hmem := (enumeration mode i).property
    obtain ⟨a,ha,he⟩ := mem_image.mp hmem
    exact ⟨a,he.trans hi⟩
  · rintro ⟨a,ha⟩
    obtain ⟨i,hi⟩ := values_coverage mode a
    exact ⟨i,hi.trans ha⟩

theorem support_representation (mode mass : P → ℤ) (hm : ∀ a, 0<mass a)
    {H : ℕ} (hH : (support mode).card≤H) :
    ∃ t≤H, ∃ v w : Fin t → ℤ, Function.Injective v ∧
      (∀ i, w i≠0) ∧ (∀ k, moment v w k=∑ a, mass a*mode a^k) ∧
      (∀ target, (∃ i, v i=target) ↔ ∃ a, mode a=target) := by
  refine ⟨(support mode).card,hH,values mode,weights mode mass,values_injective mode,?_,
    grouped_moment mode mass,target_iff mode⟩
  intro i
  exact ne_of_gt (weights_positive mode mass hm i)

end ThreeSum.TernaryPhysicalMomentSupport
