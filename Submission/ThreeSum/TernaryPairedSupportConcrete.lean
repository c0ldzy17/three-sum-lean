import Submission.ThreeSum.TernaryPairedPotential

/-! The concrete squared-minor potential supplies the paired-support
theorem, including both endpoint tags and every original pair record. -/

noncomputable section
namespace ThreeSum.TernaryPairedSupportConcrete

open Finset TernaryPairedPotential TernaryPairedSupport
open scoped BigOperators

variable {K : Type*} [Field K]

def flatten (J : ℕ) : ((Fin J → K) × (K × K)) →ₗ[K] (Fin (J+2) → K) where
  toFun u i := Sum.elim u.1 (fun j : Fin 2 => ![u.2.1,u.2.2] j) (finSumFinEquiv.symm i)
  map_add' u v := by
    funext i
    cases h : finSumFinEquiv.symm i with
    | inl j => simp [h]
    | inr j => fin_cases j <;> simp [h]
  map_smul' c u := by
    funext i
    cases h : finSumFinEquiv.symm i with
    | inl j => simp [h]
    | inr j => fin_cases j <;> simp [h]

theorem flatten_injective (J : ℕ) : Function.Injective (flatten (K := K) J) := by
  intro u v h
  apply Prod.ext
  · funext j
    have hh := congrFun h (finSumFinEquiv (Sum.inl j))
    simpa [flatten] using hh
  · apply Prod.ext
    · have hh := congrFun h (finSumFinEquiv (Sum.inr (0 : Fin 2)))
      simpa [flatten] using hh
    · have hh := congrFun h (finSumFinEquiv (Sum.inr (1 : Fin 2)))
      simpa [flatten] using hh

def flattenInt (J : ℕ) (u : (Fin J → ℤ) × (ℤ × ℤ)) : Fin (J+2) → ℤ :=
  fun i => Sum.elim u.1 (fun j : Fin 2 => ![u.2.1,u.2.2] j) (finSumFinEquiv.symm i)

theorem cast_flattenInt (J : ℕ) (u : (Fin J → ℤ) × (ℤ × ℤ)) :
    (fun i => (flattenInt J u i : K)) =
      flatten J ((fun j => (u.1 j : K)),((u.2.1 : K),(u.2.2 : K))) := by
  funext i
  cases h : finSumFinEquiv.symm i with
  | inl j => simp [flattenInt,flatten,h]
  | inr j => fin_cases j <;> simp [flattenInt,flatten,h]

variable {P W D : Type*} [Fintype P] [Fintype K]
  [AddCommGroup W] [Module K W] [Fintype W] [DecidableEq D]

def tupleMatrix {J m : ℕ} (L R : P → Fin J → ℤ) (e : Fin m → P) :
    (Fin m ⊕ Fin m) → Fin (J+2) → ℤ :=
  Sum.elim (fun i => flattenInt J (L (e i),(1,0)))
    (fun i => flattenInt J (R (e i),(0,1)))

theorem cast_tupleMatrix {J m : ℕ} (L R : P → Fin J → ℤ) (e : Fin m → P) :
    (fun i j => (tupleMatrix L R e i j : K)) =
      fun i => flatten J (taggedEndpoints (K := K)
        (fun i j => (L (e i) j : K)) (fun i j => (R (e i) j : K)) i) := by
  funext i
  cases i with
  | inl i => simpa [tupleMatrix,taggedEndpoints] using cast_flattenInt (K := K) J (L (e i),(1,0))
  | inr i => simpa [tupleMatrix,taggedEndpoints] using cast_flattenInt (K := K) J (R (e i),(0,1))

theorem physical_support_cap_of_zero_minors {J : ℕ}
    (L R : P → Fin J → ℤ) (H : (Fin J → K) →ₗ[K] W) (o : W)
    (mode : P → D) (m : ℕ)
    (hroot : ∀ a, H ((fun j => (L a j : K))+(fun j => (R a j : K)))=o)
    (hmode : ∀ a b, (fun j => (L a j : K))+(fun j => (R a j : K)) =
      (fun j => (L b j : K))+(fun j => (R b j : K)) → mode a=mode b)
    (hhash : ∀ a b, H (fun j => (L a j : K))=H (fun j => (L b j : K)) → mode a=mode b)
    (hzero : (∑ e : Fin m → P, rowWeight (tupleMatrix L R e))=0) :
    (physicalSupport mode).card ≤ 2*Fintype.card K^m := by
  classical
  apply physical_support_cap_of_zero_potential
    (fun a j => (L a j : K)) (fun a j => (R a j : K)) H o mode m
    (fun e => rowWeight (tupleMatrix L R e)) hroot hmode hhash
    (hzero := hzero)
  intro e he
  apply rowWeight_pos_of_mod_independent _ (Int.castRingHom K)
  change LinearIndependent K (fun i j => (tupleMatrix L R e i j : K))
  rw [cast_tupleMatrix]
  exact he.map' (flatten J) (LinearMap.ker_eq_bot.mpr (flatten_injective J))

/-- Singleton buckets on BOTH original source colors imply the required
left-hash injection on one fixed wanted root. No injection of local words
or uniqueness of an encoded representation is used. -/
theorem mode_eq_of_singleton_source_hashes {B C : Type*} {J : ℕ}
    (left : P → B) (right : P → C)
    (L : B → Fin J → K) (R : C → Fin J → K)
    (H : (Fin J → K) →ₗ[K] W) (o : W) (mode : P → D)
    (hleft : Function.Injective (fun b => H (L b)))
    (hright : Function.Injective (fun c => H (R c)))
    (hroot : ∀ a, H (L (left a)+R (right a))=o)
    (hmode : ∀ a b, left a=left b → right a=right b → mode a=mode b) :
    ∀ a b, H (L (left a))=H (L (left b)) → mode a=mode b := by
  intro a b hab
  apply hmode a b (hleft hab)
  apply hright
  have ha := hroot a
  have hb := hroot b
  rw [map_add] at ha hb
  exact add_left_cancel (hab ▸ ha.trans hb.symm)

end ThreeSum.TernaryPairedSupportConcrete
