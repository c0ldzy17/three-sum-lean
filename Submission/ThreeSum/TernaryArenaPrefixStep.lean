import Submission.ThreeSum.TernaryArenaPrefixPotential

noncomputable section
namespace ThreeSum.TernaryArenaPrefixStep
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryArenaPrefixGroups TernaryArenaPrefixPairs TernaryArenaPrefixPotential
open TernaryNativePrefixLineage TernaryPairedPotential TernaryPairedContraction TernaryOriginalRowMenu
open TernaryExtensionEncoding
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F Λ : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : TernaryGoodOutputCatalog.Output m)

variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

theorem next_eq_physical (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (r K : ℕ) :
    nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
      ((M maps τ cap I L R row root).matrix (r := r) (K := K)) maps seed=
    nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
      (matrix maps τ cap I L R row root Q (r := r) (K := K)) maps seed := by
  unfold nextPotential
  have hh := (equiv maps τ cap I L R row root Q r K).sum_comp
    (fun x => ∑ c : Child (fixedLength m) K F (fixedAlpha m) (fixedPi m),
      if seed∈menuEvent ℓ
          (fun i j => (((M maps τ cap I L R row root).matrix x i j : ℤ) : ZMod p))
          (childTarget maps c)
        then minorWeight ((M maps τ cap I L R row root).matrix x) else 0)
  convert hh.symm using 1 <;> simp only [matrix_equiv]
  rfl

/-- The checked physical score of the next prefix is bounded using the
literal parent physical records. No assumed source/potential correspondence
remains: the bijections retain every actual ordinal and dictionary index. -/
theorem retained_next (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (r K : ℕ)
    (hrow : row r=TernaryOriginalRowMenu.row Λ ℓ seed) :
    value maps τ cap I L R row root Q (r+1) K≤
      nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
        (matrix maps τ cap I L R row root Q (r := r) (K := K)) maps seed := by
  rw [value_eq_model]
  exact ((M maps τ cap I L R row root).retained_next_le ℓ seed hrow).trans_eq
    (next_eq_physical maps τ cap I L R row root Q ℓ seed r K)

/-- Appending one ORIGINAL row changes no earlier native key or wanted
carry/root occurrence. This is the common-parent identity for all seeds. -/
theorem input_update_prefix (newrow : (Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p)
    (newroot : ℕ→ZMod p) (r : ℕ) :
    input I L R (Function.update row r newrow) (fun o => Function.update (root o) r (newroot o)) r=
      input I L R row root r := by
  have hr (j : Fin r) : j.val≠r := Nat.ne_of_lt j.isLt
  have hL : (fun i => (coefficientCode (fun j : Fin r =>
      Function.update row r newrow j.val (fun t => (L i t : ZMod p))) : ℤ))=
      fun i => (coefficientCode (fun j : Fin r => row j.val (fun t => (L i t : ZMod p))) : ℤ) := by
    funext i
    congr 1
    congr 1
    funext j
    rw [Function.update_of_ne (hr j)]
  have hR : (fun i => (coefficientCode (fun j : Fin r =>
      Function.update row r newrow j.val (fun t => (R i t : ZMod p))) : ℤ))=
      fun i => (coefficientCode (fun j : Fin r => row j.val (fun t => (R i t : ZMod p))) : ℤ) := by
    funext i
    congr 1
    congr 1
    funext j
    rw [Function.update_of_ne (hr j)]
  have hO : (fun i => (coefficientCode (fun j : Fin r =>
      Function.update (root i) r (newroot i) j.val) : ℤ))=
      fun i => (coefficientCode (fun j : Fin r => root i j.val) : ℤ) := by
    funext i
    congr 1
    congr 1
    funext j
    rw [Function.update_of_ne (hr j)]
  unfold input
  rw [hL,hR,hO]


abbrev PhysicalIndex {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (K : ℕ) :=
  Σ j : Fin S.front.count, Fin K→TernaryNativePairMoments.Pair S j.val

def physicalMatrix {N K : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (L R : ℕ→Fin Λ→ℤ) (x : PhysicalIndex S K) : Matrix (Fin (K+K)) (Fin Λ) ℤ :=
  fun i => Sum.elim (fun k => L (x.2 k).val.1.1) (fun k => R (x.2 k).val.2.1) (finSumFinEquiv.symm i)

/-- All menu candidates share exactly the same literal physical parent. -/
theorem appended_next (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (newroot : ℕ→ZMod p) (r K : ℕ) :
    value maps τ cap I L R (Function.update row r (TernaryOriginalRowMenu.row Λ ℓ seed))
      (fun o => Function.update (root o) r (newroot o)) Q (r+1) K≤
      nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
        (matrix maps τ cap I L R row root Q (r := r) (K := K)) maps seed := by
  let rn := Function.update row r (TernaryOriginalRowMenu.row Λ ℓ seed)
  let on := fun o => Function.update (root o) r (newroot o)
  have hh := retained_next maps τ cap I L R rn on Q ℓ seed r K (by simp [rn])
  have hs : S (r := r) maps τ cap I L R rn on Q=S (r := r) maps τ cap I L R row root Q := by
    apply congrArg (fun v => setup (r := r) maps τ cap Q v)
    exact input_update_prefix I L R row root (TernaryOriginalRowMenu.row Λ ℓ seed) newroot r
  change value maps τ cap I L R rn on Q (r+1) K≤
    nextPotential (α := fixedAlpha m) (π := fixedPi m) ℓ
      (physicalMatrix (S (r := r) maps τ cap I L R rn on Q) L R (K := K)) maps seed at hh
  rw [hs] at hh
  exact hh

/-- Original physical paired potentials satisfy the proved menu average,
including dictionary trimming, all carry/requester occurrences and all groups. -/
theorem sum_appended_bound (ℓ : E→ₗ[ZMod p] ZMod p) (hℓ : ℓ≠0)
    (V : Submodule (ZMod p) (Fin Λ→ZMod p)) (hV : V≠⊤) (hp : 3≤p)
    (newroot : E×E→ℕ→ZMod p) (r K b : ℕ)
    (hL : ∀ i j, (L i j).natAbs≤b) (hR : ∀ i j, (R i j).natAbs≤b)
    (hdet : (K+K).factorial*b^(K+K)<p)
    (hsize1 : 8*Λ*p^2≤Fintype.card E) (hsize : 8*Λ*p^(2*(K+K))≤Fintype.card E) :
    p^(K+K)*(∑ seed∈admissible Λ ℓ V,
      value maps τ cap I L R (Function.update row r (TernaryOriginalRowMenu.row Λ ℓ seed))
        (fun o => Function.update (root o) r (newroot seed o)) Q (r+1) K)≤
      3*(admissible Λ ℓ V).card*F*(vertices (fixedLength m) (fixedPi m)).card*
        (2^(fixedPi m 1)*3^(fixedPi m 2))^K*value maps τ cap I L R row root Q r K := by
  have hsmall : ∀ (x : Index maps τ cap I L R row root Q r K) f,
      ((matrix maps τ cap I L R row root Q x).submatrix id f).det.natAbs<p := by
    intro x
    apply minor_small_of_entry_bound _ b ?_ hdet
    intro i j
    unfold matrix
    cases finSumFinEquiv.symm i with
    | inl k => exact hL _ _
    | inr k => exact hR _ _
  have hh := sum_nextPotential_bound (α := fixedAlpha m) (π := fixedPi m) ℓ hℓ V hV hp
    (matrix maps τ cap I L R row root Q (r := r) (K := K)) hsmall maps hsize1 hsize
  apply le_trans (Nat.mul_le_mul_left _ (sum_le_sum (fun seed hs =>
    appended_next maps τ cap I L R row root Q ℓ seed (newroot seed) r K))) hh

end ThreeSum.TernaryArenaPrefixStep
