import Submission.ThreeSum.TernaryPairedSupportConcrete

/-! Existing tag coordinates suffice: the executable potential does not need
an additional pair of artificial coordinates. -/
noncomputable section
namespace ThreeSum.TernaryTaggedMinorSupport
open TernaryPairedSupport TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {p Λ : ℕ} [Fact p.Prime]
variable {P W D : Type*} [Fintype P] [AddCommGroup W] [Module (ZMod p) W] [Fintype W] [DecidableEq D]

def retag (a b : Fin Λ) : (Fin Λ→ZMod p)→ₗ[ZMod p] ((Fin Λ→ZMod p)×(ZMod p×ZMod p)) where
  toFun v := (v,(v a,v b))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem support (L R : P→Fin Λ→ℤ) (a b : Fin Λ)
    (hL : ∀ x, L x a=1 ∧ L x b=0) (hR : ∀ x, R x a=0 ∧ R x b=1)
    (H : (Fin Λ→ZMod p)→ₗ[ZMod p] W) (o : W) (mode : P→D) (K : ℕ)
    (hroot : ∀ x, H ((fun j => (L x j : ZMod p))+(fun j => (R x j : ZMod p)))=o)
    (hmode : ∀ x y, (fun j => (L x j : ZMod p))+(fun j => (R x j : ZMod p))=
      (fun j => (L y j : ZMod p))+(fun j => (R y j : ZMod p))→mode x=mode y)
    (hhash : ∀ x y, H (fun j => (L x j : ZMod p))=H (fun j => (L y j : ZMod p))→mode x=mode y)
    (hzero : (∑ e : Fin K→P, rowWeight (Sum.elim (fun k => L (e k)) (fun k => R (e k))))=0) :
    (physicalSupport mode).card≤2*p^K := by
  suffices hc : (physicalSupport mode).card≤2*Fintype.card (ZMod p)^K by
    simpa using hc
  apply physical_support_cap_of_zero_potential
    (fun x j => (L x j : ZMod p)) (fun x j => (R x j : ZMod p)) H o mode K
    (fun e => rowWeight (Sum.elim (fun k => L (e k)) (fun k => R (e k)))) hroot hmode hhash ?_ hzero
  intro e he
  apply rowWeight_pos_of_mod_independent _ (Int.castRingHom (ZMod p))
  apply LinearIndependent.of_comp (retag a b)
  have hrow : (fun i => retag a b (Sum.elim
      (fun k j => (L (e k) j : ZMod p)) (fun k j => (R (e k) j : ZMod p)) i))=
      taggedEndpoints (K := ZMod p) (fun k j => (L (e k) j : ZMod p))
        (fun k j => (R (e k) j : ZMod p)) := by
    funext i
    cases i with
    | inl k => simp [retag,taggedEndpoints,(hL (e k)).1,(hL (e k)).2]
    | inr k => simp [retag,taggedEndpoints,(hR (e k)).1,(hR (e k)).2]
  have hcast : (fun i j => (Int.castRingHom (ZMod p))
      (Sum.elim (fun k => L (e k)) (fun k => R (e k)) i j))=
      Sum.elim (fun k j => (L (e k) j : ZMod p)) (fun k j => (R (e k) j : ZMod p)) := by
    funext i j
    cases i <;> rfl
  change LinearIndependent (ZMod p) (fun i => retag a b ((fun i j => (Int.castRingHom (ZMod p))
      (Sum.elim (fun k => L (e k)) (fun k => R (e k)) i j)) i))
  rw [hcast,hrow]
  exact he

end ThreeSum.TernaryTaggedMinorSupport
