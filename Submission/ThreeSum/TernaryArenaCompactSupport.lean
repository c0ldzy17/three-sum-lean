import Submission.ThreeSum.TernaryArenaPairRestriction
import Submission.ThreeSum.TernaryArenaPairModel
import Submission.ThreeSum.TernaryTaggedMinorSupport

noncomputable section
namespace ThreeSum.TernaryArenaCompactSupport
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaSourceSetup
open TernaryNativePairMoments TernaryNativeTensorScore LightOriginalSurvivors
open TernaryExtensionEncoding TernaryPairedPotential
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 4000000
variable {p m F r J K : ℕ} [Fact p.Prime]

/-- The actual compact native moment groups have bounded support once the
literal full native paired potential is zero. All singleton and physical
record restrictions are discharged inside this theorem. -/
theorem support (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (L R : ℕ→ℕ→ℤ) (B C : ℕ→ℤ)
    (H : (Fin (J+2)→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p)) (O : ℕ→Fin r→ZMod p)
    (keysB keysC : ℕ→ℕ) (a b : Fin (J+2))
    (hB : ∀ j<I.nB, I.leftInput j=(coefficientCode (H (fun t => (L j t.val : ZMod p))) : ℤ))
    (hC : ∀ j<I.nC, I.rightInput j=(coefficientCode (H (fun t => (R j t.val : ZMod p))) : ℤ))
    (hO : ∀ j<I.requesterCount, I.targets j=(coefficientCode (O j) : ℤ))
    (hkB : ∀ j<I.nB, keysB j=coefficientCode (H (fun t => (L j t.val : ZMod p))))
    (hkC : ∀ j<I.nC, keysC j=coefficientCode (H (fun t => (R j t.val : ZMod p))))
    (hLtag : ∀ j<I.nB, L j a.val=1 ∧ L j b.val=0)
    (hRtag : ∀ j<I.nC, R j a.val=0 ∧ R j b.val=1)
    (hraw : ∀ u<I.nB, ∀ v<I.nC, ∀ u'<I.nB, ∀ v'<I.nC,
      (fun t : Fin (J+2) => (L u t.val : ZMod p))+(fun t => (R v t.val : ZMod p))=
      (fun t : Fin (J+2) => (L u' t.val : ZMod p))+(fun t => (R v' t.val : ZMod p))→
        C v-B u=C v'-B u')
    (hzero : pairedPotential (setup (r := r) maps τ cap Q I) K J L R=0) :
    let fB := index keysB I.nB
    let fC := index keysC I.nC
    let I' := TernaryArenaPairRestriction.restrict I (indices keysB I.nB).length
      (indices keysC I.nC).length fB fC
    ∀ i<(setup (r := r) maps τ cap Q I').front.count,
      (TernaryPairedSupport.physicalSupport
        (mode (fun j => B (fB j)) (fun j => C (fC j)) (S := setup (r := r) maps τ cap Q I') (i := i))).card≤2*p^K := by
  let fB := index keysB I.nB
  let fC := index keysC I.nC
  let nB := (indices keysB I.nB).length
  let nC := (indices keysC I.nC).length
  let I' := TernaryArenaPairRestriction.restrict I nB nC fB fC
  let S := setup (r := r) maps τ cap Q I'
  have fBlt (j : ℕ) (hj : j<nB) : fB j<I.nB := index_lt hj
  have fClt (j : ℕ) (hj : j<nC) : fC j<I.nC := index_lt hj
  have fBinj : ∀ x<nB, ∀ y<nB, fB x=fB y→x=y := by
    intro x hx y hy he
    exact keys_injective hx hy (congrArg keysB he)
  have fCinj : ∀ x<nC, ∀ y<nC, fC x=fC y→x=y := by
    intro x hx y hy he
    exact keys_injective hx hy (congrArg keysC he)
  have hz : pairedPotential S K J (fun j => L (fB j)) (fun j => R (fC j))=0 := by
    exact Nat.eq_zero_of_le_zero ((TernaryArenaPairRestriction.potential_le (r := r)
      maps τ cap Q I nB nC fB fC fBlt fClt K J L R fBinj fCinj).trans_eq hzero)
  change ∀ i<S.front.count,
    (TernaryPairedSupport.physicalSupport
      (mode (fun j => B (fB j)) (fun j => C (fC j)) (S := S) (i := i))).card≤2*p^K
  intro i hi
  let L' : Pair S i→Fin (J+2)→ℤ := fun x t => L (fB x.val.1.1) t.val
  let R' : Pair S i→Fin (J+2)→ℤ := fun x t => R (fC x.val.2.1) t.val
  let root := O (TernaryArenaQueryModel.descriptor maps τ I'.targets I'.positions I'.requesterCount ⟨i,hi⟩).1
  have leftlt (x : Pair S i) : x.val.1.1<nB := TernaryCompactPairedSupport.native_left_lt x
  have rightlt (x : Pair S i) : x.val.2.1<nC := TernaryCompactPairedSupport.native_right_lt x
  have hr (x : Pair S i) : H ((fun t => (L' x t : ZMod p))+(fun t => (R' x t : ZMod p)))=root := by
    rw [map_add]
    exact TernaryArenaPairModel.original_hash_sum hi x
      (fun j => H (fun t => (L (fB j) t.val : ZMod p)))
      (fun j => H (fun t => (R (fC j) t.val : ZMod p))) O
      (fun j hj => hB _ (fBlt j hj)) (fun j hj => hC _ (fClt j hj)) hO
  have hweights : (∑ e : Fin K→Pair S i,
      rowWeight (Sum.elim (fun k => L' (e k)) (fun k => R' (e k))))=0 := by
    have hh := Finset.single_le_sum
      (f := fun q : Fin S.front.count => ∑ e : Fin K→Pair S q.val,
        rowWeight (Sum.elim
          (fun k => originalLeft S J (fun j => L (fB j)) q.val (e k))
          (fun k => originalRight S J (fun j => R (fC j)) q.val (e k))))
      (fun q hq => Nat.zero_le _) (Finset.mem_univ (⟨i,hi⟩ : Fin S.front.count))
    exact Nat.eq_zero_of_le_zero (hh.trans_eq hz)
  apply TernaryTaggedMinorSupport.support L' R' a b
    (fun x => hLtag _ (fBlt _ (leftlt x))) (fun x => hRtag _ (fClt _ (rightlt x))) H root
    (mode (fun j => B (fB j)) (fun j => C (fC j))) K hr ?_ ?_ hweights
  · intro x y he
    exact hraw _ (fBlt _ (leftlt x)) _ (fClt _ (rightlt x)) _ (fBlt _ (leftlt y)) _
      (fClt _ (rightlt y)) he
  · intro x y he
    have hk : keysB (fB x.val.1.1)=keysB (fB y.val.1.1) := by
      rw [hkB _ (fBlt _ (leftlt x)),hkB _ (fBlt _ (leftlt y)),he]
    have hbxy : x.val.1.1=y.val.1.1 := keys_injective (leftlt x) (leftlt y) hk
    have hright : H (fun t => (R' x t : ZMod p))=H (fun t => (R' y t : ZMod p)) := by
      have hx := hr x
      have hy := hr y
      rw [map_add] at hx hy
      exact add_left_cancel (he ▸ hx.trans hy.symm)
    have hkc : keysC (fC x.val.2.1)=keysC (fC y.val.2.1) := by
      rw [hkC _ (fClt _ (rightlt x)),hkC _ (fClt _ (rightlt y)),hright]
    have hcxy : x.val.2.1=y.val.2.1 := keys_injective (rightlt x) (rightlt y) hkc
    unfold mode
    rw [hbxy,hcxy]

end ThreeSum.TernaryArenaCompactSupport
