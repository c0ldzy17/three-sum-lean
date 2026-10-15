import Submission.ThreeSum.TernaryExtensionSearchCorrect
import Submission.ThreeSum.TernaryOriginalRowMenu
import Submission.ThreeSum.LightExtensionSeedRow
import Submission.ThreeSum.LightNaturalDot

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000
noncomputable local instance (Q : Prop) : Decidable Q := Classical.propDecidable Q

variable {f : (ZMod p)[X]}

def encodedMul (hf : f.Monic) (a b : ℕ) : ℕ :=
  if ha : a<p^f.natDegree then if hb : b<p^f.natDegree then
    encode hf ((encodedEquiv hf).symm ⟨a,ha⟩*(encodedEquiv hf).symm ⟨b,hb⟩) else 0 else 0

theorem encodedMul_lt (hf : f.Monic) (a b : ℕ) : encodedMul hf a b<p^f.natDegree := by
  unfold encodedMul
  split_ifs
  · exact encode_lt hf _
  · exact pow_pos (Fact.out : p.Prime).pos _
  · exact pow_pos (Fact.out : p.Prime).pos _

theorem encodedMul_encode (hf : f.Monic) (x y : AdjoinRoot f) :
    encodedMul hf (encode hf x) (encode hf y)=encode hf (x*y) := by
  have hx : (encodedEquiv hf).symm ⟨encode hf x,encode_lt hf x⟩=x :=
    (encodedEquiv hf).symm_apply_apply x
  have hy : (encodedEquiv hf).symm ⟨encode hf y,encode_lt hf y⟩=y :=
    (encodedEquiv hf).symm_apply_apply y
  simp only [encodedMul,dif_pos (encode_lt hf x),dif_pos (encode_lt hf y),hx,hy]

theorem trajectory_encode (hf : f.Monic) (x y : AdjoinRoot f) (i : ℕ) :
    LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i=
      encode hf (y*x^i) := by
  induction i with
  | zero => simp [LightExtensionSeedRow.trajectory]
  | succ i ih =>
    simp only [LightExtensionSeedRow.trajectory,ih,encodedMul_encode,pow_succ,mul_assoc]

theorem trajectory_constantCoefficient (hf : f.Monic) (hd : 0<f.natDegree)
    (x y : AdjoinRoot f) (i : ℕ) :
    (LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i)%p=
      (constantCoefficient hf hd (y*x^i)).val := by
  rw [trajectory_encode,encode_mod]


def quotientGood (d c x y h r : ℕ) : Prop :=
  LightPolynomialProductCheck.Valid p (codeDigits (p := p) x) (codeDigits (p := p) y)
    (LightPolynomialQuotientCheck.expected p d (codeDigits (p := p) h)
      (codeDigits (p := p) (c+p^d)) (codeDigits (p := p) r)) d d (2*d)

theorem first_quotient_code (hf : f.Monic) (hd : 0<f.natDegree)
    {c x y : ℕ} (hc : c<p^f.natDegree) (hx : x<p^f.natDegree) (hy : y<p^f.natDegree)
    (hm : monicOfCode (p := p) f.natDegree c=f) :
    let q := p^f.natDegree
    let result := LightPairSearch.first
      (LightPairSearch.goodCode q (quotientGood (p := p) f.natDegree c x y)) (q*q)
    0<result ∧ (result-1)%q=encodedMul hf x y := by
  classical
  dsimp only
  let q := p^f.natDegree
  let good := quotientGood (p := p) f.natDegree c x y
  have hq : 0<q := pow_pos (Fact.out : p.Prime).pos _
  have hs := LightPairSearch.first_pair_spec q hq good
  obtain ⟨h,hh,r,hr,hg⟩ := quotient_code_exists hf hd hc hm x y
  have hn : LightPairSearch.first (LightPairSearch.goodCode q good) (q*q)≠0 := by
    intro hz
    exact (hs.1.mp hz h hh r hr) hg
  obtain ⟨code,hcode⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨hu,hv,hgood,hmin⟩ := hs.2 code hcode
  have hcproduct := quotient_code_correct hf hc hx hy hv hm hgood
  refine ⟨Nat.pos_of_ne_zero hn,?_⟩
  change (LightPairSearch.first (LightPairSearch.goodCode q good) (q*q)-1)%q=encodedMul hf x y
  rw [hcode,Nat.succ_sub_one]
  unfold encodedMul
  rw [dif_pos hx,dif_pos hy]
  exact hcproduct.symm

variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem rowMenu_coefficient (Λ : ℕ) (ℓ : AdjoinRoot f →ₗ[ZMod p] ZMod p)
    (x y : AdjoinRoot f) (i : Fin Λ) :
    TernaryOriginalRowMenu.seedRow Λ ℓ (x,y) i=ℓ (y*x^i.val) := by
  unfold TernaryOriginalRowMenu.seedRow TernaryOriginalRowMenu.row
    TernaryOriginalRowMenu.evalVector TernaryOriginalRowMenu.vectorPoly
  simp only [LinearMap.comp_apply,LinearMap.flip_apply,LinearMap.coe_mk,AddHom.coe_mk,
    LinearMap.pi_apply,LinearMap.proj_apply,LinearMap.restrictScalars_apply,
    Polynomial.ofFn_eq_sum_monomial,map_sum]
  simp [TernaryOriginalRowMenu.pairing,Pi.single_apply,mul_comm]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [hji]
  · simp

theorem trajectory_rowMenu (hf : f.Monic) (hd : 0<f.natDegree) (Λ : ℕ)
    (x y : AdjoinRoot f) (i : Fin Λ) :
    (LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i.val)%p=
      (TernaryOriginalRowMenu.seedRow Λ (constantCoefficient hf hd) (x,y) i).val := by
  rw [rowMenu_coefficient,trajectory_constantCoefficient]


theorem signed_lift_cast (z : ℤ) (hz : 0≤z+(p : ℤ)) :
    (((z+(p : ℤ)).toNat : ℕ) : ZMod p)=(z : ZMod p) := by
  have he : (((z+(p : ℤ)).toNat : ℕ) : ℤ)=z+(p : ℤ) := Int.toNat_of_nonneg hz
  have hh := congrArg (fun a : ℤ => (a : ZMod p)) he
  simpa only [Int.cast_natCast,Int.cast_add,ZMod.natCast_self,add_zero] using hh

theorem naturalDot_rowMenu (hf : f.Monic) (hd : 0<f.natDegree) (Λ : ℕ)
    (x y : AdjoinRoot f) (raw : Fin Λ → ℤ)
    (values coefs : ℕ → ℕ)
    (hvalues : ∀ i : Fin Λ, (values i.val : ZMod p)=(raw i : ZMod p))
    (hcoefs : ∀ i : Fin Λ, coefs i.val=
      LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i.val%p) :
    LightNaturalDot.dot values coefs Λ%p=
      (TernaryOriginalRowMenu.row Λ (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p))).val := by
  have he : ((LightNaturalDot.dot values coefs Λ : ℕ) : ZMod p)=
      TernaryOriginalRowMenu.row Λ (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p)) := by
    rw [TernaryOriginalRowMenu.row_eq_dot]
    unfold LightNaturalDot.dot LightBooleanDot.dot
    rw [Nat.cast_sum,← Fin.sum_univ_eq_sum_range]
    apply sum_congr rfl
    intro i hi
    rw [Nat.cast_mul,hvalues i,hcoefs i,trajectory_rowMenu hf hd Λ x y i,
      ZMod.natCast_zmod_val]
  have hh := congrArg ZMod.val he
  simpa using hh

end ThreeSum.TernaryExtensionEncoding
