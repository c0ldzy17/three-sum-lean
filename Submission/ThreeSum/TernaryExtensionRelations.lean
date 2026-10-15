import Submission.ThreeSum.TernaryExtensionCandidates

/-! Exact bounded factor and quotient relations used by exhaustive machine searches. -/

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding

open Polynomial Finset
set_option maxHeartbeats 3000000

variable {p : ℕ} [Fact p.Prime]

theorem irreducible_iff_no_monic_factors {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.Monic) (hdeg : f.natDegree=d) (hd : 0<d) :
    Irreducible f ↔ ∀ e, 0<e → e<d →
      ∀ (a : Fin e → ZMod p) (b : Fin (d-e) → ZMod p),
        monicCandidate a*monicCandidate b≠f := by
  constructor
  · intro hI e he hed a b hab
    rcases hI.2 hab.symm with hu | hu
    · have hz := natDegree_eq_zero_of_isUnit hu
      rw [monicCandidate_degree] at hz
      omega
    · have hz := natDegree_eq_zero_of_isUnit hu
      rw [monicCandidate_degree] at hz
      omega
  · intro h
    apply hf.irreducible_iff_natDegree.mpr
    refine ⟨?_,?_⟩
    · intro he
      rw [he,natDegree_one] at hdeg
      omega
    · intro g k hg hk hprod
      by_cases hz : g.natDegree=0
      · exact Or.inl hz
      by_cases hz' : k.natDegree=0
      · exact Or.inr hz'
      have hsum : g.natDegree+k.natDegree=d := by rw [← hdeg,← hprod,hg.natDegree_mul hk]
      have he : 0<g.natDegree := by omega
      have hed : g.natDegree<d := by omega
      have hkdeg : k.natDegree=d-g.natDegree := by omega
      exfalso
      apply h g.natDegree he hed (fun i => g.coeff i.val) (fun i => k.coeff i.val)
      rw [monicCandidate_of_monic hg rfl,monicCandidate_of_monic hk hkdeg,hprod]

theorem coefficients_mk_vector {f : (ZMod p)[X]} (hf : f.Monic)
    (a : Fin f.natDegree → ZMod p) :
    coefficients hf (AdjoinRoot.mk f (vectorPolynomial a))=a := by
  funext i
  change (vectorPolynomial a %ₘ f).coeff i.val=a i
  rw [(modByMonic_eq_self_iff hf).mpr (by
    simpa only [degree_eq_natDegree hf.ne_zero] using vectorPolynomial_degree_lt a)]
  exact vectorPolynomial_coeff a i

theorem vectorPolynomial_of_natDegree_lt {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.natDegree<d) : vectorPolynomial (fun i : Fin d => f.coeff i.val)=f := by
  ext k
  by_cases hk : k<d
  · exact vectorPolynomial_coeff _ ⟨k,hk⟩
  · have hg : (vectorPolynomial (fun i : Fin d => f.coeff i.val)).coeff k=0 := by
      apply coeff_eq_zero_of_degree_lt
      exact (vectorPolynomial_degree_lt _).trans_le (by exact_mod_cast Nat.le_of_not_lt hk)
    rw [hg,coeff_eq_zero_of_natDegree_lt (by omega)]

def remainderRelation {f : (ZMod p)[X]}
    (a b h r : Fin f.natDegree → ZMod p) : Prop :=
  vectorPolynomial a*vectorPolynomial b=vectorPolynomial h*f+vectorPolynomial r

theorem remainderRelation_correct {f : (ZMod p)[X]} (hf : f.Monic)
    (a b h r : Fin f.natDegree → ZMod p) (hr : remainderRelation a b h r) :
    coefficients hf ((coefficients hf).symm a*(coefficients hf).symm b)=r := by
  have ha : (coefficients hf).symm a=AdjoinRoot.mk f (vectorPolynomial a) :=
    (LinearEquiv.symm_apply_eq (coefficients hf)).mpr (coefficients_mk_vector hf a).symm
  have hb : (coefficients hf).symm b=AdjoinRoot.mk f (vectorPolynomial b) :=
    (LinearEquiv.symm_apply_eq (coefficients hf)).mpr (coefficients_mk_vector hf b).symm
  rw [ha,hb,← map_mul]
  change vectorPolynomial a*vectorPolynomial b=vectorPolynomial h*f+vectorPolynomial r at hr
  rw [hr,map_add,map_mul,AdjoinRoot.mk_self,mul_zero,zero_add]
  exact coefficients_mk_vector hf r

theorem remainderRelation_exists {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) (a b : Fin f.natDegree → ZMod p) :
    ∃ h r : Fin f.natDegree → ZMod p, remainderRelation a b h r := by
  let z := vectorPolynomial a*vectorPolynomial b
  have hv (c : Fin f.natDegree → ZMod p) : (vectorPolynomial c).natDegree<f.natDegree := by
    by_cases hz : vectorPolynomial c=0
    · simpa only [hz,natDegree_zero] using hd
    · exact (natDegree_lt_iff_degree_lt hz).mpr (vectorPolynomial_degree_lt c)
  have ha := hv a
  have hb := hv b
  have hz : z.natDegree<2*f.natDegree := by
    exact (natDegree_mul_le.trans_lt (by omega))
  have hq : (z /ₘ f).natDegree<f.natDegree := by rw [natDegree_divByMonic z hf]; omega
  have hf1 : f≠1 := by intro h; rw [h,natDegree_one] at hd; omega
  have hrem := natDegree_modByMonic_lt z hf hf1
  refine ⟨fun i => (z /ₘ f).coeff i.val,fun i => (z %ₘ f).coeff i.val,?_⟩
  unfold remainderRelation
  rw [vectorPolynomial_of_natDegree_lt hq,vectorPolynomial_of_natDegree_lt hrem]
  change z=(z /ₘ f)*f+z %ₘ f
  rw [add_comm,mul_comm]
  exact (modByMonic_add_div z f).symm

end ThreeSum.TernaryExtensionEncoding
