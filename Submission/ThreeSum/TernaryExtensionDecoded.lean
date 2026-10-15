import Submission.ThreeSum.TernaryExtensionRelations

/-! Physical coefficient decoding agrees with the actual quotient-field basis. -/

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding

open Polynomial
variable {p : ℕ} [Fact p.Prime]

theorem encode_digit {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f)
    (i : Fin f.natDegree) :
    encode hf x/p^i.val%p=((coefficients hf) x i).val := by
  let xs := List.ofFn fun j => ((coefficients hf) x j).val
  have hb : ∀ n∈xs, n<p := by
    intro n hn
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hn
    exact ZMod.val_lt _
  have hh : (xs.drop i.val).head?=some (((coefficients hf) x i).val) := by
    simp [xs,List.head?_drop,List.getElem?_ofFn,i.isLt]
  change Nat.ofDigits p xs/p^i.val%p=_
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i.val (Fact.out : p.Prime).pos xs hb,
    Nat.ofDigits_mod_eq_head!,List.head!_of_head? hh,Nat.mod_eq_of_lt (ZMod.val_lt _)]

theorem decode_encoded {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    (fun i : Fin f.natDegree => ((encode hf x/p^i.val%p : ℕ) : ZMod p))=
      coefficients hf x := by
  funext i
  rw [encode_digit]
  exact ZMod.natCast_zmod_val _

theorem mk_decoded {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    AdjoinRoot.mk f (vectorPolynomial
      (fun i : Fin f.natDegree => ((encode hf x/p^i.val%p : ℕ) : ZMod p)))=x := by
  rw [decode_encoded]
  apply (coefficients hf).injective
  exact coefficients_mk_vector hf _

theorem quotient_product_of_relation {f : (ZMod p)[X]} (hf : f.Monic)
    (x y : AdjoinRoot f) (h r : Fin f.natDegree → ZMod p)
    (hr : remainderRelation (coefficients hf x) (coefficients hf y) h r) :
    coefficients hf (x*y)=r := by
  simpa only [LinearEquiv.symm_apply_apply] using
    remainderRelation_correct hf (coefficients hf x) (coefficients hf y) h r hr

end ThreeSum.TernaryExtensionEncoding
