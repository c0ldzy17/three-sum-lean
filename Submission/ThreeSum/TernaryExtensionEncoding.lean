import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.PrimitiveElement
import Mathlib.RingTheory.AdjoinRoot
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# Finite extension representation for the original-vector row menu

Existence of an irreducible polynomial justifies a finite exhaustive search.
The representation used after that search is its genuine monomial basis,
not an input-dependent table of field operations.
-/

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding

open Polynomial

set_option maxHeartbeats 3000000

variable (p : ℕ) [Fact p.Prime]

theorem exists_monic_irreducible (d : ℕ) (hd : 0<d) :
    ∃ f : (ZMod p)[X], f.Monic ∧ Irreducible f ∧ f.natDegree=d := by
  let E := GaloisField p d
  obtain ⟨a,ha⟩ := Field.exists_primitive_element_of_finite_top (ZMod p) E
  have hi : IsIntegral (ZMod p) a := IsIntegral.of_finite (ZMod p) a
  refine ⟨minpoly (ZMod p) a,minpoly.monic hi,minpoly.irreducible hi,?_⟩
  have hn := (Field.primitive_element_iff_minpoly_natDegree_eq (ZMod p) a).mp ha
  exact hn.trans (GaloisField.finrank p (by omega))

variable {p}

def coefficients {f : (ZMod p)[X]} (hf : f.Monic) :
    AdjoinRoot f ≃ₗ[ZMod p] (Fin f.natDegree → ZMod p) :=
  (AdjoinRoot.powerBasisAux' hf).equivFun

def constantCoefficient {f : (ZMod p)[X]} (hf : f.Monic) (hd : 0<f.natDegree) :
    AdjoinRoot f →ₗ[ZMod p] ZMod p :=
  (LinearMap.proj (⟨0,hd⟩ : Fin f.natDegree)).comp (coefficients hf).toLinearMap

theorem constantCoefficient_surjective {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) : Function.Surjective (constantCoefficient hf hd) := by
  intro a
  refine ⟨(coefficients hf).symm (fun _ => a),?_⟩
  simp [constantCoefficient]

theorem constantCoefficient_ne_zero {f : (ZMod p)[X]} (hf : f.Monic)
    (hd : 0<f.natDegree) : constantCoefficient hf hd≠0 := by
  intro h
  obtain ⟨x,hx⟩ := constantCoefficient_surjective hf hd (1 : ZMod p)
  rw [h,LinearMap.zero_apply] at hx
  exact zero_ne_one hx

theorem extension_card {f : (ZMod p)[X]} (hf : f.Monic) :
    Nat.card (AdjoinRoot f)=p^f.natDegree := by
  rw [Nat.card_congr (coefficients hf).toEquiv]
  simp [Nat.card_fun,Nat.card_zmod]

def encode {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) : ℕ :=
  Nat.ofDigits p (List.ofFn fun i => ((coefficients hf) x i).val)

theorem encode_lt {f : (ZMod p)[X]} (hf : f.Monic) (x : AdjoinRoot f) :
    encode hf x<p^f.natDegree := by
  have hp : 1<p := (Fact.out : p.Prime).one_lt
  have h := Nat.ofDigits_lt_base_pow_length hp
    (l := List.ofFn fun i => ((coefficients hf) x i).val) (by
      intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _)
  simpa [encode] using h

theorem encode_injective {f : (ZMod p)[X]} (hf : f.Monic) :
    Function.Injective (encode hf) := by
  intro x y hxy
  have hlist : (List.ofFn fun i => ((coefficients hf) x i).val)=
      (List.ofFn fun i => ((coefficients hf) y i).val) := by
    apply Nat.ofDigits_inj_of_len_eq (Fact.out : p.Prime).one_lt (by simp)
    · intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _
    · intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _
    · exact hxy
  apply (coefficients hf).injective
  funext i
  apply ZMod.val_injective
  have he := congrArg (fun l : List ℕ => l[i.val]?) hlist
  simpa using he

theorem ofDigits_ofFn_mod {d : ℕ} (hd : 0<d) (a : Fin d → ℕ) :
    Nat.ofDigits p (List.ofFn a)%p=a ⟨0,hd⟩%p := by
  cases d with
  | zero => omega
  | succ d => simp [List.ofFn_succ,Nat.ofDigits_cons,Nat.add_mod]

theorem encode_mod {f : (ZMod p)[X]} (hf : f.Monic) (hd : 0<f.natDegree)
    (x : AdjoinRoot f) : encode hf x%p=(constantCoefficient hf hd x).val := by
  rw [encode,ofDigits_ofFn_mod hd]
  rw [Nat.mod_eq_of_lt (ZMod.val_lt _)]
  rfl

def encodedEquiv {f : (ZMod p)[X]} (hf : f.Monic) :
    AdjoinRoot f ≃ Fin (p^f.natDegree) := by
  letI : Fintype (AdjoinRoot f) := Fintype.ofEquiv
    (Fin f.natDegree → ZMod p) (coefficients hf).toEquiv.symm
  exact Equiv.ofBijective (fun x => ⟨encode hf x,encode_lt hf x⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun x y h => encode_injective hf (congrArg Fin.val h),by
        simpa only [Nat.card_eq_fintype_card,Fintype.card_fin] using extension_card hf⟩)

end ThreeSum.TernaryExtensionEncoding
