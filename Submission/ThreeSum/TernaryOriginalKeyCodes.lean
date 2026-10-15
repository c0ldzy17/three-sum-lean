import Submission.ThreeSum.TernaryExtensionSeedSemantics
import Submission.ThreeSum.LightTernaryAppendKeys
import Submission.ThreeSum.TernarySignedLayout

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding
open Polynomial Finset
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

def appendVector {r : ℕ} (v : Fin r → ZMod p) (a : ZMod p) : Fin (r+1) → ZMod p :=
  Fin.lastCases a v

theorem coefficientCode_append {r : ℕ} (v : Fin r → ZMod p) (a : ZMod p) :
    coefficientCode (appendVector v a)=coefficientCode v+p^r*a.val := by
  unfold coefficientCode
  rw [List.ofFn_succ_last]
  simp [appendVector,Nat.ofDigits_append]

theorem packed_keys_equal_iff {r : ℕ} (a b : Fin r → ZMod p) :
    coefficientCode a=coefficientCode b ↔ a=b :=
  (coefficientCode_injective r).eq_iff

def digitOrder (J : ℕ) : Fin (J+2) ≃ Fin (J+2) where
  toFun i := ⟨TernarySignedLayout.offset J i.val,TernarySignedLayout.offset_lt i.isLt⟩
  invFun i := ⟨TernarySignedLayout.offset J i.val,TernarySignedLayout.offset_lt i.isLt⟩
  left_inv i := Fin.ext (TernarySignedLayout.offset_involutive i.isLt)
  right_inv i := Fin.ext (TernarySignedLayout.offset_involutive i.isLt)

theorem physical_dot_eq_logical (J : ℕ) (raw coeff : Fin (J+2) → ZMod p) :
    (∑ i, raw (digitOrder J i)*coeff (digitOrder J i))=∑ i, raw i*coeff i :=
  Equiv.sum_comp (digitOrder J) (fun i => raw i*coeff i)

variable {f : (ZMod p)[X]} [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem physical_original_hash (hf : f.Monic) (hd : 0<f.natDegree) (J : ℕ)
    (x y : AdjoinRoot f) (raw : Fin (J+2) → ℤ) (z : ℕ → ℤ) (c : ℕ → ℕ)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i)).val) :
    LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p))).val := by
  have he : ((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2) : ℕ) : ZMod p)=
      TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i : ZMod p)) := by
    rw [TernaryOriginalRowMenu.row_eq_dot]
    unfold LightNaturalDot.dot LightBooleanDot.dot
    rw [Nat.cast_sum,← Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ i : Fin (J+2), (raw (digitOrder J i) : ZMod p)*
          TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i) := by
        apply sum_congr rfl
        intro i hi
        rw [Nat.cast_mul,hc i,ZMod.natCast_zmod_val]
        have hlift : ((LightSignedRowHash.lifted p (z i.val) : ℕ) : ZMod p)=(raw (digitOrder J i) : ZMod p) := by
          unfold LightSignedRowHash.lifted
          rw [Int.add_comm (p : ℤ)]
          rw [signed_lift_cast _ (by simpa [Int.add_comm] using hzNonneg i.val i.isLt),hz i]
        rw [hlift,mul_comm]
      _ = _ := physical_dot_eq_logical J (fun i => (raw i : ZMod p))
        (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y))
  have hh := congrArg ZMod.val he
  simpa using hh

theorem append_original_key (hf : f.Monic) (hd : 0<f.natDegree) {r J : ℕ}
    (x y : AdjoinRoot f) (raw : Fin (J+2) → ℤ) (z : ℕ → ℤ) (c : ℕ → ℕ)
    (previous : Fin r → ZMod p)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y) (digitOrder J i)).val) :
    LightTernaryAppendKeys.key p (p^r) (J+2) (fun _ => coefficientCode previous)
      (fun _ => z) c 0=
      coefficientCode (appendVector previous
        (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
          (fun i => (raw i : ZMod p)))) := by
  rw [coefficientCode_append]
  unfold LightTernaryAppendKeys.key
  rw [physical_original_hash hf hd J x y raw z c hz hzNonneg hc]

end ThreeSum.TernaryExtensionEncoding
