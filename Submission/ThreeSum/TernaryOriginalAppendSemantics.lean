import Submission.ThreeSum.TernaryOriginalKeyCodes
import Submission.ThreeSum.TernaryOriginalCollisions

noncomputable section
namespace ThreeSum.TernaryOriginalAppendSemantics
open Finset TernaryOriginalRowMenu TernaryExtensionEncoding
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 3000000

theorem physical_hash (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (J : ℕ)
    (raw : Fin (J+2)→ℤ) (z : ℕ→ℤ) (c : ℕ→ℕ)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=(seedRow (J+2) ℓ seed (digitOrder J i)).val) :
    LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) ℓ seed (fun i => (raw i : ZMod p))).val := by
  have he : ((LightNaturalDot.dot c (fun k => LightSignedRowHash.lifted p (z k)) (J+2) : ℕ) : ZMod p)=
      TernaryOriginalRowMenu.row (J+2) ℓ seed (fun i => (raw i : ZMod p)) := by
    rw [TernaryOriginalRowMenu.row_eq_dot]
    unfold LightNaturalDot.dot LightBooleanDot.dot
    rw [Nat.cast_sum,←Fin.sum_univ_eq_sum_range]
    calc
      _ = ∑ i : Fin (J+2), (raw (digitOrder J i) : ZMod p)*seedRow (J+2) ℓ seed (digitOrder J i) := by
        apply sum_congr rfl
        intro i hi
        rw [Nat.cast_mul,hc i,ZMod.natCast_zmod_val]
        have hlift : ((LightSignedRowHash.lifted p (z i.val) : ℕ) : ZMod p)=(raw (digitOrder J i) : ZMod p) := by
          unfold LightSignedRowHash.lifted
          rw [Int.add_comm (p : ℤ)]
          rw [signed_lift_cast _ (by simpa [Int.add_comm] using hzNonneg i.val i.isLt),hz i]
        rw [hlift,mul_comm]
      _ = _ := physical_dot_eq_logical J (fun i => (raw i : ZMod p)) (seedRow (J+2) ℓ seed)
  simpa using congrArg ZMod.val he

theorem append_key (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) {r J : ℕ}
    (raw : Fin (J+2)→ℤ) (z : ℕ→ℤ) (c : ℕ→ℕ) (previous : Fin r→ZMod p)
    (hz : ∀ i : Fin (J+2), z i.val=raw (digitOrder J i))
    (hzNonneg : ∀ i<J+2, 0≤(p : ℤ)+z i)
    (hc : ∀ i : Fin (J+2), c i.val=(seedRow (J+2) ℓ seed (digitOrder J i)).val) :
    LightTernaryAppendKeys.key p (p^r) (J+2) (fun _ => coefficientCode previous) (fun _ => z) c 0=
      coefficientCode (appendVector previous (TernaryOriginalRowMenu.row (J+2) ℓ seed (fun i => (raw i : ZMod p)))) := by
  rw [coefficientCode_append]
  unfold LightTernaryAppendKeys.key
  rw [physical_hash ℓ seed J raw z c hz hzNonneg hc]

theorem appended_code_eq_iff {r : ℕ} (a b : Fin r→ZMod p) (x y : ZMod p) :
    coefficientCode (appendVector a x)=coefficientCode (appendVector b y) ↔ a=b ∧ x=y := by
  rw [(coefficientCode_injective (r+1)).eq_iff]
  constructor
  · intro he
    refine ⟨funext (fun j => by simpa [appendVector] using congrFun he j.castSucc),?_⟩
    simpa [appendVector] using congrFun he (Fin.last r)
  · rintro ⟨rfl,rfl⟩
    rfl

theorem collision_count {B : Type*} [Fintype B] [DecidableEq B] {r Λ : ℕ}
    (ℓ : E→ₗ[ZMod p] ZMod p) (v : B→Fin Λ→ZMod p) (hash : B→Fin r→ZMod p) (seed : E×E) :
    (TernaryOriginalCollisions.collisionPairs (fun i => coefficientCode
      (appendVector (hash i) (TernaryOriginalRowMenu.row Λ ℓ seed (v i))))).card=
        TernaryOriginalCollisions.nextCollisions ℓ v hash seed := by
  congr 1
  ext ab
  simp only [TernaryOriginalCollisions.collisionPairs,TernaryOriginalCollisions.nextCollisions,
    mem_filter,mem_univ,true_and,appended_code_eq_iff]
  tauto

end ThreeSum.TernaryOriginalAppendSemantics
