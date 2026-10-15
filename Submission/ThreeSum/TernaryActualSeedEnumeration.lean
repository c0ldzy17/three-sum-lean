import Submission.ThreeSum.TernaryOriginalKeyCodes
import Submission.ThreeSum.LightExtensionSeedMatrix

noncomputable section
namespace ThreeSum.TernaryActualSeedEnumeration
open TernaryExtensionEncoding Polynomial
open scoped BigOperators
variable {p : ℕ} [Fact p.Prime] {f : (ZMod p)[X]}
variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]
set_option maxHeartbeats 2000000

def equiv (hf : f.Monic) : (AdjoinRoot f×AdjoinRoot f) ≃ Fin ((p^f.natDegree)*(p^f.natDegree)) :=
  (Equiv.prodCongr (encodedEquiv hf) (encodedEquiv hf)).trans finProdFinEquiv

theorem index_value (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val=encode hf y+p^f.natDegree*encode hf x := rfl

theorem index_div (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val/(p^f.natDegree)=encode hf x := by
  rw [index_value,Nat.add_mul_div_left _ _ (by have := (Fact.out : p.Prime).pos; positivity),
    Nat.div_eq_of_lt (encode_lt hf y),Nat.zero_add]

theorem index_mod (hf : f.Monic) (x y : AdjoinRoot f) :
    (equiv hf (x,y)).val%(p^f.natDegree)=encode hf y := by
  rw [index_value,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt (encode_lt hf y)]

/-- The actual integer menu ordinal realizes the original extension-field
row, including its physical reversal of only the digit coordinates. -/
theorem matrix_row (hf : f.Monic) (hd : 0<f.natDegree) (J : ℕ)
    (x y : AdjoinRoot f) (i : Fin (J+2)) :
    LightExtensionSeedMatrix.value (encodedMul hf) (p^f.natDegree) p
      (equiv hf (x,y)).val (TernarySignedLayout.offset J i.val)=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (x,y)
        (digitOrder J i)).val := by
  unfold LightExtensionSeedMatrix.value
  rw [index_div,index_mod]
  exact trajectory_rowMenu hf hd (J+2) x y (digitOrder J i)

/-- Every seed counted in the average is visited once by the actual q²
integer loop, with no omitted or duplicated field pair. -/
theorem sum_rows (hf : f.Monic) (score : Fin ((p^f.natDegree)*(p^f.natDegree))→ℕ) :
    (∑ i, score i)=∑ seed : AdjoinRoot f×AdjoinRoot f, score (equiv hf seed) :=
  (Equiv.sum_comp (equiv hf) score).symm

 theorem exists_good (hf : f.Monic)
    (good : AdjoinRoot f×AdjoinRoot f→Prop) (h : ∃s, good s) :
    ∃i : Fin ((p^f.natDegree)*(p^f.natDegree)), good ((equiv hf).symm i) := by
  obtain ⟨s,hs⟩:=h
  exact ⟨equiv hf s,by simpa only [Equiv.symm_apply_apply] using hs⟩

end ThreeSum.TernaryActualSeedEnumeration
