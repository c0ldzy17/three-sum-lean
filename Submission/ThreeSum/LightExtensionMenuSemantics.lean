import Submission.ThreeSum.LightExtensionFieldMultiply
import Submission.ThreeSum.LightExtensionMenuMatrix

noncomputable section
namespace ThreeSum.LightExtensionMenuMatrix
open TernaryExtensionEncoding
set_option maxHeartbeats 2000000
variable {p : ℕ} [Fact p.Prime] {f : Polynomial (ZMod p)}

def seed (hf : f.Monic) (r : ℕ) (hr : r < (p^f.natDegree)*(p^f.natDegree)) :
    AdjoinRoot f × AdjoinRoot f :=
  let q := p^f.natDegree
  let hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  ((encodedEquiv hf).symm ⟨r/q,(Nat.div_lt_iff_lt_mul hq).mpr hr⟩,
   (encodedEquiv hf).symm ⟨r%q,Nat.mod_lt r hq⟩)

variable [Fact (Irreducible f)] [Fintype (AdjoinRoot f)]

theorem value_is_rowMenu (hf : f.Monic) (hd : 0 < f.natDegree)
    (J r : ℕ) (hr : r < (p^f.natDegree)*(p^f.natDegree)) {i : ℕ} (hi : i < J+2) :
    LightExtensionSeedMatrix.value (encodedMul hf) (p^f.natDegree) p r
      (TernarySignedLayout.offset J i)=
      (TernaryOriginalRowMenu.seedRow (J+2) (constantCoefficient hf hd) (seed hf r hr)
        ⟨TernarySignedLayout.offset J i,TernarySignedLayout.offset_lt hi⟩).val := by
  let q := p^f.natDegree
  have hq : 0 < q := pow_pos (Fact.out : p.Prime).pos _
  have hx : r/q < q := (Nat.div_lt_iff_lt_mul hq).mpr hr
  have hy : r%q < q := Nat.mod_lt r hq
  have hex : encode hf ((encodedEquiv hf).symm ⟨r/q,hx⟩)=r/q := by
    exact congrArg Fin.val ((encodedEquiv hf).apply_symm_apply ⟨r/q,hx⟩)
  have hey : encode hf ((encodedEquiv hf).symm ⟨r%q,hy⟩)=r%q := by
    exact congrArg Fin.val ((encodedEquiv hf).apply_symm_apply ⟨r%q,hy⟩)
  have h := trajectory_rowMenu hf hd (J+2)
    ((encodedEquiv hf).symm ⟨r/q,hx⟩) ((encodedEquiv hf).symm ⟨r%q,hy⟩)
    ⟨TernarySignedLayout.offset J i,TernarySignedLayout.offset_lt hi⟩
  rw [hex,hey] at h
  exact h

/-- Reversing digit coordinates while keeping both tags fixed preserves a dot product. -/
theorem dot_offset (J : ℕ) (f g : ℕ → ℕ) :
    LightNaturalDot.dot (fun i => f (TernarySignedLayout.offset J i))
      (fun i => g (TernarySignedLayout.offset J i)) (J+2)=LightNaturalDot.dot f g (J+2) := by
  unfold LightNaturalDot.dot LightBooleanDot.dot
  apply Finset.sum_bij (fun i _ => TernarySignedLayout.offset J i)
  · intro i hi
    exact Finset.mem_range.mpr (TernarySignedLayout.offset_lt (Finset.mem_range.mp hi))
  · intro i hi j hj hij
    have h := congrArg (TernarySignedLayout.offset J) hij
    rwa [TernarySignedLayout.offset_involutive (Finset.mem_range.mp hi),
      TernarySignedLayout.offset_involutive (Finset.mem_range.mp hj)] at h
  · intro j hj
    refine ⟨TernarySignedLayout.offset J j,
      Finset.mem_range.mpr (TernarySignedLayout.offset_lt (Finset.mem_range.mp hj)),?_⟩
    exact TernarySignedLayout.offset_involutive (Finset.mem_range.mp hj)
  · intro i hi
    rfl


/-- The exact integer hash returned by SignedRowHash is the original logical row functional. -/
theorem signed_physical_hash (hf : f.Monic) (hd : 0 < f.natDegree)
    (J : ℕ) (x y : AdjoinRoot f) (raw : ℕ → ℤ)
    (hlift : ∀ i < J+2, 0 ≤ (p : ℤ)+raw i) :
    LightNaturalDot.dot
      (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y)
        (TernarySignedLayout.offset J i)%p)
      (fun i => ((p : ℤ)+raw (TernarySignedLayout.offset J i)).toNat) (J+2)%p=
      (TernaryOriginalRowMenu.row (J+2) (constantCoefficient hf hd) (x,y)
        (fun i => (raw i.val : ZMod p))).val := by
  rw [dot_offset J
    (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i%p)
    (fun i => ((p : ℤ)+raw i).toNat)]
  have hcomm : LightNaturalDot.dot
      (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i%p)
      (fun i => ((p : ℤ)+raw i).toNat) (J+2)=
    LightNaturalDot.dot (fun i => ((p : ℤ)+raw i).toNat)
      (fun i => LightExtensionSeedRow.trajectory (encodedMul hf) (encode hf x) (encode hf y) i%p) (J+2) := by
    unfold LightNaturalDot.dot LightBooleanDot.dot
    apply Finset.sum_congr rfl
    intro i hi
    exact Nat.mul_comm _ _
  rw [hcomm]
  apply naturalDot_rowMenu hf hd (J+2) x y (fun i => raw i.val)
  · intro i
    have h := signed_lift_cast (p := p) (raw i.val) (by simpa [add_comm] using hlift i.val i.isLt)
    simpa [add_comm] using h
  · intro i
    rfl

end ThreeSum.LightExtensionMenuMatrix
