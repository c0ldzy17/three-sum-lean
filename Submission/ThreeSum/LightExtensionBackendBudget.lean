import Submission.ThreeSum.LightExtensionBackend
import Submission.ThreeSum.LightIrreducibleBudget
import Submission.ThreeSum.LightExtensionMenuBudget

namespace ThreeSum.LightExtensionBackend
set_option maxHeartbeats 2000000

/-- The complete actual field construction and physical menu construction
cost a fixed polynomial, independent of every absolute memory address. -/
theorem time_polynomial (F : LightExtensionFactorPredicate.Layout)
    (q J a b h r prod sum : ℕ) :
    time F q J a b h r prod sum (LightIrreducibleFinder.uniformFactorTime F.dim F.p q) ≤
      10000000000*(F.dim+F.p+q+J+2)^10 := by
  let B := F.dim+F.p+q+J+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hsmall : F.dim+F.p+q+2 ≤ B := by dsimp [B]; omega
  have hf := LightIrreducibleFinder.setupTime_polynomial F q
  have hf' : LightIrreducibleFinder.setupTime F q (LightIrreducibleFinder.uniformFactorTime F.dim F.p q) ≤
      1000000000*B^10 := hf.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hsmall 10))
  have hm := LightExtensionMenuMatrix.time_polynomial (quotientLayout F a b h r prod sum) q J
  have hm' : LightExtensionMenuMatrix.time (quotientLayout F a b h r prod sum) q J ≤
      1000000000*B^8 := by simpa only [quotientLayout] using hm
  have hp : B^8 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h1 : 1 ≤ B^10 := Nat.one_le_pow _ _ hB
  unfold time
  change _ ≤ 10000000000*B^10
  omega

end ThreeSum.LightExtensionBackend
