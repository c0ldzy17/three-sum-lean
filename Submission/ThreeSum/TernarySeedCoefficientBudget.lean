import Submission.ThreeSum.TernaryActualPrefixRuntime
import Submission.ThreeSum.LightTernaryWantedBudget

noncomputable section
namespace ThreeSum.TernarySeedCoefficientBudget
open TernaryActualPrefixRuntime
set_option maxHeartbeats 6000000

/-- The actual signed row hash has linear digit-length cost at fixed
native prime and signed digit bound. -/
theorem hash_linear (J p B : ℕ) :
    LightSignedRowHash.time (J+2) p B+120≤
      (596+80*p*(p+B))*(J+1) := by
  unfold LightSignedRowHash.time LightReportingAffine.time LightNaturalDot.reducedTime
    LightNaturalDot.time LightBooleanDot.time
  nlinarith [Nat.zero_le (p*(p+B)*J)]

/-- Only the logarithm of the full signed-target envelope enters each
wanted DFS node, so all prefix overhead remains quadratic in J. -/
theorem wanted_quadratic (p A J j : ℕ) (hj : j≤J) :
    (LightTernaryWantedCanonical.overhead p (A*(p+1)^j)+
      LightTernaryWantedCanonical.stepCost (A*(p+1)^j)+40)*(j+1)≤
      (1000*(A+2*p+4))*(J+1)^2 := by
  have hA : A≤2^A := (Nat.lt_two_pow_self).le
  have hP : p+1≤2^(p+1) := (Nat.lt_two_pow_self).le
  have hv : A*(p+1)^j≤2^(A+(p+1)*j) := by
    calc
      _≤2^A*(2^(p+1))^j := Nat.mul_le_mul hA (Nat.pow_le_pow_left hP j)
      _=_ := by rw [←pow_mul,←pow_add]
  have hn := LightTernaryWantedBudget.node_budget p (A*(p+1)^j) (A+(p+1)*j) hv
  have hlin : p+(A+(p+1)*j)+3≤(A+2*p+4)*(J+1) := by nlinarith
  have hlin' := hn.trans (Nat.mul_le_mul_left 1000 hlin)
  have hh := Nat.mul_le_mul hlin' (Nat.add_le_add_right hj 1)
  nlinarith only [hh]

/-- The complete real per-seed coefficient is polynomial in digit length,
uniformly over every prefix. No signed target or hash call is unit-cost. -/
theorem seed_coefficient_polynomial (K p B A : ℕ) :
    ∃ C d : ℕ, ∀J j, j≤J→
      seedCoefficient K J p B (A*(p+1)^j) j≤C*(J+1)^d := by
  obtain ⟨T,e,hT⟩ := tensor_coefficient_polynomial K
  let d:=max 2 e
  let H:=596+80*p*(p+B)
  let W:=1000*(A+2*p+4)
  refine ⟨11000+H+W+T,d,fun J j hj=>?_⟩
  have hbase : 1≤J+1 := by omega
  have h1 : 1≤(J+1)^d := Nat.one_le_pow _ _ hbase
  have hlin : J+1≤(J+1)^d := by
    simpa only [pow_one] using Nat.pow_le_pow_right hbase (show 1≤d by dsimp [d]; omega)
  have hquad : (J+1)^2≤(J+1)^d := Nat.pow_le_pow_right hbase (le_max_left _ _)
  have hten : (J+1)^e≤(J+1)^d := Nat.pow_le_pow_right hbase (le_max_right _ _)
  have hh := (hash_linear J p B).trans (Nat.mul_le_mul_left H hlin)
  have hw := (wanted_quadratic p A J j hj).trans (Nat.mul_le_mul_left W hquad)
  have ht := (hT J).trans (Nat.mul_le_mul_left T hten)
  have hc := Nat.mul_le_mul_left 11000 hlin
  unfold seedCoefficient
  dsimp only [H,W] at hh hw ⊢
  nlinarith only [hh,hw,ht,hc]

end ThreeSum.TernarySeedCoefficientBudget
