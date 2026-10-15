import Submission.ThreeSum.TernaryNativeMomentBounds

/-! Shared signed-weight bounds for both actual moment channels and actual
fourth-tensor channels of the source/count host. -/
noncomputable section
namespace ThreeSum.TernaryPhysicalPairWordBounds
open Finset TernaryNativePairMoments TernaryNativeMomentBounds
open scoped BigOperators

def weighted {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ) : ℤ :=
  TernaryConvolution.factorial (S.front.Q i)*
    TernaryWeightedPhysicalSources.pairWeight
      (leftSet S i) (rightSet S i) (leftWord S) (rightWord S)
      (fun pair => leftWeight pair.1) (fun pair => rightWeight pair.1) (S.front.Q i)

theorem weighted_as_pairs {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ) :
    weighted S leftWeight rightWeight i=
      ∑ p : Pair S i, mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1 := by
  classical
  unfold weighted TernaryWeightedPhysicalSources.pairWeight
  have hs := TernaryPhysicalTensorChannels.sum_records (leftSet S i) (rightSet S i)
    (leftWord S) (rightWord S) (S.front.Q i) (fun p => leftWeight p.1.1*rightWeight p.2.1)
  calc
    _=TernaryConvolution.factorial (S.front.Q i)*
        ∑ p : Pair S i, leftWeight p.val.1.1*rightWeight p.val.2.1 :=
      congrArg (fun z : ℤ => TernaryConvolution.factorial (S.front.Q i)*z) hs.symm
    _=_ := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro p hp
      dsimp only [mass]
      ring

theorem weighted_abs_le {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (hL : ∀ a<S.left.NL, |leftWeight a|≤(S.left.weightU : ℤ))
    (hR : ∀ a<S.right.NL, |rightWeight a|≤(S.right.weightU : ℤ)) :
    |weighted S leftWeight rightWeight i|≤(scoreBound S : ℤ) := by
  classical
  rw [weighted_as_pairs]
  have hterm (p : Pair S i) : |mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1|≤
      (2 : ℤ)^N*S.left.weightU*S.right.weightU := by
    rw [abs_mul,abs_mul]
    have hp := indices_lt p
    have hm : |mass S i p|≤(2 : ℤ)^N := by
      rw [abs_of_pos (mass_positive S i p)]
      exact factorial_le _
    exact mul_le_mul (mul_le_mul hm (hL _ hp.1) (abs_nonneg _) (by positivity))
      (hR _ hp.2) (abs_nonneg _) (by positivity)
  have hs : |∑ p : Pair S i, mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1|≤
      (Fintype.card (Pair S i) : ℤ)*((2 : ℤ)^N*S.left.weightU*S.right.weightU) := by
    calc
      _≤∑ p : Pair S i, |mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1| := abs_sum_le_sum_abs _ _
      _≤∑ _p : Pair S i, (2 : ℤ)^N*S.left.weightU*S.right.weightU := sum_le_sum (fun p hp => hterm p)
      _=_ := by simp
  have hc : (Fintype.card (Pair S i) : ℤ)≤(pairBound S : ℤ) := by exact_mod_cast pair_card_le S i
  have hm := mul_le_mul_of_nonneg_right hc
    (show (0 : ℤ)≤2^N*S.left.weightU*S.right.weightU by positivity)
  unfold scoreBound
  push_cast
  exact hs.trans (by nlinarith only [hm])

theorem weighted_abs_le_of_seed {N d boundary : ℕ} {lim : Light.Limits}
    (S : TernarySourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (H : TernarySourceCountExecutionFactory.Seed S lim d boundary μ leftWeight rightWeight) :
    |weighted S leftWeight rightWeight i|≤(scoreBound S : ℤ) :=
  weighted_abs_le S leftWeight rightWeight i H.left.hweightBound H.right.hweightBound

/-- Independent numeric caps allow the final caller to choose uniform
source-weight bounds before constructing the per-channel source setups. -/
theorem weighted_abs_le_caps {N U V : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (leftWeight rightWeight : ℕ→ℤ) (i : ℕ)
    (hL : ∀ a<S.left.NL, |leftWeight a|≤(U : ℤ))
    (hR : ∀ a<S.right.NL, |rightWeight a|≤(V : ℤ)) :
    |weighted S leftWeight rightWeight i|≤(pairBound S*2^N*U*V : ℕ) := by
  classical
  rw [weighted_as_pairs]
  have hterm (p : Pair S i) : |mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1|≤
      (2 : ℤ)^N*U*V := by
    rw [abs_mul,abs_mul]
    have hp := indices_lt p
    have hm : |mass S i p|≤(2 : ℤ)^N := by
      rw [abs_of_pos (mass_positive S i p)]
      exact factorial_le _
    exact mul_le_mul (mul_le_mul hm (hL _ hp.1) (abs_nonneg _) (by positivity))
      (hR _ hp.2) (abs_nonneg _) (by positivity)
  have hs : |∑ p : Pair S i, mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1|≤
      (Fintype.card (Pair S i) : ℤ)*((2 : ℤ)^N*U*V) := by
    calc
      _≤∑ p : Pair S i, |mass S i p*leftWeight p.val.1.1*rightWeight p.val.2.1| := abs_sum_le_sum_abs _ _
      _≤∑ _p : Pair S i, (2 : ℤ)^N*U*V := sum_le_sum (fun p hp => hterm p)
      _=_ := by simp
  have hc : (Fintype.card (Pair S i) : ℤ)≤(pairBound S : ℤ) := by exact_mod_cast pair_card_le S i
  have hm := mul_le_mul_of_nonneg_right hc (show (0 : ℤ)≤2^N*U*V by positivity)
  push_cast
  exact hs.trans (by nlinarith only [hm])

end ThreeSum.TernaryPhysicalPairWordBounds
