import Submission.ThreeSum.TernaryNativePairMoments
import Submission.ThreeSum.LightMomentDeterminant

/-! Explicit ordinary-integer bounds for the physical moments and signed
channels; these are word bounds, not additional runtime charges. -/
noncomputable section
namespace ThreeSum.TernaryNativeMomentBounds
open Finset TernaryJointType TernaryNativePairMoments
open scoped BigOperators

def pairBound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) : ℕ :=
  (S.left.NL*LightTernarySourceHost.size S.left.xs S.left.J)*
  (S.right.NL*LightTernarySourceHost.size S.right.xs S.right.J)

theorem source_card_le (S : TernarySourceExecutionFactory.Setup) :
    S.records.card≤S.NL*LightTernarySourceHost.size S.xs S.J := by
  calc
    _≤((range S.NL).product (range (LightTernarySourceHost.size S.xs S.J))).card := card_filter_le _ _
    _=_ := by simp

theorem pair_card_le {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (i : ℕ) :
    Fintype.card (Pair S i)≤pairBound S := by
  classical
  have hl : (leftSet S i).card≤S.left.NL*LightTernarySourceHost.size S.left.xs S.left.J :=
    (card_filter_le _ _).trans (source_card_le S.left)
  have hr : (rightSet S i).card≤S.right.NL*LightTernarySourceHost.size S.right.xs S.right.J :=
    (card_filter_le _ _).trans (source_card_le S.right)
  have hp : (pairs S i).card≤(leftSet S i).card*(rightSet S i).card := by
    calc
      _≤((leftSet S i)×ˢ(rightSet S i)).card := card_filter_le _ _
      _=_ := card_product _ _
  simpa only [Pair,Fintype.card_coe,pairBound] using hp.trans (Nat.mul_le_mul hl hr)

theorem indices_lt {N : ℕ} {S : TernarySourceCountExecutionFactory.Setup N} {i : ℕ}
    (p : Pair S i) : p.val.1.1<S.left.NL ∧ p.val.2.1<S.right.NL := by
  classical
  have hp := p.property
  change p.val∈((leftSet S i)×ˢ(rightSet S i)).filter
    (fun x => TernaryConvolution.Adds (leftWord S x.1) (rightWord S x.2) (S.front.Q i)) at hp
  have ht := mem_product.mp (mem_filter.mp hp).1
  have hl := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp (mem_filter.mp ht.1).1
  have hr := (TernarySourceHostModel.mem_records _ _ _ _ _ _).mp (mem_filter.mp ht.2).1
  exact ⟨hl.1,hr.1⟩

theorem factorial_le {N : ℕ} (Q : TritWord N) : TernaryConvolution.factorial Q≤(2 : ℤ)^N := by
  calc
    _=∏ i, ((Q i).val.factorial : ℤ) := rfl
    _≤∏ _i : Fin N, (2 : ℤ) := by
      apply prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        rcases Q i with ⟨n,hn⟩
        interval_cases n <;> norm_num
    _=_ := by simp

theorem mode_abs_le {N U : ℕ} {S : TernarySourceCountExecutionFactory.Setup N} {i : ℕ}
    (B C : ℕ→ℤ) (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ))
    (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) (p : Pair S i) :
    |mode B C p|≤2*(U : ℤ) := by
  have hp := indices_lt p
  have ht := abs_sub_le (C p.val.2.1) 0 (B p.val.1.1)
  simp only [sub_zero,zero_sub,abs_neg] at ht
  exact ht.trans (by have := hC _ hp.2; have := hB _ hp.1; omega)

def momentBound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (U K : ℕ) : ℕ :=
  pairBound S*2^N*(2*U+1)^K

theorem moment_abs_le {N U K k : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (i : ℕ) (hk : k≤K)
    (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ)) (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) :
    |∑ p : Pair S i, mass S i p*mode B C p^k|≤(momentBound S U K : ℤ) := by
  classical
  have hpow (p : Pair S i) : |mode B C p|^k≤(2*(U : ℤ)+1)^K := by
    have hp := mode_abs_le B C hB hC p
    exact (pow_le_pow_left₀ (abs_nonneg _) (show |mode B C p|≤2*(U : ℤ)+1 by omega) k).trans
      (pow_le_pow_right₀ (by omega) hk)
  have hmass (p : Pair S i) : |mass S i p|≤(2 : ℤ)^N := by
    rw [abs_of_pos (mass_positive S i p)]
    exact factorial_le _
  have hs : |∑ p : Pair S i, mass S i p*mode B C p^k|≤
      (Fintype.card (Pair S i) : ℤ)*((2 : ℤ)^N*(2*(U : ℤ)+1)^K) := by
    calc
      _≤∑ p : Pair S i, |mass S i p*mode B C p^k| := abs_sum_le_sum_abs _ _
      _≤∑ _p : Pair S i, (2 : ℤ)^N*(2*(U : ℤ)+1)^K := by
        apply sum_le_sum
        intro p hp
        rw [abs_mul,abs_pow]
        exact mul_le_mul (hmass p) (hpow p) (by positivity) (by positivity)
      _=_ := by simp
  have hc : (Fintype.card (Pair S i) : ℤ)≤(pairBound S : ℤ) := by exact_mod_cast pair_card_le S i
  have hm := mul_le_mul_of_nonneg_right hc (show (0 : ℤ)≤2^N*(2*(U : ℤ)+1)^K by positivity)
  unfold momentBound
  push_cast
  exact hs.trans (by nlinarith only [hm])

def scoreBound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) : ℕ :=
  pairBound S*2^N*S.left.weightU*S.right.weightU

theorem score_as_pairs {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k j i : ℕ) :
    LightTernaryMomentChannelFactory.score S B C k j i=
      ∑ p : Pair S i, mass S i p*
        LightTernaryMomentChannelFactory.leftWeights k j B p.val.1.1*
        LightTernaryMomentChannelFactory.rightWeights k j C p.val.2.1 := by
  classical
  unfold LightTernaryMomentChannelFactory.score TernaryWeightedPhysicalSources.pairWeight
  have hs := TernaryPhysicalTensorChannels.sum_records (leftSet S i) (rightSet S i)
    (leftWord S) (rightWord S) (S.front.Q i)
      (fun p => LightTernaryMomentChannelFactory.leftWeights k j B p.1.1*
        LightTernaryMomentChannelFactory.rightWeights k j C p.2.1)
  calc
    _=TernaryConvolution.factorial (S.front.Q i)*
        ∑ p : Pair S i, LightTernaryMomentChannelFactory.leftWeights k j B p.val.1.1*
          LightTernaryMomentChannelFactory.rightWeights k j C p.val.2.1 :=
      congrArg (fun z : ℤ => TernaryConvolution.factorial (S.front.Q i)*z) hs.symm
    _=_ := by
      rw [Finset.mul_sum]
      apply sum_congr rfl
      intro p hp
      dsimp only [mass]
      ring

theorem score_abs_le {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (k j i : ℕ)
    (hL : ∀ a<S.left.NL, |LightTernaryMomentChannelFactory.leftWeights k j B a|≤(S.left.weightU : ℤ))
    (hR : ∀ a<S.right.NL, |LightTernaryMomentChannelFactory.rightWeights k j C a|≤(S.right.weightU : ℤ)) :
    |LightTernaryMomentChannelFactory.score S B C k j i|≤(scoreBound S : ℤ) := by
  classical
  rw [score_as_pairs]
  have hterm (p : Pair S i) :
      |mass S i p*LightTernaryMomentChannelFactory.leftWeights k j B p.val.1.1*
        LightTernaryMomentChannelFactory.rightWeights k j C p.val.2.1|≤
        (2 : ℤ)^N*S.left.weightU*S.right.weightU := by
    rw [abs_mul,abs_mul]
    have hp := indices_lt p
    have hm : |mass S i p|≤(2 : ℤ)^N := by
      rw [abs_of_pos (mass_positive S i p)]
      exact factorial_le _
    exact mul_le_mul
      (mul_le_mul hm (hL _ hp.1) (abs_nonneg _) (by positivity)) (hR _ hp.2)
      (abs_nonneg _) (by positivity)
  have hs : |∑ p : Pair S i, mass S i p*
        LightTernaryMomentChannelFactory.leftWeights k j B p.val.1.1*
        LightTernaryMomentChannelFactory.rightWeights k j C p.val.2.1|≤
        (Fintype.card (Pair S i) : ℤ)*((2 : ℤ)^N*S.left.weightU*S.right.weightU) := by
    calc
      _≤∑ p : Pair S i, |mass S i p*
        LightTernaryMomentChannelFactory.leftWeights k j B p.val.1.1*
        LightTernaryMomentChannelFactory.rightWeights k j C p.val.2.1| := abs_sum_le_sum_abs _ _
      _≤∑ _p : Pair S i, (2 : ℤ)^N*S.left.weightU*S.right.weightU := sum_le_sum (fun p hp => hterm p)
      _=_ := by simp
  have hc : (Fintype.card (Pair S i) : ℤ)≤(pairBound S : ℤ) := by exact_mod_cast pair_card_le S i
  have hm := mul_le_mul_of_nonneg_right hc
    (show (0 : ℤ)≤2^N*S.left.weightU*S.right.weightU by positivity)
  unfold scoreBound
  push_cast
  exact hs.trans (by nlinarith only [hm])

theorem score_abs_le_of_seed {N d boundary : ℕ} {lim : Light.Limits}
    (S : TernarySourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (B C : ℕ→ℤ) (k j i : ℕ)
    (H : TernarySourceCountExecutionFactory.Seed S lim d boundary μ
      (LightTernaryMomentChannelFactory.leftWeights k j B)
      (LightTernaryMomentChannelFactory.rightWeights k j C)) :
    |LightTernaryMomentChannelFactory.score S B C k j i|≤(scoreBound S : ℤ) :=
  score_abs_le S B C k j i H.left.hweightBound H.right.hweightBound

def detectorInput {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (U H : ℕ) : ℕ :=
  U+momentBound S U (2*H)

def detectorWord (x H : ℕ) : ℕ :=
  ((LightMomentDeterminant.wordCoefficient H).toNat+1)*
    (x+1)^(LightMomentDeterminant.wordDegree H+1)

/-- The detector's complete arithmetic guard is a fixed polynomial in its
explicit input magnitude bound. Its coefficient and degree depend only on H. -/
theorem detector_word_bound (x H : ℕ) :
    max (x : ℤ) (LightMomentDeterminant.wordBound x H)≤(detectorWord x H : ℤ) := by
  have hc := LightMomentDeterminant.wordCoefficient_pos H
  have hcoef : ((LightMomentDeterminant.wordCoefficient H).toNat : ℤ)=
      LightMomentDeterminant.wordCoefficient H := Int.toNat_of_nonneg (by omega)
  have hx : (1 : ℤ)≤x+1 := by omega
  have hp := pow_le_pow_right₀ hx (show LightMomentDeterminant.wordDegree H≤
    LightMomentDeterminant.wordDegree H+1 by omega)
  have hp1 : (x : ℤ)+1≤((x : ℤ)+1)^(LightMomentDeterminant.wordDegree H+1) := by
    simpa using pow_le_pow_right₀ hx (show 1≤LightMomentDeterminant.wordDegree H+1 by omega)
  have hp0 : (0 : ℤ)≤((x : ℤ)+1)^(LightMomentDeterminant.wordDegree H+1) := by positivity
  have hw := LightMomentDeterminant.wordBound_polynomial H (U := (x : ℤ)) (by positivity)
  have hmul := mul_le_mul_of_nonneg_left hp (show 0≤LightMomentDeterminant.wordCoefficient H by omega)
  unfold detectorWord
  push_cast
  rw [hcoef]
  apply max_le <;> nlinarith

theorem detector_moments_bound {N U H : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (B C : ℕ→ℤ) (hB : ∀ j<S.left.NL, |B j|≤(U : ℤ))
    (hC : ∀ j<S.right.NL, |C j|≤(U : ℤ)) :
    ∀ i, ∀ k≤2*H, |∑ p : Pair S i, mass S i p*mode B C p^k|≤(detectorInput S U H : ℤ) := by
  intro i k hk
  exact (moment_abs_le S B C i hk hB hC).trans (by unfold detectorInput; push_cast; omega)

end ThreeSum.TernaryNativeMomentBounds
