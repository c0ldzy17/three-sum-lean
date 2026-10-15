import Submission.ThreeSum.TernaryMomentDetectorResources
import Submission.ThreeSum.TernaryPhysicalPairWordBounds
import Submission.ThreeSum.TernaryMomentSchedule

/-! Fixed-degree arithmetic guards for every reporting channel, derived
from actual original source magnitudes and the literal pair-mass bound. -/
noncomputable section
namespace ThreeSum.TernaryMomentChannelResources
open TernaryMomentWeightBounds TernaryNativeMomentBounds StageBounds

def scoreBound (B U K : ℕ) : ℕ :=B*leftBound U K*rightBound U K
def coefficient (K : ℕ) : ℕ :=
  1+2*(2^K+1)*2^K+3+2*(TernaryMomentSchedule.channels (K+1)).length*2^K+(K+1)+10
def need (B U K : ℕ) : Light.Need :=
  ⟨coefficient K*(B+1)*(U+1)^(2*K+1),0,0⟩

theorem score_abs_le {N B U K k j : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (left right : ℕ→ℤ) (hpairs : pairBound S*2^N≤B)
    (hleft : ∀ i<S.left.NL, |left i|≤(U : ℤ))
    (hright : ∀ i<S.right.NL, |right i|≤(U : ℤ)) (hk : k≤K) (hj : j≤k) (i : ℕ) :
    |LightTernaryMomentChannelFactory.score S left right k j i|≤(scoreBound B U K : ℤ) := by
  have hs := TernaryPhysicalPairWordBounds.weighted_abs_le_caps S
    (LightTernaryMomentChannelFactory.leftWeights k j left)
    (LightTernaryMomentChannelFactory.rightWeights k j right) i
    (fun a ha => left_bound (left a) (hleft a ha) hk hj)
    (fun a ha => right_bound (right a) (hright a ha) hk)
  have hm := Nat.mul_le_mul_right (rightBound U K)
    (Nat.mul_le_mul_right (leftBound U K) hpairs)
  exact hs.trans (by exact_mod_cast hm)

private theorem base_bounds (U K : ℕ) :
    U≤(U+1)^(2*K+1) ∧ (U+1)^K≤(U+1)^(2*K+1) ∧
      (U+2)^K≤2^K*(U+1)^(2*K+1) := by
  have hbase : 1≤U+1 := by omega
  have hp := Nat.pow_le_pow_right hbase (show K≤2*K+1 by omega)
  have hU : U+1≤(U+1)^(2*K+1) := by
    simpa using Nat.pow_le_pow_right hbase (show 1≤2*K+1 by omega)
  refine ⟨by omega,hp,?_⟩
  calc
    _≤(2*(U+1))^K := Nat.pow_le_pow_left (by omega) _
    _=2^K*(U+1)^K := mul_pow _ _ _
    _≤_ := Nat.mul_le_mul_left _ hp

theorem left_word_le (B U K : ℕ) : leftWord U K≤(need B U K).word := by
  obtain ⟨hU,hp,h2⟩ := base_bounds U K
  have hm := Nat.mul_le_mul_left (2*(2^K+1)) h2
  have hc : 1+2*(2^K+1)*2^K≤coefficient K*(B+1) := by
    have hB : coefficient K≤coefficient K*(B+1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold coefficient at *
    omega
  have hc' := Nat.mul_le_mul_right ((U+1)^(2*K+1)) hc
  dsimp [leftWord,need]
  nlinarith only [hU,hm,hc']

theorem right_word_le (B U K : ℕ) : rightWord U K≤(need B U K).word := by
  obtain ⟨hU,hp,h2⟩ := base_bounds U K
  have hc : 3≤coefficient K*(B+1) := by
    have hB : coefficient K≤coefficient K*(B+1) := Nat.le_mul_of_pos_right _ (by omega)
    unfold coefficient at *
    omega
  have hc' := Nat.mul_le_mul_right ((U+1)^(2*K+1)) hc
  dsimp [rightWord,need]
  nlinarith only [hU,hp,hc']

theorem add_word_le (B U K : ℕ) :
    2*((TernaryMomentSchedule.channels (K+1)).length*scoreBound B U K)≤(need B U K).word := by
  have hp := Nat.pow_le_pow_right (show 1≤U+1 by omega) (show 2*K≤2*K+1 by omega)
  have hc : 2*(TernaryMomentSchedule.channels (K+1)).length*2^K≤coefficient K := by
    unfold coefficient
    omega
  have hb := Nat.mul_le_mul hc (show B≤B+1 by omega)
  have hh := Nat.mul_le_mul hb hp
  calc
    _=(2*(TernaryMomentSchedule.channels (K+1)).length*2^K*B)*(U+1)^(2*K) := by
      simp only [scoreBound,leftBound,rightBound,two_mul,pow_add]
      ring
    _≤_ := hh

theorem terms_word_le (B U K : ℕ) : K+1≤(need B U K).word := by
  have hc : K+1≤coefficient K := by unfold coefficient; omega
  have hB : coefficient K≤coefficient K*(B+1) := Nat.le_mul_of_pos_right _ (by omega)
  exact (hc.trans hB).trans (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (by omega)))

theorem polyNeed {B : ℕ→ℕ} {a : ℝ} (hB : PowerBound B a) (K : ℕ) :
    Light.PolyNeed (fun n U => need (B n) U K) := by
  let q := max a 0
  have hb : PowerBound B q := hB.mono_exponent (le_max_left _ _)
  have h1 : PowerBound (fun n => B n+1) q :=
    hb.add_same ((PowerBound.const 1).mono_exponent (le_max_right _ _))
  have hc : PowerBound (fun n => coefficient K*(B n+1)) q := by
    simpa using (PowerBound.const (coefficient K)).mul h1
  apply PolynomialResources.polyNeed_of_envelope hc (2*K+1)
  · intro n U
    exact le_rfl
  · intro n U
    exact Nat.zero_le _
  · intro n U
    exact Nat.zero_le _

end ThreeSum.TernaryMomentChannelResources
