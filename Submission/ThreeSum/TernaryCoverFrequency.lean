import Submission.ThreeSum.TernaryCoverGoodMaps
import Submission.ThreeSum.Greedy
import Submission.ThreeSum.TernaryPartitionCount

/-! # Support frequency and deterministic greedy coverage -/

noncomputable section
namespace ThreeSum.TernaryCoverFrequency

open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps
open scoped BigOperators

theorem support_frequency {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (f : Ω → ℕ) (N p C a : ℕ) (hN : 0 < N)
    (hfirst : N * Fintype.card Ω ≤ 2*p^2*∑ w, f w)
    (hsecond : (∑ w, f w^2) ≤ C*Fintype.card Ω)
    (hscale : 4*p^4*C ≤ a*N^2) :
    Fintype.card Ω ≤ a * (univ.filter fun w => f w ≠ 0).card := by
  classical
  let g : Ω → ℝ := fun w => (f w : ℝ)
  have hW : (0 : ℝ) < Fintype.card Ω := by exact_mod_cast Fintype.card_pos
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hfirstR : (N : ℝ)*Fintype.card Ω ≤ 2*(p : ℝ)^2*∑ w, g w := by
    dsimp [g]
    exact_mod_cast hfirst
  have hsecondR : (∑ w, g w^2) ≤ (C : ℝ)*Fintype.card Ω := by
    dsimp [g]
    exact_mod_cast hsecond
  have hscaleR : 4*(p : ℝ)^4*C ≤ (a : ℝ)*(N : ℝ)^2 := by exact_mod_cast hscale
  have hG : (0 : ℝ) ≤ ∑ w, g w := sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  let supp := (univ.filter fun w => g w ≠ 0).card
  have hs : (∑ w, g w)^2 ≤ (supp : ℝ)*(∑ w, g w^2) := Cover.support_cauchy g
  have hsup : (0 : ℝ) ≤ supp := Nat.cast_nonneg _
  have hbound := mul_le_mul_of_nonneg_left hsecondR hsup
  have hsq : ((N : ℝ)*Fintype.card Ω)^2 ≤ 4*(p : ℝ)^4*(∑ w, g w)^2 := by
    have h := (sq_le_sq₀ (by positivity : (0 : ℝ) ≤ (N : ℝ)*Fintype.card Ω)
      (by positivity : (0 : ℝ) ≤ 2*(p : ℝ)^2*∑ w, g w)).mpr hfirstR
    have he : (2*(p : ℝ)^2*∑ w, g w)^2 = 4*(p : ℝ)^4*(∑ w, g w)^2 := by ring
    rw [he] at h
    exact h
  have hraw : (N : ℝ)^2*Fintype.card Ω ≤ 4*(p : ℝ)^4*C*(supp : ℝ) := by
    apply (mul_le_mul_iff_left₀ hW).mp
    have hc := mul_le_mul_of_nonneg_left (hs.trans hbound) (by positivity : (0 : ℝ) ≤ 4*(p : ℝ)^4)
    nlinarith
  have hfreq : (Fintype.card Ω : ℝ) ≤ (a : ℝ)*(supp : ℝ) := by
    apply (mul_le_mul_iff_right₀ (pow_pos hNr 2)).mp
    have hp := mul_le_mul_of_nonneg_right hscaleR hsup
    nlinarith
  have heq : (univ.filter fun w : Ω => g w ≠ 0) = (univ.filter fun w : Ω => f w ≠ 0) := by
    ext w
    simp [g]
  change (Fintype.card Ω : ℝ) ≤ (a : ℝ)*((univ.filter fun w => g w ≠ 0).card : ℝ) at hfreq
  rw [heq] at hfreq
  exact_mod_cast hfreq

variable (m p : ℕ) [Fact p.Prime]

def Covers (B τ : ℕ) (w : Weight m p) (t : ZMod p × ZMod p) : Prop :=
  prunedHit m p B τ w t.1 t.2 ≠ 0

instance (B τ : ℕ) : DecidableRel (Covers m p B τ) := fun _ _ => inferInstanceAs (Decidable (_ ≠ (0 : ℕ)))

theorem actual_cover_frequency (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B k τ a : ℕ) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (hscale : 4*p^4*3^16 ≤ a*Fintype.card (ActualEdge m)^2) (t : ZMod p × ZMod p) :
    Fintype.card (Weight m p) ≤ a * (univ.filter fun w => Covers m p B τ w t).card := by
  have hN : 0 < Fintype.card (ActualEdge m) := by
    by_contra hn
    have hz : Fintype.card (ActualEdge m) = 0 := by omega
    have hh := hscale
    rw [hz] at hh
    have hlo : 0 < 4*p^4*3^16 := by positivity
    simp only [zero_pow (by decide : 2 ≠ 0), mul_zero] at hh
    omega
  exact support_frequency (fun w => prunedHit m p B τ w t.1 t.2)
    (Fintype.card (ActualEdge m)) p (3^16) a hN
    (pruned_first_moment m p hp hP B k τ hτ hB hguard t.1 t.2)
    (pruned_second_moment m p hp hP B τ t.1 t.2) hscale

/-- The existing exhaustive first-maximum greedy routine covers every
ordered target with an actual retained edge and a valid global raw cap. -/
theorem greedy_covers (maps : List (Weight m p)) (hall : ∀ w, w ∈ maps)
    (hp : 4 < p)
    (hP : (vertices (fixedLength m) (fixedPi m)).card *
      (2 ^ (fixedPi m 1) * 3 ^ (fixedPi m 2)) ≤ p ^ 2)
    (B k τ a : ℕ) (ha : 1 < a) (hτ : 0 < τ)
    (hB : 8 * (p + (fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B * p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (hscale : 4*p^4*3^16 ≤ a*Fintype.card (ActualEdge m)^2) (t : ZMod p × ZMod p) :
    ∃ w ∈ Cover.greedyChoices maps (Covers m p B τ) univ (a*(Nat.log2 (p^2)+1)),
      Covers m p B τ w t := by
  have h := Cover.greedy_cover maps hall (Covers m p B τ) univ a ha
    (fun t _ => actual_cover_frequency m p hp hP B k τ a hτ hB hguard hscale t) t (mem_univ _)
  simpa [pow_two] using h

def frequencyFactor (m : ℕ) : ℕ :=
  4*3^16*(16*TernaryPartitionCount.partitionLoss (7930175*m) (978249*m))^2

theorem polynomial_frequency_scale
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    4*p^4*3^16 ≤ frequencyFactor m*Fintype.card (ActualEdge m)^2 := by
  have h := TernaryPartitionCount.fixed_prime_sq_le_poly_edges m p hup
  have hs := Nat.mul_le_mul_left (4*3^16) (Nat.pow_le_pow_left h 2)
  unfold frequencyFactor
  change 4*p^4*3^16 ≤
    4*3^16*(16*TernaryPartitionCount.partitionLoss (7930175*m) (978249*m))^2*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m))^2
  convert hs using 1 <;> ring

theorem actual_cover_frequency_poly (hp : 4 < p)
    (hlo : (vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)) ≤ p^2)
    (hup : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2)))
    (B k τ : ℕ) (hτ : 0 < τ)
    (hB : 8*(p+(fieldVertices (fixedLength m) p (fixedAlpha m)).card) ≤ B*p)
    (hguard : 16*p^4*B^2*3^(4*k^2) ≤ τ^k*Fintype.card (ActualEdge m))
    (t : ZMod p × ZMod p) :
    Fintype.card (Weight m p) ≤ frequencyFactor m*
      (univ.filter fun w => Covers m p B τ w t).card :=
  actual_cover_frequency m p hp hlo B k τ (frequencyFactor m) hτ hB hguard
    (polynomial_frequency_scale m p hup) t

/-- A positive retained hit certifies the full raw cap at every ordered
target pair, including pairs different from the one being covered. -/
theorem covers_raw_cap {B τ : ℕ} {w : Weight m p} {t : ZMod p × ZMod p}
    (hc : Covers m p B τ w t) : rawCap (fixedAlpha m) (fixedPi m) w ≤ τ := by
  classical
  apply (rawCap_le_iff (fixedAlpha m) (fixedPi m) w τ).mpr
  intro a b
  by_contra hn
  have hb : w ∈ rawBadMaps m p τ := mem_filter.mpr
    ⟨mem_univ _, ⟨(a,b), Nat.lt_of_not_ge hn⟩⟩
  simp [Covers, prunedHit, hb] at hc

end ThreeSum.TernaryCoverFrequency
