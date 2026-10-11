import Submission.ThreeSum.LayerCounts
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Nat.Sqrt
import Mathlib.NumberTheory.Bertrand
import Mathlib.Algebra.Order.Floor.Div
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Finite numerical bounds for the local cover

The graph degree bound follows from exact finite cardinalities: the degree
is no larger than the number of vertices, while vertices times degree equal
outputs times representations per output.  This avoids any approximation
of factorials.  The prime-interval and normalized first-moment estimates
are stated explicitly in terms of the concrete binomial coefficients.
-/

namespace ThreeSum.LocalCoverBounds

open scoped BigOperators

def outputCount (L h : ℕ) : ℕ := L.choose (2 * h)
def vertexCount (L h : ℕ) : ℕ := L.choose h
def degree (L h : ℕ) : ℕ := (L - h).choose h
def groupSize (h : ℕ) : ℕ := (2 * h).choose h

/-- Choose one coordinate from each of `r` disjoint blocks of size `c`. This
is a direct finite injection giving an exact binomial lower bound. -/
theorem pow_le_choose_mul (c r : ℕ) : c ^ r ≤ (c * r).choose r := by
  let graph (f : Fin r → Fin c) : Finset (Fin r × Fin c) :=
    Finset.univ.image (fun i => (i, f i))
  have hgcard (f : Fin r → Fin c) : (graph f).card = r := by
    change (Finset.univ.image (fun i : Fin r => (i, f i))).card = r
    rw [Finset.card_image_of_injective]
    · simp
    · intro i j he
      exact congrArg Prod.fst he
  have hginj : Function.Injective graph := by
    intro f g he
    funext i
    have hm : (i, f i) ∈ graph g := by
      rw [← he]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hm
    have hji : j = i := congrArg Prod.fst hj
    subst j
    exact (congrArg Prod.snd hj).symm
  have hcount : (Finset.univ : Finset (Fin r → Fin c)).card ≤
      ((Finset.univ : Finset (Fin r × Fin c)).powersetCard r).card := by
    apply Finset.card_le_card_of_injOn graph
    · intro f _
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hgcard f⟩
    · intro f _ g _ he
      exact hginj he
  simpa [Finset.card_powersetCard, Nat.mul_comm] using hcount

theorem concrete_output_gt_pow {h : ℕ} (hh : 0 < h) :
    2 ^ (2 * h) < outputCount (512 * h) h := by
  have hlo : 256 ^ (2 * h) ≤ outputCount (512 * h) h := by
    simpa [outputCount, show 256 * (2 * h) = 512 * h by omega] using
      pow_le_choose_mul 256 (2 * h)
  exact ((Nat.pow_lt_pow_iff_left (by omega : 2 * h ≠ 0)).mpr (by decide)).trans_le hlo

theorem degree_le_vertices (L h : ℕ) : degree L h ≤ vertexCount L h :=
  Nat.choose_le_choose h (Nat.sub_le L h)

theorem vertices_mul_degree (L h : ℕ) :
    vertexCount L h * degree L h = outputCount L h * groupSize h :=
  LayerCounts.vertex_degree_identity L h

theorem groupSize_lt_pow {h : ℕ} (hh : 0 < h) : groupSize h < 2 ^ (2 * h) :=
  Nat.choose_lt_two_pow _ _ (by omega)

theorem groupSize_le_pow (h : ℕ) : groupSize h ≤ 2 ^ (2 * h) :=
  Nat.choose_le_two_pow _ _

theorem groupSize_lower (h : ℕ) :
    2 ^ (2 * h) ≤ (2 * h + 1) * groupSize h := by
  simpa only [show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul,
    groupSize] using Nat.four_pow_le_two_mul_add_one_mul_central_binom h

/-- Exact strict version of the degree-square estimate needed to compare the
degree with the selected prime. -/
theorem degree_sq_lt_output_pow {L h : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L) :
    degree L h ^ 2 < outputCount L h * 2 ^ (2 * h) := by
  have hM : 0 < outputCount L h := Nat.choose_pos hL
  calc
    degree L h ^ 2 = degree L h * degree L h := by rw [pow_two]
    _ ≤ vertexCount L h * degree L h :=
      Nat.mul_le_mul_right _ (degree_le_vertices L h)
    _ = outputCount L h * groupSize h := vertices_mul_degree L h
    _ < outputCount L h * 2 ^ (2 * h) :=
      Nat.mul_lt_mul_of_pos_left (groupSize_lt_pow hh) hM

theorem degree_lt_modulus {L h p : ℕ} (hh : 0 < h) (hL : 2 * h ≤ L)
    (hp : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : degree L h < p := by
  have hs := (degree_sq_lt_output_pow hh hL).trans_le hp
  nlinarith

theorem groupSize_lt_modulus {L h p : ℕ}
    (hM : 2 ^ (2 * h) < outputCount L h)
    (hp : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : groupSize h < p := by
  have hG := groupSize_le_pow h
  have hpow : 0 < (2 : ℕ) ^ (2 * h) := Nat.pow_pos (by decide)
  have hsq : groupSize h ^ 2 < outputCount L h * 2 ^ (2 * h) := by
    calc
      groupSize h ^ 2 ≤ (2 ^ (2 * h)) ^ 2 := Nat.pow_le_pow_left hG _
      _ = 2 ^ (2 * h) * 2 ^ (2 * h) := by rw [pow_two]
      _ < outputCount L h * 2 ^ (2 * h) := Nat.mul_lt_mul_of_pos_right hM hpow
  have hs := hsq.trans_le hp
  nlinarith

/-- The exact expectation of the actual edge count, once its hash moment
identity has been proved. -/
noncomputable def mean (L h p : ℕ) : ℝ :=
  (outputCount L h : ℝ) * groupSize h / (p : ℝ) ^ 2

theorem mean_positive {L h p : ℕ} (hL : 2 * h ≤ L) (hp : 0 < p) :
    0 < mean L h p := by
  have hM : 0 < outputCount L h := Nat.choose_pos hL
  have hG : 0 < groupSize h := Nat.choose_pos (by omega)
  unfold mean
  positivity

theorem mean_le_one {L h p : ℕ} (hp : 0 < p)
    (hlo : outputCount L h * 2 ^ (2 * h) ≤ p ^ 2) : mean L h p ≤ 1 := by
  have hG : (groupSize h : ℝ) ≤ 2 ^ (2 * h) := by exact_mod_cast groupSize_le_pow h
  have hlow : (outputCount L h : ℝ) * 2 ^ (2 * h) ≤ (p : ℝ) ^ 2 := by
    exact_mod_cast hlo
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  rw [mean, div_le_one (by positivity)]
  exact (mul_le_mul_of_nonneg_left hG (Nat.cast_nonneg _)).trans hlow

/-- The factor 16 permits a prime above the rounded square-root threshold.
Together with the central-binomial estimate it gives the stated explicit
lower bound on the probability scale. -/
theorem mean_lower {L h p : ℕ} (hL : 2 * h ≤ L) (hp : 0 < p)
    (hup : p ^ 2 ≤ 16 * (outputCount L h * 2 ^ (2 * h))) :
    1 / (16 * (2 * (h : ℝ) + 1)) ≤ mean L h p := by
  have hM : (0 : ℝ) < outputCount L h := by exact_mod_cast Nat.choose_pos hL
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hG : (2 : ℝ) ^ (2 * h) ≤ (2 * (h : ℝ) + 1) * groupSize h := by
    exact_mod_cast groupSize_lower h
  have hupper : (p : ℝ) ^ 2 ≤ 16 * ((outputCount L h : ℝ) * 2 ^ (2 * h)) := by
    exact_mod_cast hup
  have hscale := mul_le_mul_of_nonneg_left hG (by positivity :
    (0 : ℝ) ≤ 16 * outputCount L h)
  rw [mean]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith

/-! ## A deterministic selected prime -/

/-- For positive `N`, this is exactly the integer ceiling of `sqrt N`. -/
def rootCeiling (N : ℕ) : ℕ := Nat.sqrt (N - 1) + 1

theorem rootCeiling_pos (N : ℕ) : 0 < rootCeiling N := by
  unfold rootCeiling
  omega

theorem le_rootCeiling_sq (N : ℕ) : N ≤ rootCeiling N ^ 2 := by
  have hs := Nat.lt_succ_sqrt' (N - 1)
  simp only [Nat.succ_eq_add_one] at hs
  unfold rootCeiling
  omega

theorem rootCeiling_sq_le_four {N : ℕ} (hN : 0 < N) : rootCeiling N ^ 2 ≤ 4 * N := by
  have hmono := Nat.sqrt_le_sqrt (Nat.sub_le N 1)
  have hpos := Nat.sqrt_pos.mpr hN
  have hlo := Nat.sqrt_le' N
  have hroot : rootCeiling N ≤ 2 * Nat.sqrt N := by
    unfold rootCeiling
    omega
  have hsq := Nat.pow_le_pow_left hroot 2
  nlinarith

/-- The interval is finite and explicitly enumerated; primality is decidable. -/
def primeCandidates (N : ℕ) : Finset ℕ :=
  (Finset.range (2 * rootCeiling N + 1)).filter
    (fun p => Nat.Prime p ∧ rootCeiling N < p)

theorem mem_primeCandidates {N p : ℕ} :
    p ∈ primeCandidates N ↔ Nat.Prime p ∧ rootCeiling N < p ∧ p ≤ 2 * rootCeiling N := by
  simp only [primeCandidates, Finset.mem_filter, Finset.mem_range]
  constructor
  · rintro ⟨hup, hp, hlo⟩
    exact ⟨hp, hlo, by omega⟩
  · rintro ⟨hp, hlo, hup⟩
    exact ⟨by omega, hp, hlo⟩

theorem primeCandidates_nonempty (N : ℕ) : (primeCandidates N).Nonempty := by
  obtain ⟨p, hp, hlo, hup⟩ :=
    Nat.exists_prime_lt_and_le_two_mul (rootCeiling N) (rootCeiling_pos N).ne'
  exact ⟨p, mem_primeCandidates.mpr ⟨hp, hlo, hup⟩⟩

def selectedPrime (N : ℕ) : ℕ :=
  (primeCandidates N).min' (primeCandidates_nonempty N)

theorem selectedPrime_spec (N : ℕ) :
    Nat.Prime (selectedPrime N) ∧ rootCeiling N < selectedPrime N ∧
      selectedPrime N ≤ 2 * rootCeiling N :=
  mem_primeCandidates.mp (Finset.min'_mem _ _)

theorem selectedPrime_pos (N : ℕ) : 0 < selectedPrime N :=
  (selectedPrime_spec N).1.pos

theorem selectedPrime_sq_lower (N : ℕ) : N ≤ selectedPrime N ^ 2 := by
  exact (le_rootCeiling_sq N).trans
    (Nat.pow_le_pow_left (selectedPrime_spec N).2.1.le 2)

theorem selectedPrime_sq_upper {N : ℕ} (hN : 0 < N) :
    selectedPrime N ^ 2 ≤ 16 * N := by
  have hu := (selectedPrime_spec N).2.2
  have hsq := Nat.pow_le_pow_left hu 2
  have hr := rootCeiling_sq_le_four hN
  nlinarith

theorem selectedPrime_gt_two {N : ℕ} (hN : 1 < N) : 2 < selectedPrime N := by
  have hs : 0 < Nat.sqrt (N - 1) := Nat.sqrt_pos.mpr (by omega)
  have hlo := (selectedPrime_spec N).2.1
  unfold rootCeiling at hlo
  omega

theorem selectedPrime_odd {N : ℕ} (hN : 1 < N) : Odd (selectedPrime N) :=
  (selectedPrime_spec N).1.odd_of_ne_two (by have := selectedPrime_gt_two hN; omega)

/-- Enumeration of local prime candidates has a direct finite work domain. -/
theorem primeCandidates_card_bound (N : ℕ) :
    (primeCandidates N).card ≤ 2 * rootCeiling N + 1 := by
  exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)

/-! ## Exact integer rounding of the separable bucket cap -/

/-- Integer ceiling of `4*(1+V/p)`, expressed using computable ceiling division. -/
def bucketCap (V p : ℕ) : ℕ := (4 * (p + V)) ⌈/⌉ p

theorem bucketCap_formula (V p : ℕ) :
    bucketCap V p = (4 * (p + V) + p - 1) / p := rfl

theorem bucketCap_le_iff {V p b : ℕ} (hp : 0 < p) :
    bucketCap V p ≤ b ↔ 4 * (p + V) ≤ b * p := by
  simpa only [bucketCap, Nat.mul_comm] using
    (ceilDiv_le_iff_le_mul (b := 4 * (p + V)) (c := b) hp)

theorem bucketCap_threshold {V p : ℕ} (hp : 0 < p) :
    4 * (p + V) ≤ bucketCap V p * p :=
  (bucketCap_le_iff hp).mp le_rfl

theorem bucketCap_mul_lt {V p : ℕ} (hp : 0 < p) :
    bucketCap V p * p < 4 * (p + V) + p := by
  rw [bucketCap_formula]
  have hdiv := Nat.div_mul_le_self (4 * (p + V) + p - 1) p
  omega

theorem bucketCap_real_bound {V p : ℕ} (hp : 0 < p) :
    (bucketCap V p : ℝ) < 5 + 4 * (V : ℝ) / p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp
  have hb : (bucketCap V p : ℝ) * p < 4 * (p + (V : ℝ)) + p := by
    exact_mod_cast bucketCap_mul_lt (V := V) hp
  rw [show 5 + 4 * (V : ℝ) / p = (5 * p + 4 * V) / p by field_simp,
    lt_div_iff₀ hp0]
  nlinarith

/-! ## The actual local parameters at `L=512*h` -/

def localThreshold (h : ℕ) : ℕ := outputCount (512 * h) h * 2 ^ (2 * h)
def localPrime (h : ℕ) : ℕ := selectedPrime (localThreshold h)
def localBucketCap (h : ℕ) : ℕ := bucketCap (vertexCount (512 * h) h) (localPrime h)

theorem localThreshold_pos (h : ℕ) : 0 < localThreshold h :=
  Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.pow_pos (by decide))

theorem localThreshold_gt_one {h : ℕ} (hh : 0 < h) : 1 < localThreshold h := by
  have hm := concrete_output_gt_pow hh
  have hpow : 0 < (2 : ℕ) ^ (2 * h) := Nat.pow_pos (by decide)
  unfold localThreshold
  nlinarith

theorem localPrime_prime (h : ℕ) : Nat.Prime (localPrime h) :=
  (selectedPrime_spec (localThreshold h)).1

theorem localPrime_pos (h : ℕ) : 0 < localPrime h := (localPrime_prime h).pos

theorem localPrime_odd {h : ℕ} (hh : 0 < h) : Odd (localPrime h) :=
  selectedPrime_odd (localThreshold_gt_one hh)

theorem localPrime_sq_lower (h : ℕ) :
    outputCount (512 * h) h * 2 ^ (2 * h) ≤ localPrime h ^ 2 :=
  selectedPrime_sq_lower (localThreshold h)

theorem localPrime_sq_upper (h : ℕ) :
    localPrime h ^ 2 ≤ 16 * (outputCount (512 * h) h * 2 ^ (2 * h)) :=
  selectedPrime_sq_upper (localThreshold_pos h)

theorem degree_lt_localPrime {h : ℕ} (hh : 0 < h) :
    degree (512 * h) h < localPrime h :=
  degree_lt_modulus hh (by omega) (localPrime_sq_lower h)

theorem groupSize_lt_localPrime {h : ℕ} (hh : 0 < h) : groupSize h < localPrime h :=
  groupSize_lt_modulus (concrete_output_gt_pow hh) (localPrime_sq_lower h)

theorem edgeCount_le_localPrime_sq (h : ℕ) :
    outputCount (512 * h) h * groupSize h ≤ localPrime h ^ 2 :=
  (Nat.mul_le_mul_left _ (groupSize_le_pow h)).trans (localPrime_sq_lower h)

theorem badCount_le_localPrime {h : ℕ} (hh : 0 < h) :
    2 * degree (512 * h) h + groupSize h ≤ 3 * localPrime h := by
  have hd := degree_lt_localPrime hh
  have hg := groupSize_lt_localPrime hh
  omega

theorem localMean_positive (h : ℕ) : 0 < mean (512 * h) h (localPrime h) :=
  mean_positive (by omega) (localPrime_pos h)

theorem localMean_le_one (h : ℕ) : mean (512 * h) h (localPrime h) ≤ 1 :=
  mean_le_one (localPrime_pos h) (localPrime_sq_lower h)

theorem localMean_lower (h : ℕ) :
    1 / (16 * (2 * (h : ℝ) + 1)) ≤ mean (512 * h) h (localPrime h) :=
  mean_lower (by omega) (localPrime_pos h) (localPrime_sq_upper h)

theorem localBucketCap_threshold (h : ℕ) :
    4 * (localPrime h + vertexCount (512 * h) h) ≤ localBucketCap h * localPrime h :=
  bucketCap_threshold (localPrime_pos h)

end ThreeSum.LocalCoverBounds
