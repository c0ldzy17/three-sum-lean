import Submission.ThreeSum.TernaryCoverCapParameters
import Submission.ThreeSum.LocalCoverBounds
import Mathlib.Data.Nat.Log
import Mathlib.Data.Nat.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! Exact selection of the local prime, finite catalog, and repeated cover scale.
This is a cover parameter theorem, not a word-RAM solver theorem. -/

noncomputable section
namespace ThreeSum.TernaryCoverScale
open TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryTypeLowerBound TernaryCoverCapParameters TernaryCoverFrequency

def threshold (m : ℕ) : ℕ :=
  (vertices (fixedLength m) (fixedPi m)).card * (2^(fixedPi m 1)*3^(fixedPi m 2))
def prime (m : ℕ) : ℕ := LocalCoverBounds.selectedPrime (threshold m)

theorem threshold_pos (m : ℕ) : 0 < threshold m := by
  have hR : 0 < 2^(fixedPi m 1)*3^(fixedPi m 2) := by positivity
  have hM := hR.trans_le (vertices_lower_bound (fixedPi m) (fixedPi_total m) (fixedPi_space m))
  exact Nat.mul_pos hM hR

theorem prime_prime (m : ℕ) : (prime m).Prime :=
  (LocalCoverBounds.selectedPrime_spec (threshold m)).1
instance (m : ℕ) : Fact (prime m).Prime := ⟨prime_prime m⟩

theorem prime_lower (m : ℕ) : threshold m ≤ prime m^2 :=
  LocalCoverBounds.selectedPrime_sq_lower _
theorem prime_upper (m : ℕ) : prime m^2 ≤ 16*threshold m :=
  LocalCoverBounds.selectedPrime_sq_upper (threshold_pos m)

theorem partition_le_prime (m : ℕ) : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ prime m :=
  partition_cap_le_prime (fixedPi m) (fixedPi_total m) (fixedPi_space m) (prime m) (prime_lower m)

theorem prime_gt_four {m : ℕ} (hm : 0 < m) : 4 < prime m := by
  have h := partition_le_prime m
  have he : 3 ≤ fixedPi m 1 := by simp [fixedPi]; omega
  have hp := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  have ht : 2^(fixedPi m 1) ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by
    simpa using Nat.mul_le_mul_left (2^(fixedPi m 1)) (Nat.one_le_pow (fixedPi m 2) 3 (by decide))
  norm_num at hp
  omega

def catalog (m : ℕ) : List (TernaryCoverGoodMaps.Weight m (prime m)) :=
  Finset.univ.toList
theorem catalog_complete (m : ℕ) (w : TernaryCoverGoodMaps.Weight m (prime m)) :
    w ∈ catalog m := by simp [catalog]

def family (m k : ℕ) := Cover.greedyChoices (catalog m)
  (TernaryCoverFrequency.Covers m (prime m) (sourceCap m (prime m))
    (rawThreshold (prime m) (sourceCap m (prime m)) k)) Finset.univ
  (frequencyFactor m*(Nat.log2 (prime m^2)+1))

theorem family_covers {m k : ℕ} (hm : 0 < m) (hk : 0 < k)
    (t : ZMod (prime m) × ZMod (prime m)) :
    ∃ w ∈ family m k, TernaryCoverFrequency.Covers m (prime m)
      (sourceCap m (prime m)) (rawThreshold (prime m) (sourceCap m (prime m)) k) w t :=
  explicit_greedy_covers m (prime m) (catalog m) (catalog_complete m) (prime_gt_four hm)
    (prime_lower m) (by simpa only [threshold, Nat.mul_assoc] using prime_upper m) k hk t

theorem family_length (m k : ℕ) :
    (family m k).length = frequencyFactor m*(Nat.log2 (prime m^2)+1) :=
  Cover.greedyChoices_length _ _ _ _

theorem vertices_upper (L : ℕ) (a : DigitType) : (vertices L a).card ≤ 3^L := by
  have h := Finset.card_le_card (Finset.subset_univ (vertices L a))
  simpa [TritWord, Fintype.card_fun] using h

theorem prime_crude_upper (m : ℕ) : prime m ≤ 2^(2*fixedLength m+2) := by
  have hM := vertices_upper (fixedLength m) (fixedPi m)
  have hR : 2^(fixedPi m 1)*3^(fixedPi m 2) ≤ 3^fixedLength m := by
    have hp := Nat.pow_le_pow_left (by decide : (2 : ℕ) ≤ 3) (fixedPi m 1)
    have ht : fixedPi m 1+fixedPi m 2 ≤ fixedLength m := by have := fixedPi_total m; omega
    exact (Nat.mul_le_mul_right _ hp).trans (by rw [← pow_add]; exact Nat.pow_le_pow_right (by decide) ht)
  have hs := (prime_upper m).trans (Nat.mul_le_mul_left 16 (Nat.mul_le_mul hM hR))
  have hq : prime m ≤ 4*3^fixedLength m := by nlinarith [sq_nonneg (prime m-4*3^fixedLength m : ℤ)]
  calc
    _ ≤ 4*3^fixedLength m := hq
    _ ≤ 4*(2^2)^fixedLength m := Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left (by decide) _)
    _ = _ := by rw [← pow_mul, show (4 : ℕ) = 2^2 by norm_num, ← pow_add]; congr 1; omega

theorem sourceCap_crude_upper (m : ℕ) : sourceCap m (prime m) ≤ 2^(2*fixedLength m+4) := by
  have hp := (prime_prime m).pos
  have hv : (fieldVertices (fixedLength m) (prime m) (fixedAlpha m)).card ≤ 3^fixedLength m :=
    (Finset.card_image_le).trans (vertices_upper _ _)
  have h1 : 1 ≤ 3^fixedLength m := Nat.one_le_pow _ _ (by decide)
  have hcap : sourceCap m (prime m) ≤ 16*3^fixedLength m := by
    apply (ceilDiv_le_iff_le_mul hp).mpr
    have hV := Nat.mul_le_mul_left (3^fixedLength m) hp
    change 8*(prime m+_) ≤ prime m*(16*3^fixedLength m)
    nlinarith
  exact hcap.trans (by
    have hh := Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by decide : (3 : ℕ) ≤ 2^2) (fixedLength m))
    simpa only [← pow_mul, show (16 : ℕ) = 2^4 by norm_num, ← pow_add,
      show 4+2*fixedLength m = 2*fixedLength m+4 by omega] using hh)

theorem log2_le_of_le_pow {x e : ℕ} (h : x ≤ 2^e) : Nat.log2 x ≤ e := by
  rw [Nat.log2_eq_log_two]
  exact (Nat.log_mono_right h).trans_eq (Nat.log_pow (by decide) _)

theorem budget_crude_upper (m k : ℕ) :
    capBudget (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26 := by
  have hp := log2_le_of_le_pow (prime_crude_upper m)
  have hB := log2_le_of_le_pow (sourceCap_crude_upper m)
  unfold capBudget
  omega

theorem capExponent_mul_upper (m k : ℕ) :
    k*capExponent (prime m) (sourceCap m (prime m)) k ≤ 12*fixedLength m+8*k^2+26+k := by
  have hd := Nat.div_mul_le_self (capBudget (prime m) (sourceCap m (prime m)) k+k-1) k
  have hb := budget_crude_upper m k
  unfold capExponent
  rw [Nat.ceilDiv_eq_add_pred_div]
  rw [Nat.mul_comm] at hd
  omega

theorem schedule_upper (m : ℕ) :
    frequencyFactor m*(Nat.log2 (prime m^2)+1) ≤ 2^234*(m+1)^7 := by
  have hL : fixedLength m+1 ≤ 2^27*(m+1) := by simp [fixedLength]; norm_num; omega
  have hD : TernaryPartitionCount.partitionLoss (7930175*m) (978249*m) ≤
      (fixedLength m+1)^3 := by
    unfold TernaryPartitionCount.partitionLoss fixedLength
    have h1 : 2*(7930175*m)+1 ≤ 100000000*m+1 := by omega
    have h2 : 3*(978249*m)+1 ≤ 100000000*m+1 := by omega
    have h3 : 2*(978249*m)+1 ≤ 100000000*m+1 := by omega
    simpa only [pow_succ, pow_zero, one_mul] using Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hF : frequencyFactor m ≤ 2^42*(fixedLength m+1)^6 := by
    have h3 : (3 : ℕ)^16 ≤ 2^32 := by norm_num
    have hs := Nat.pow_le_pow_left hD 2
    unfold frequencyFactor
    calc
      _ ≤ 4*2^32*(16*(fixedLength m+1)^3)^2 := by
        exact Nat.mul_le_mul (Nat.mul_le_mul_left 4 h3) (Nat.pow_le_pow_left (Nat.mul_le_mul_left 16 hD) 2)
      _ = _ := by rw [mul_pow, ← pow_mul]; norm_num; ring
  have hp2 : prime m^2 ≤ 2^(4*fixedLength m+4) := by
    have h := Nat.pow_le_pow_left (prime_crude_upper m) 2
    simpa only [← pow_mul, show (2*fixedLength m+2)*2 = 4*fixedLength m+4 by omega] using h
  have hl := log2_le_of_le_pow hp2
  have ht : Nat.log2 (prime m^2)+1 ≤ 8*(fixedLength m+1) := by omega
  calc
    _ ≤ (2^42*(fixedLength m+1)^6)*(8*(fixedLength m+1)) := Nat.mul_le_mul hF ht
    _ = 2^45*(fixedLength m+1)^7 := by norm_num; ring
    _ ≤ 2^45*(2^27*(m+1))^7 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL 7)
    _ = _ := by rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]

def momentOrder (C : ℕ) : ℕ := 100000*C
def scaleAux (C c d : ℕ) : ℕ :=
  C*momentOrder C*(28*d+241+(2*d+15)+1)+
    C*(8*(momentOrder C)^2+momentOrder C+26)+c+2
def scale (C c d : ℕ) : ℕ := 2^(2*scaleAux C c d)

theorem scale_pos (C c d : ℕ) : 0 < scale C c d := by unfold scale; positivity

theorem polynomial_schedule_upper (c d t : ℕ) (hc : c ≤ t) :
    (c*(fixedLength (2^(2*t))+1)^d)*
      (frequencyFactor (2^(2*t))*(Nat.log2 (prime (2^(2*t))^2)+1)) ≤
    2^(28*d+241+(2*d+15)*t) := by
  have hc2 : c ≤ 2^t := hc.trans (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < (2 : ℕ))))
  have hm : 2^(2*t)+1 ≤ 2^(2*t+1) := by rw [pow_succ]; have := Nat.one_le_pow (2*t) 2 (by decide); omega
  have hL : fixedLength (2^(2*t))+1 ≤ 2^27*(2^(2*t)+1) := by simp [fixedLength]; norm_num; omega
  have hb := Nat.mul_le_mul (Nat.mul_le_mul hc2 (Nat.pow_le_pow_left hL d)) (schedule_upper (2^(2*t)))
  calc
    _ ≤ (2^t*(2^27*(2^(2*t)+1))^d)*(2^234*(2^(2*t)+1)^7) := hb
    _ = 2^(t+27*d+234)*(2^(2*t)+1)^(d+7) := by rw [mul_pow, ← pow_mul, pow_add]; ring
    _ ≤ 2^(t+27*d+234)*(2^(2*t+1))^(d+7) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hm _)
    _ = _ := by rw [← pow_mul, ← pow_add]; congr 1; ring

/-- Every polynomial carry factor and both repeated cover factors fit an
arbitrarily small reciprocal exponent, for a single fixed exact block. -/
theorem selected_scale_bound (C c d : ℕ) (hC : 0 < C) :
    ((c*(fixedLength (scale C c d)+1)^d)*
      (frequencyFactor (scale C c d)*(Nat.log2 (prime (scale C c d)^2)+1))*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C))^C ≤ prime (scale C c d) := by
  let k := momentOrder C
  let t := scaleAux C c d
  let m := scale C c d
  let A := 28*d+241
  let D := 2*d+15
  have hk : 0 < k := by dsimp [k, momentOrder]; positivity
  have hkt : C*k*A ≤ t := by dsimp [t,scaleAux,A,k]; ring_nf; omega
  have hdt : C*k*D ≤ t := by dsimp [t,scaleAux,D,k]; ring_nf; omega
  have hbt : C*(8*k^2+k+26) ≤ t := by dsimp [t,scaleAux,k]; omega
  have hc : c ≤ t := by dsimp [t,scaleAux]; omega
  have ht : 2 ≤ t := by dsimp [t,scaleAux]; omega
  have hm : 2*t^2+1 ≤ m := Nat.two_mul_sq_add_one_le_two_pow_two_mul t
  have hbudget := capExponent_mul_upper m k
  have hsmall : C*k*(A+D*t)+C*(8*k^2+k+26) ≤ m := by
    have hh := Nat.mul_le_mul_right t hdt
    nlinarith
  have hbig : C*k*(A+D*t)+C*(12*fixedLength m+8*k^2+26+k) ≤ k*(fixedPi m 1) := by
    have hmain : 12*C*fixedLength m+m ≤ k*(fixedPi m 1) := by
      dsimp [k,momentOrder,fixedLength,fixedPi]
      nlinarith
    nlinarith
  have hexp : C*(A+D*t+capExponent (prime m) (sourceCap m (prime m)) k) ≤ fixedPi m 1 := by
    have hh := Nat.mul_le_mul_left C hbudget
    have hx : k*(C*(A+D*t+capExponent (prime m) (sourceCap m (prime m)) k)) ≤ k*(fixedPi m 1) := by nlinarith
    exact Nat.le_of_mul_le_mul_left hx hk
  have hp := polynomial_schedule_upper c d t hc
  have hall := Nat.pow_le_pow_left (Nat.mul_le_mul_right
    (rawThreshold (prime m) (sourceCap m (prime m)) k) hp) C
  change _ ≤ prime m
  calc
    _ ≤ (2^(A+D*t)*rawThreshold (prime m) (sourceCap m (prime m)) k)^C := hall
    _ = 2^((A+D*t+capExponent (prime m) (sourceCap m (prime m)) k)*C) := by
      rw [rawThreshold, ← pow_add, ← pow_mul]
    _ ≤ 2^(fixedPi m 1) := Nat.pow_le_pow_right (by decide) (by simpa [Nat.mul_comm] using hexp)
    _ ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by
      simpa using Nat.mul_le_mul_left (2^(fixedPi m 1)) (Nat.one_le_pow (fixedPi m 2) 3 (by decide))
    _ ≤ prime m := partition_le_prime m

def localFactor (C c d : ℕ) : ℕ :=
  (c*(fixedLength (scale C c d)+1)^d)*
    (family (scale C c d) (momentOrder C)).length*
    rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
      (momentOrder C)

theorem repeated_scale_bound (C c d r : ℕ) (hC : 0 < C) :
    (localFactor C c d^r)^C ≤ prime (scale C c d)^r := by
  have h := Nat.pow_le_pow_left (selected_scale_bound C c d hC) r
  simpa only [localFactor, family_length, ← pow_mul, Nat.mul_comm] using h

/-- This bridge charges every polynomial carry choice and every repeated
family/raw-cap choice. Its only global assumption is the displayed radix
bound; it supplies no implementation time bound. -/
theorem global_representation_budget (c d a n r : ℕ)
    (hradix : prime (scale 40000000000 c d)^r ≤ a*n^3) (han : a ≤ n) :
    ((localFactor 40000000000 c d)^r : ℝ) ≤ (n : ℝ)^(1/10000000000 : ℝ) := by
  have hpow : (localFactor 40000000000 c d^r)^40000000000 ≤ n^4 := by
    calc
      _ ≤ prime (scale 40000000000 c d)^r := repeated_scale_bound _ _ _ _ (by decide)
      _ ≤ a*n^3 := hradix
      _ ≤ n*n^3 := Nat.mul_le_mul_right _ han
      _ = n^4 := by ring
  have hr : (((localFactor 40000000000 c d)^r : ℝ)^40000000000) ≤ (n : ℝ)^4 := by
    exact_mod_cast hpow
  have hh := (Real.le_rpow_inv_iff_of_pos
    (Nat.cast_nonneg ((localFactor 40000000000 c d)^r))
    (by positivity : (0 : ℝ) ≤ (n : ℝ)^4)
    (by norm_num : (0 : ℝ) < ((40000000000 : ℕ) : ℝ))).mpr (by
      simpa only [Real.rpow_natCast, Nat.cast_pow] using hr)
  rw [← Real.rpow_natCast (n : ℝ) 4, ← Real.rpow_mul (Nat.cast_nonneg n)] at hh
  convert hh using 1 <;> norm_num

theorem global_representation_eventually (c d a : ℕ) (r : ℕ → ℕ)
    (hradix : ∀ᶠ n : ℕ in Filter.atTop, prime (scale 40000000000 c d)^(r n) ≤ a*n^3) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((localFactor 40000000000 c d)^(r n) : ℝ) ≤ (n : ℝ)^(1/10000000000 : ℝ) := by
  filter_upwards [hradix, Filter.eventually_ge_atTop a] with n hr hn
  exact global_representation_budget c d a n (r n) hr hn

def outputSize (m : ℕ) : ℕ := (vertices (fixedLength m) (fixedPi m)).card

theorem outputSize_ge_sixteen {m : ℕ} (hm : 0 < m) : 16 ≤ outputSize m := by
  have hM := vertices_lower_bound (fixedPi m) (fixedPi_total m) (fixedPi_space m)
  have he : 4 ≤ fixedPi m 1 := by simp [fixedPi]; omega
  have hpow := Nat.pow_le_pow_right (by decide : 0 < (2 : ℕ)) he
  have ht : 2^(fixedPi m 1) ≤ 2^(fixedPi m 1)*3^(fixedPi m 2) := by
    simpa using Nat.mul_le_mul_left (2^(fixedPi m 1)) (Nat.one_le_pow (fixedPi m 2) 3 (by decide))
  exact hpow.trans (ht.trans hM)

theorem prime_square_le_cube {m : ℕ} (hm : 0 < m) : prime m^2 ≤ outputSize m^3 := by
  have hM := vertices_lower_bound (fixedPi m) (fixedPi_total m) (fixedPi_space m)
  have h16 := outputSize_ge_sixteen hm
  calc
    _ ≤ 16*threshold m := prime_upper m
    _ ≤ 16*(outputSize m)^2 := by
      unfold threshold outputSize
      simpa [pow_two, Nat.mul_assoc] using Nat.mul_le_mul_left 16 (Nat.mul_le_mul_left _ hM)
    _ ≤ outputSize m^3 := by nlinarith

def radixLength (m n : ℕ) : ℕ := Nat.clog (outputSize m) (n^2)

theorem radix_power_upper {m n : ℕ} (hm : 0 < m) (hn : 1 < n) :
    prime m^(radixLength m n) ≤ outputSize m^2*n^3 := by
  have hM : 1 < outputSize m := lt_of_lt_of_le (by decide : 1 < (16 : ℕ)) (outputSize_ge_sixteen hm)
  have hn2 : 1 < n^2 := by nlinarith
  have hpos := Nat.clog_pos hM hn2
  have hl := Nat.pow_pred_clog_lt_self hM hn2
  have hexp : outputSize m^(radixLength m n) ≤ outputSize m*n^2 := by
    have he : radixLength m n = (Nat.clog (outputSize m) (n^2)).pred+1 := by
      exact (Nat.succ_pred_eq_of_pos hpos).symm
    rw [he, pow_succ]
    exact (Nat.mul_le_mul_right (outputSize m) hl.le).trans_eq (Nat.mul_comm _ _)
  have hp := Nat.pow_le_pow_left (prime_square_le_cube hm) (radixLength m n)
  have hx := Nat.pow_le_pow_left hexp 3
  have hpow : (prime m^(radixLength m n))^2 ≤ (outputSize m^2*n^3)^2 := by
    calc
      _ ≤ (outputSize m^(radixLength m n))^3 := by
        simpa only [← pow_mul, Nat.mul_comm] using hp
      _ ≤ (outputSize m*n^2)^3 := hx
      _ ≤ (outputSize m^2*n^3)^2 := by
        have h1 : 1 ≤ outputSize m := hM.le
        have hh := Nat.mul_le_mul_right ((outputSize m)^3*n^6) h1
        convert hh using 1 <;> ring
  exact (Nat.pow_le_pow_iff_left (by decide : (2 : ℕ) ≠ 0)).mp hpow

/-- A completely specified fixed block and radix schedule pay all repeated
cover and polynomial carry multiplicities within the 10^-10 allowance. -/
theorem fixed_representation_eventually (c d : ℕ) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((localFactor 40000000000 c d)^
        (radixLength (scale 40000000000 c d) n) : ℝ) ≤
          (n : ℝ)^(1/10000000000 : ℝ) := by
  apply global_representation_eventually c d (outputSize (scale 40000000000 c d)^2)
  filter_upwards [Filter.eventually_gt_atTop (1 : ℕ)] with n hn
  exact radix_power_upper (scale_pos _ _ _) hn

theorem carry_factor_le (C c d b : ℕ)
    (hb : b ≤ c*(fixedLength (scale C c d)+1)^d) :
    b*(family (scale C c d) (momentOrder C)).length*
      rawThreshold (prime (scale C c d)) (sourceCap (scale C c d) (prime (scale C c d)))
        (momentOrder C) ≤ localFactor C c d := by
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hb)

/-- The bound applies to any actual carry count below the polynomial
envelope, rather than requiring that count to equal its envelope. -/
theorem polynomial_carry_representation (c d b : ℕ)
    (hb : b ≤ c*(fixedLength (scale 40000000000 c d)+1)^d) :
    ∀ᶠ n : ℕ in Filter.atTop,
      ((b*(family (scale 40000000000 c d) (momentOrder 40000000000)).length*
        rawThreshold (prime (scale 40000000000 c d))
          (sourceCap (scale 40000000000 c d) (prime (scale 40000000000 c d)))
          (momentOrder 40000000000))^
          (radixLength (scale 40000000000 c d) n) : ℝ) ≤
        (n : ℝ)^(1/10000000000 : ℝ) := by
  filter_upwards [fixed_representation_eventually c d] with n hn
  have h := Nat.pow_le_pow_left (carry_factor_le 40000000000 c d b hb)
    (radixLength (scale 40000000000 c d) n)
  exact (by exact_mod_cast h : _ ≤ ((localFactor 40000000000 c d)^
    (radixLength (scale 40000000000 c d) n) : ℝ)).trans hn

end ThreeSum.TernaryCoverScale
