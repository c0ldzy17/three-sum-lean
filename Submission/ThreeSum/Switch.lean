import Submission.ThreeSum.BandScales
import Mathlib.Data.Finset.Max

/-!
# The executable integer cubic switch

The implementation scans integers `q ≤ r/2` and tests a cleared integer
inequality.  No real-number comparison, logarithm oracle, or unbounded
noncomputable search occurs in the definition.  For admissible depths the
candidate set is nonempty.  Minimality gives the exact `9/r` rounding error
needed by the certified box and entropy bounds.
-/

namespace ThreeSum.Switch

open Set ThreeSum.Parameters ThreeSum.Scales

set_option maxHeartbeats 0

def cubicNumerator (r q : ℕ) : ℕ := 799 * q * r ^ 2 + 72 * q ^ 2 * r + 24 * q ^ 3

def accepts (J j r q : ℕ) : Prop :=
  (291 * J + 1000 * j) * r ^ 3 ≤ 10 * (J - j) * cubicNumerator r q

instance (J j r q : ℕ) : Decidable (accepts J j r q) :=
  inferInstanceAs (Decidable (_ ≤ _))

def candidates (J j r : ℕ) : Finset ℕ :=
  (Finset.range (r / 2 + 1)).filter (accepts J j r)

def switchIndex (J j r : ℕ) : ℕ :=
  if h : (candidates J j r).Nonempty then (candidates J j r).min' h else 0

def residualSize (n j : ℕ) : ℕ := (blockCount (inputBits n) - j) * muZero n

def actualSwitch (n j : ℕ) : ℕ :=
  switchIndex (blockCount (inputBits n)) j (residualSize n j)

def terminalDepth (n : ℕ) : ℕ := 13 * blockCount (inputBits n) / 20

@[simp] theorem mem_candidates {J j r q : ℕ} :
    q ∈ candidates J j r ↔ q ≤ r / 2 ∧ accepts J j r q := by
  simp [candidates, Nat.lt_succ_iff]

theorem switchIndex_mem {J j r : ℕ} (h : (candidates J j r).Nonempty) :
    switchIndex J j r ∈ candidates J j r := by
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_mem _ _

theorem switchIndex_le {J j r q : ℕ} (hq : q ∈ candidates J j r) :
    switchIndex J j r ≤ q := by
  have h : (candidates J j r).Nonempty := ⟨q, hq⟩
  simp only [switchIndex, dif_pos h]
  exact Finset.min'_le _ _ hq

noncomputable section

theorem depth_fraction {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) :
    (j : ℝ) / J ∈ Icc (0 : ℝ) terminalFraction := by
  have hJR : (0 : ℝ) < J := by exact_mod_cast hJ
  constructor
  · positivity
  · rw [div_le_iff₀ hJR]
    have ht : (20 : ℝ) * j ≤ 13 * J := by exact_mod_cast hj
    dsimp [terminalFraction]
    linarith

theorem depth_lt {J j : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J) : j < J := by
  omega

theorem threshold_fraction {J j : ℕ} (hJ : 0 < J) (hj : j < J) :
    switchThreshold ((j : ℝ) / J) =
      (291 * (J : ℝ) + 1000 * j) / (1000 * ((J - j : ℕ) : ℝ)) := by
  have hJR : (J : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  have hd : ((J - j : ℕ) : ℝ) = (J : ℝ) - j := by
    exact Nat.cast_sub hj.le
  have hden : (J : ℝ) - j ≠ 0 := by
    have hlt : (j : ℝ) < J := by exact_mod_cast hj
    linarith
  rw [hd]
  unfold switchThreshold boxSaving bandShift
  field_simp
  <;> ring

theorem phi_fraction {r q : ℕ} (hr : 0 < r) :
    phi ((q : ℝ) / r) = (cubicNumerator r q : ℝ) / (100 * (r : ℝ) ^ 3) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  simp only [phi, cubicNumerator, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  field_simp
  <;> ring

theorem accepts_iff {J j r q : ℕ} (hJ : 0 < J) (hj : j < J) (hr : 0 < r) :
    accepts J j r q ↔ switchThreshold ((j : ℝ) / J) ≤ phi ((q : ℝ) / r) := by
  have hd : (0 : ℝ) < ((J - j : ℕ) : ℝ) := by exact_mod_cast Nat.sub_pos_of_lt hj
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  rw [threshold_fraction hJ hj, phi_fraction hr, div_le_div_iff₀ (by positivity) (by positivity)]
  have hc : accepts J j r q ↔
      (291 * (J : ℝ) + 1000 * j) * (r : ℝ) ^ 3 ≤
        10 * ((J - j : ℕ) : ℝ) * (cubicNumerator r q : ℝ) := by
    unfold accepts
    exact_mod_cast Iff.rfl
  rw [hc]
  constructor <;> intro h <;> nlinarith

theorem half_fraction {r : ℕ} (hr : 0 < r) (heven : 2 ∣ r) :
    ((r / 2 : ℕ) : ℝ) / r = (1 / 2 : ℝ) := by
  have hm := Nat.div_mul_cancel heven
  have hmR : ((r / 2 : ℕ) : ℝ) * 2 = r := by exact_mod_cast hm
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
  field_simp
  linarith

theorem candidates_nonempty {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : (candidates J j r).Nonempty := by
  refine ⟨r / 2, mem_candidates.mpr ⟨le_rfl, ?_⟩⟩
  rw [accepts_iff hJ (depth_lt hJ hj) hr, half_fraction hr heven, phi_half]
  have h := switchThreshold_upper (depth_fraction hJ hj)
  linarith

theorem switchIndex_spec {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    switchIndex J j r ≤ r / 2 ∧ accepts J j r (switchIndex J j r) :=
  mem_candidates.mp (switchIndex_mem (candidates_nonempty hJ hj hr heven))

theorem switchIndex_pos {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) : 0 < switchIndex J j r := by
  have hs := (switchIndex_spec hJ hj hr heven).2
  by_contra hn
  have hz : switchIndex J j r = 0 := by omega
  rw [hz] at hs
  have hp : 0 < (291 * J + 1000 * j) * r ^ 3 := by positivity
  simp [accepts, cubicNumerator] at hs
  omega

theorem predecessor_rejected {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    ¬ accepts J j r (switchIndex J j r - 1) := by
  have hpos := switchIndex_pos hJ hj hr heven
  have hle := (switchIndex_spec hJ hj hr heven).1
  intro ha
  have hm : switchIndex J j r - 1 ∈ candidates J j r :=
    mem_candidates.mpr ⟨by omega, ha⟩
  have hbad := switchIndex_le hm
  omega

theorem ratio_mem_half {r q : ℕ} (hr : 0 < r) (hq : q ≤ r / 2) :
    (q : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) := by
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  have htwo : 2 * q ≤ r := by
    have hm := Nat.div_mul_le_self r 2
    omega
  have htwoR : (2 : ℝ) * q ≤ r := by exact_mod_cast htwo
  constructor
  · positivity
  · rw [div_le_iff₀ hrR]
    linarith

theorem switch_ratio_mem {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    (switchIndex J j r : ℝ) / r ∈ Icc (0 : ℝ) (1 / 2) :=
  ratio_mem_half hr (switchIndex_spec hJ hj hr heven).1

theorem phi_enclosure {J j r : ℕ} (hJ : 0 < J) (hj : 20 * j ≤ 13 * J)
    (hr : 0 < r) (heven : 2 ∣ r) :
    switchThreshold ((j : ℝ) / J) ≤ phi ((switchIndex J j r : ℝ) / r) ∧
      phi ((switchIndex J j r : ℝ) / r) <
        switchThreshold ((j : ℝ) / J) + 9 / r := by
  have hlt := depth_lt hJ hj
  have hspec := switchIndex_spec hJ hj hr heven
  constructor
  · exact (accepts_iff hJ hlt hr).mp hspec.2
  · have hpos := switchIndex_pos hJ hj hr heven
    have hpre : phi (((switchIndex J j r - 1 : ℕ) : ℝ) / r) <
        switchThreshold ((j : ℝ) / J) := by
      apply lt_of_not_ge
      intro ha
      exact predecessor_rejected hJ hj hr heven ((accepts_iff hJ hlt hr).mpr ha)
    have hrR : (0 : ℝ) < r := by exact_mod_cast hr
    have hpR : ((switchIndex J j r - 1 : ℕ) : ℝ) = (switchIndex J j r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega), Nat.cast_one]
    apply phi_step_rounding
      (ratio_mem_half hr (show switchIndex J j r - 1 ≤ r / 2 by omega))
      (switch_ratio_mem hJ hj hr heven) hrR ?_ hpre
    rw [hpR]
    field_simp
    <;> ring

theorem actual_totalSize (n : ℕ) : mu n = blockCount (inputBits n) * muZero n := rfl

theorem actual_residual_even (n j : ℕ) : 2 ∣ residualSize n j := by
  exact dvd_mul_of_dvd_right (microSize_even (inputBits n)) _

theorem actual_depth_condition {n j : ℕ} (hj : j ≤ terminalDepth n) :
    20 * j ≤ 13 * blockCount (inputBits n) := by
  have hm := Nat.div_mul_le_self (13 * blockCount (inputBits n)) 20
  unfold terminalDepth at hj
  omega

theorem actual_residual_pos {n j : ℕ} (hmu : 0 < mu n) (hj : j ≤ terminalDepth n) :
    0 < residualSize n j := by
  rw [actual_totalSize] at hmu
  have hp := And.intro (Nat.pos_of_mul_pos_right hmu) (Nat.pos_of_mul_pos_left hmu)
  have hd := depth_lt hp.1 (actual_depth_condition hj)
  exact Nat.mul_pos (Nat.sub_pos_of_lt hd) hp.2

theorem residual_real_identity {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    (residualSize n j : ℝ) =
      (1 - (j : ℝ) / blockCount (inputBits n)) * mu n := by
  have hm := hmu
  rw [actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hlt := depth_lt hp.1 (actual_depth_condition hj)
  have hJ : (blockCount (inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hp.1.ne'
  simp only [residualSize, actual_totalSize, Nat.cast_mul, Nat.cast_sub hlt.le]
  field_simp
  <;> ring

theorem actual_switch_certified {n j : ℕ} (hmu : 0 < mu n)
    (hj : j ≤ terminalDepth n) :
    let a : ℝ := (j : ℝ) / blockCount (inputBits n)
    let t : ℝ := (actualSwitch n j : ℝ) / residualSize n j
    t ∈ Icc (0 : ℝ) (1 / 2) ∧
      boxSaving ≤ 2 * bandShift - a + (1 - a) * gamma t ∧
      (1 - a) * entropy t <
        entropyRatio * (1 + boxSaving - 2 * bandShift) + 9 * entropyRatio / mu n := by
  dsimp only
  have hm := hmu
  rw [actual_totalSize] at hm
  have hp := And.intro (Nat.pos_of_mul_pos_right hm) (Nat.pos_of_mul_pos_left hm)
  have hdepth := actual_depth_condition hj
  have hr := actual_residual_pos hmu hj
  have he := actual_residual_even n j
  have ha := depth_fraction hp.1 hdepth
  have ht := switch_ratio_mem hp.1 hdepth hr he
  have hf := phi_enclosure hp.1 hdepth hr he
  change ((switchIndex _ _ _ : ℝ) / _) ∈ _ ∧ _
  refine ⟨ht, switch_box_bound ha ht hf.1, ?_⟩
  apply switch_entropy_bound ha ht (by exact_mod_cast hmu)
  rw [← residual_real_identity hmu hj]
  exact hf.2

theorem terminal_fraction_exact {n : ℕ} (hmu : 0 < mu n) :
    (terminalDepth n : ℝ) / blockCount (inputBits n) = terminalFraction := by
  have hm := hmu
  rw [actual_totalSize] at hm
  have hJ := Nat.pos_of_mul_pos_right hm
  have hd : 20 ∣ 13 * blockCount (inputBits n) :=
    dvd_mul_of_dvd_right (blockCount_multiple_twenty (inputBits n)) _
  have hid := Nat.div_mul_cancel hd
  have hidR : (terminalDepth n : ℝ) * 20 = 13 * (blockCount (inputBits n) : ℝ) := by
    exact_mod_cast hid
  have hJR : (blockCount (inputBits n) : ℝ) ≠ 0 := by exact_mod_cast hJ.ne'
  unfold terminalFraction
  field_simp
  linarith

end
end ThreeSum.Switch
