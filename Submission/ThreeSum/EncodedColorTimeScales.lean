import Submission.ThreeSum.EncodedColorPipelineResources
import Submission.ThreeSum.SharedReportingCostBounds
import Submission.ThreeSum.BandPrimeCostBounds

/-!
# Subpolynomial scalar work in the actual selected-color preprocessing

Polynomial resource bounds are used only inside integer logarithms here.
The resulting bit-length work has exponent zero, regardless of the
polynomial degree needed to contain the machine's stored integers.
-/

namespace ThreeSum.EncodedColorTime

open Filter Real Scales BandScales Parameters StageBounds ArithmeticStageBounds
open EncodedColorResources LocalCoverBounds
open scoped Topology

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

noncomputable section

theorem sum_zero {f g : ℕ → ℕ} (hf : PowerBound f 0) (hg : PowerBound g 0) :
    PowerBound (fun n => f n+g n) 0 := hf.add_same hg

theorem product_zero {f g : ℕ → ℕ} (hf : PowerBound f 0) (hg : PowerBound g 0) :
    PowerBound (fun n => f n*g n) 0 := by simpa only [zero_add] using hf.mul hg

theorem power_zero {f : ℕ → ℕ} (hf : PowerBound f 0) (k : ℕ) :
    PowerBound (fun n => f n^k) 0 := by simpa only [mul_zero] using hf.pow k

theorem log_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    PowerBound (fun n => Nat.log 2 (f n+1)) 0 := by
  let k : ℕ := ⌈a+1⌉₊
  have hk : a+1 ≤ (k : ℝ) := Nat.le_ceil _
  apply powerBound_mono (bitBudget_powerBound k)
  filter_upwards [hf 1 (by norm_num),eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hh := hn.trans (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn1) hk)
  rw [Real.rpow_natCast] at hh
  have hfn : f n ≤ n^k := by exact_mod_cast hh
  exact (Nat.log_mono_right (b := 2) (Nat.add_le_add_right hfn 1)).trans
    ((Nat.le_succ _).trans (remainder_bits_le k (by omega)))

theorem clog_powerBound {f : ℕ → ℕ} {a : ℝ} (hf : PowerBound f a) :
    PowerBound (fun n => Nat.clog 2 (f n)) 0 := by
  apply powerBound_mono (sum_zero (log_powerBound hf) (PowerBound.const 1))
  exact Eventually.of_forall fun n => Nat.clog_le_of_le_pow
    ((Nat.le_succ (f n)).trans (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (f n+1)).le)

theorem bounded_log {f : ℕ → ℕ} (C e : ℕ)
    (hf : ∀ n, f n ≤ C*(scale n)^e) :
    PowerBound (fun n => Nat.log 2 (f n+1)) 0 :=
  log_powerBound (powerBound_mono ((PowerBound.const C).mul (scale_powerBound.pow e))
    (Eventually.of_forall hf))

theorem half_powerBound : PowerBound half 0 := SharedReportingCosts.half_powerBound

theorem blocks_powerBound : PowerBound blocks 0 := SharedReportingCosts.blocks_powerBound

theorem local_width_powerBound : PowerBound (fun n => 512*half n) 0 :=
  product_zero (PowerBound.const 512) half_powerBound

theorem width_powerBound : PowerBound width 0 :=
  product_zero blocks_powerBound local_width_powerBound

theorem mu_powerBound : PowerBound mu 0 := by
  have hh := product_zero (product_zero (PowerBound.const 2) half_powerBound) blocks_powerBound
  simpa only [half,blocks,BlockSourceSharing.cutoff_eq] using hh

theorem local_product_log_powerBound :
    PowerBound (fun n => Nat.log 2 ((512*half n)*localPrime (half n)+1)) 0 := by
  apply bounded_log 1 2
  intro n
  have hL : 512*half n ≤ scale n := by have h := (local_bounds n).width; omega
  have hP : localPrime (half n) ≤ scale n := by have h := (local_bounds n).prime; omega
  simpa only [one_mul,pow_two] using Nat.mul_le_mul hL hP

theorem endpoint_log_powerBound :
    PowerBound (fun n => Nat.log 2 (LightBlockSourceBuild.endpointBound (half n) (blocks n)+1)) 0 :=
  bounded_log 1 2 (fun n => by simpa only [one_mul] using endpoint_le n)

theorem occurrence_log_powerBound :
    PowerBound (fun n => Nat.log 2 (LightBlockSourceCatalog.count (half n) (blocks n)+1)) 0 :=
  bounded_log 1 1 (fun n => by simpa only [one_mul,pow_one] using (powers n).2.1)

theorem key_log_powerBound :
    PowerBound (fun n => Nat.log 2 (LightGuardedWanted.keyBound (maxMod n) (half n) (blocks n)+1)) 0 :=
  bounded_log 3 4 keyBound_le

theorem moduli_log_powerBound :
    PowerBound (fun n => Nat.log 2 (maxMod n+radix n+1)) 0 := by
  apply bounded_log 2 1
  intro n
  have hp := (scale_bounds n).2.2.2.2.1
  have hm := (dimensions n).2.2.2.2
  simp only [pow_one]
  omega

theorem radix_log_powerBound :
    PowerBound (fun n => Nat.log 2 (radix n+radix n+1)) 0 := by
  apply bounded_log 2 1
  intro n
  have hm := (dimensions n).2.2.2.2
  simp only [pow_one]
  omega

theorem input_log_powerBound (k : ℕ) : PowerBound (fun n => Nat.log 2 (n^k+1)) 0 :=
  log_powerBound (identity_powerBound.pow k)

end
end ThreeSum.EncodedColorTime
