import Submission.ThreeSum.Scales
import Submission.ThreeSumApsp.Lang.Lib.Logs

/-!
# Compute the prescribed common-prime depth without division

The loop compares successive `4*(4*y)^(i+1)` with the radix. It returns
exactly `Nat.log (4*y) (R/4)`, including the zero-depth case. Only local
variables change, and the number of iterations is that logarithm.
-/

namespace ThreeSum.LightBandPrimeDepth

open Light

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

def depth (R y : ℕ) : ℕ := Nat.log (4*y) (R/4)

def body : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 16 *' v 1) ;;
  .while (v 3 ≤' v 0) (
    .set 3 (k 4 *' v 1 *' v 3) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)

def time (R y : ℕ) : ℕ := 30*depth R y+30
def word (R y : ℕ) : ℕ := 4*y*(R+4)+R+8

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ} {R y : ℕ}

theorem meets {p : ℕ} (hp : P[p]?=some body) (hy : 0 < y)
    (hword : (word R y : ℤ) ≤ lim.word) :
    Meets lim P p d [R,y] μ (time R y)
      (fun result ν => result=(depth R y : ℤ) ∧ ν=μ) := by
  have hbase : 1 < 4*y := by omega
  have hltq := Nat.lt_pow_succ_log_self hbase (R/4)
  simp only [Nat.succ_eq_add_one] at hltq
  have hlt : R < 4*(4*y)^(depth R y+1) := by unfold depth; omega
  have hdepth : depth R y ≤ R := (Nat.log_le_self _ _).trans (Nat.div_le_self _ _)
  have hstart : (16*y : ℕ) ≤ word R y := by unfold word; nlinarith
  have hR : (R : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by unfold word; omega : R ≤ word R y)).trans hword
  have hR1Word : (R : ℤ)+1 ≤ lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr (by unfold word; omega : R+1 ≤ word R y)).trans hword
  have hstartWord : ((16*y : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hstart).trans hword
  have hdepthWord : (depth R y : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hdepth).trans hR
  have hpower (i : ℕ) (hi : i ≤ depth R y) : 4*(4*y)^(i+1) ≤ word R y := by
    by_cases hz : R/4=0
    · have hi0 : i=0 := by simp only [depth,hz,Nat.log_zero_right] at hi; omega
      subst i
      simpa only [Nat.zero_add,pow_one,← Nat.mul_assoc,show 4*4=16 by decide] using hstart
    · have hiLog : i ≤ Nat.log (4*y) (R/4) := hi
      have hp := (Nat.pow_le_pow_right hbase.le hiLog).trans (Nat.pow_log_le_self _ hz)
      have h4 : 4*(4*y)^i ≤ R := by omega
      have hm := Nat.mul_le_mul_right (4*y) h4
      rw [pow_succ]
      unfold word
      nlinarith
  have hinit : 4*(4*y)^(0+1)=16*y := by ring
  have hfourWord : (4 : ℤ)*(y : ℤ) ≤ lim.word := by
    have hh : 4*y ≤ word R y := by omega
    exact_mod_cast (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body hp
  unfold body time
  light_set (0 : ℕ)
  light_set (16*y : ℕ)
  refine Ends.next _ (Ends.whileBlock (T := 30*depth R y+10) (fun i σ =>
    σ=⟨frame [R,y,i,(4*(4*y)^(i+1) : ℕ)],μ⟩)
    (depth R y) (by simp; rw [show (16 : ℤ)*(y : ℤ)=4*(4*(y : ℤ)) by ring]) ?round ?done (by simp; omega))
    (hT := by light_time)
  case round =>
    rintro i _ hi rfl
    have hqne : R/4 ≠ 0 := by
      intro hz
      simp [depth,hz] at hi
    have hiLog : i+1 ≤ Nat.log (4*y) (R/4) := by change i < Nat.log (4*y) (R/4) at hi; omega
    have hpow : (4*y)^(i+1) ≤ R/4 :=
      (Nat.pow_le_pow_right hbase.le hiLog).trans (Nat.pow_log_le_self _ hqne)
    have hle : 4*(4*y)^(i+1) ≤ R := by omega
    have hic : i+1 ≤ R := by omega
    have hcurrentWord : ((4*(4*y)^(i+1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hpower i (by omega))).trans hword
    have hnext : 4*y*(4*(4*y)^(i+1)) ≤ word R y := by
      have hh := Nat.mul_le_mul_left (4*y) hle
      unfold word
      nlinarith
    have hnextZ : ((4*y*(4*(4*y)^(i+1)) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hnext).trans hword
    have heq : 4*(4*y)^(i+1+1)=4*y*(4*(4*y)^(i+1)) := by ring
    rw [heq]
    generalize 4*(4*y)^(i+1)=q at hle hnextZ hcurrentWord ⊢
    have hprodZ : (4 : ℤ)*(y : ℤ)*(q : ℤ) ≤ lim.word := by
      simpa only [Nat.cast_mul,Nat.cast_ofNat] using hnextZ
    have hprodN : (0 : ℤ) ≤ (4 : ℤ)*(y : ℤ)*(q : ℤ) := by positivity
    exact ⟨by light_side,by light_side,by light_side,by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hlastWord : ((4*(4*y)^(depth R y+1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hpower _ le_rfl)).trans hword
    generalize 4*(4*y)^(depth R y+1)=q at hlt hlastWord ⊢
    refine ⟨by light_side,by light_side,?_⟩
    light_set (depth R y)
    exact ⟨rfl,rfl⟩

def program : Program := [body]

theorem program_meets (hy : 0 < y) (hword : (word R y : ℤ) ≤ lim.word) :
    Meets lim program 0 d [R,y] μ (time R y)
      (fun result ν => result=(depth R y : ℤ) ∧ ν=μ) := meets rfl hy hword

theorem depth_eq_primeDepth (n : ℕ) :
    depth (Scales.radix n) (Scales.primeWindow n)=Scales.primeDepth Scales.radix n := rfl

end ThreeSum.LightBandPrimeDepth
