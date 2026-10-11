import Submission.ThreeSum.BandWeightedScore

/-! # Constant-time exact truncated band lengths for weighted-score calls -/

namespace ThreeSum.LightBandWeightedScoreSlice

open Light

set_option maxHeartbeats 900000

def body : Stmt :=
  .set 3 (v 2 *' v 1) ;;
  .set 4 (v 0 -' v 3) ;;
  .ite (v 1 <' v 4) (.set 4 (v 1)) .skip ;;
  .set 0 (v 4)

def time : ℕ := 80

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}

theorem meets {pMain n g i : ℕ} (hmain : P[pMain]?=some body)
    (hg : 0 < g) (hi : i*g ≤ n) (hword : ((n+g+4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [n,g,i] μ time
      (fun r ν => r=(BandWeightedScore.length n g i : ℤ) ∧ ν=μ) := by
  have hnWord : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (show n ≤ n+g+4 by omega)).trans hword
  have hgWord : (g : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (show g ≤ n+g+4 by omega)).trans hword
  have hiN : i ≤ n := (Nat.le_mul_of_pos_right i hg).trans hi
  have hiWord : (i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hiN).trans hnWord
  have hprodWord : (i : ℤ)*(g : ℤ) ≤ lim.word :=
    (by exact_mod_cast hi : (i : ℤ)*(g : ℤ) ≤ (n : ℤ)).trans hnWord
  have hprodNonneg : (0 : ℤ) ≤ (i : ℤ)*(g : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  apply Meets.of_body hmain
  unfold body time
  light_set (i*g : ℕ)
  light_set (n-i*g : ℕ)
  light_if hlt hlt : (g : ℤ) < ((n-i*g : ℕ) : ℤ)
  · light_set (g : ℕ)
    light_set (g : ℕ)
    exact ⟨by rw [BandWeightedScore.length,min_eq_left (show g ≤ n-i*g by omega)]; rfl,rfl⟩
  · light_set (n-i*g : ℕ)
    exact ⟨by rw [BandWeightedScore.length,min_eq_right (show n-i*g ≤ g by omega)]; rfl,rfl⟩

def program : Program := [body]

theorem program_meets {n g i : ℕ}
    (hg : 0 < g) (hi : i*g ≤ n) (hword : ((n+g+4 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 0 d [n,g,i] μ time
      (fun r ν => r=(BandWeightedScore.length n g i : ℤ) ∧ ν=μ) :=
  meets rfl hg hi hword

end ThreeSum.LightBandWeightedScoreSlice
