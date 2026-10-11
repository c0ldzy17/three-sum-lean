import Submission.ThreeSum.LightParameterInit
import Submission.ThreeSum.EncodedColorPrimeResources

/-! # Exact polynomial resources for the executed parameter initializer

The nineteen-cell output starts at an arbitrary destination. Scratch begins
immediately after that header; its reservation is translated only once.
-/

namespace ThreeSum.ThreeSumParameterResources

open Light Scales BandScales LocalCoverBounds EncodedColorResources StageBounds

set_option maxHeartbeats 2200000
set_option maxRecDepth 14000

def work (dst : ℕ) : ℕ := dst+19
def cells (n : ℕ) : ℕ := 19+LightParameterInit.space 0 n
def depth (n : ℕ) : ℕ := 512*LightParameterInit.half n+6
def envelope (n : ℕ) : ℕ := 20000*scale n
def need (n _U : ℕ) : Light.Need := ⟨LightParameterInit.word n,cells n,depth n⟩

theorem local_envelope_le (n : ℕ) :
    LocalParameterBounds.envelope (LightParameterInit.half n) ≤ localEnvelope n := by
  unfold LocalParameterBounds.envelope localEnvelope LightLocalCoverInitResources.envelope
  apply Nat.pow_le_pow_right (by decide)
  change 2048*(half n+1)+2 ≤ 5000000*(half n+1)^2
  nlinarith only [Nat.zero_le (half n*half n)]

theorem local_word_le (n : ℕ) : LightLocalParameters.word (LightParameterInit.half n) ≤ scale n :=
  (LocalParameterBounds.word_bound _).trans ((local_envelope_le n).trans (scale_bounds n).2.2.2.1)

theorem local_output_power_le (n : ℕ) :
    LightGlobalSizes.localCount n^(blockCount (inputBits n)) ≤ scale n := by
  have hcount : LightGlobalSizes.localCount n ≤ 2^(512*half n) := Nat.choose_le_two_pow _ _
  calc
    _ ≤ (2^(512*half n))^(blocks n) := Nat.pow_le_pow_left hcount _
    _ = 2^(width n) := by unfold width; rw [← pow_mul]; congr 1; ring
    _ ≤ 2^(width n+1) := Nat.pow_le_pow_right (by decide) (by omega)
    _ ≤ scale n := (powers n).1

theorem divisor_le (n : ℕ) : LightGlobalSizes.divisor (mu n) ≤ scale n := by
  have ht : mu n ≤ inputBits n := LightScales.totalSize_le_self _
  have hd := Nat.div_le_self (mu n) 20
  have hp : LightGlobalSizes.divisor (mu n) ≤ SharedReportingBankResourceBounds.magnitude n :=
    Nat.pow_le_pow_right (by decide) (by omega)
  exact hp.trans (scale_bounds n).2.2.1

theorem global_word_le (n : ℕ) :
    LightGlobalSizes.word (LightGlobalSizes.localCount n) (localRadix n)
      (blockCount (inputBits n)) (mu n) ≤ 8000*scale n := by
  have hS : 1 ≤ scale n := by have hh := (scale_bounds n).1; omega
  have hC : LightGlobalSizes.localCount n ≤ scale n := layer_le n
  have hp : localRadix n ≤ scale n := by
    have hh := (local_bounds n).prime
    change localRadix n+1 ≤ scale n at hh
    omega
  have hJ : blockCount (inputBits n)+1 ≤ scale n := (dimensions n).2.1
  have hmu : mu n+1 ≤ scale n := (dimensions n).2.2.1
  have hCP := local_output_power_le n
  have hPP : localRadix n^(blockCount (inputBits n)) ≤ scale n := (dimensions n).2.2.2.2
  have hd := divisor_le n
  unfold LightGlobalSizes.word
  omega

theorem word_bound (n : ℕ) : LightParameterInit.word n ≤ envelope n := by
  have hn := (scale_bounds n).2.1
  have hb := (Nat.add_le_add_right (LightScales.inputBits_le_self n) 1).trans hn
  have hy := (scale_bounds n).2.2.2.2.2
  have hl := local_word_le n
  have hg := global_word_le n
  unfold LightParameterInit.word envelope
  omega

theorem space_eq (dst n : ℕ) : LightParameterInit.space (work dst) n=dst+cells n := by
  unfold work cells LightParameterInit.space LightLocalParameters.space LightLocalCounts.space
    LightSelectedPrime.space LightPrimePool.space
  omega

theorem cells_bound (n : ℕ) : cells n ≤ envelope n := by
  have hh := LocalParameterBounds.space_bound 0 (LightParameterInit.half n)
  have he := (local_envelope_le n).trans (scale_bounds n).2.2.2.1
  have hs := (scale_bounds n).1
  unfold cells LightParameterInit.space envelope
  omega

theorem depth_bound (n : ℕ) : depth n ≤ envelope n := by
  have hh := (local_bounds n).width
  change 512*LightParameterInit.half n+1 ≤ scale n at hh
  have hs := (scale_bounds n).1
  unfold depth envelope
  omega

noncomputable section

theorem envelope_powerBound : PowerBound envelope 2048 := by
  change PowerBound (fun n => 20000*scale n) 2048
  simpa only [zero_add] using (PowerBound.const 20000).mul scale_powerBound

theorem poly_need : Light.PolyNeed need := by
  apply PolynomialResources.polyNeed_of_envelope envelope_powerBound 0
  · intro n U; simpa only [need,pow_zero,mul_one] using word_bound n
  · intro n U; simpa only [need,pow_zero,mul_one] using cells_bound n
  · intro n U; simpa only [need,pow_zero,mul_one] using depth_bound n

end

theorem resources_of_ok {lim : Limits} {n U dst d : ℕ}
    (hok : (need n U).Ok lim dst d) :
    LightParameterInit.space (work dst) n ≤ lim.space ∧
    (LightParameterInit.word n : ℤ) ≤ lim.word ∧
      d+512*LightParameterInit.half n+6 ≤ lim.depth := by
  refine ⟨?_,hok.word,?_⟩
  · rw [space_eq]
    exact hok.cells
  · simpa only [need,depth,Nat.add_assoc] using hok.depth

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {n U dst d : ℕ}
    (hok : (need n U).Ok lim dst d) :
    Meets lim LightParameterInit.program 0 d [n,dst,work dst] μ (LightParameterInit.time n)
      (fun r ν => r=(radix n : ℤ) ∧ Seg ν dst (LightParameterInit.values n) ∧
        KeptBut μ ν (work dst) dst 19) := by
  obtain ⟨hs,hw,hd⟩ := resources_of_ok hok
  exact LightParameterInit.program_meets hok.space hd le_rfl hs hw

theorem kept_of_post {μ ν : ℕ→ℤ} {dst : ℕ} (H : KeptBut μ ν (work dst) dst 19) :
    Kept μ ν dst := by
  intro i hi
  exact H i ⟨by unfold work; omega,Or.inl hi⟩

end ThreeSum.ThreeSumParameterResources
