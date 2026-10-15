import Submission.ThreeSum.LightTernaryPrefixSetup
import Submission.ThreeSum.TernaryFrontendResources

/-! Polynomial needs of actual prefix-bank setup, uniformly over all positive
prefixes up to the actual computed radix length. -/
noncomputable section
namespace ThreeSum.TernaryPrefixSetupResources
open Light LightTernaryPrefixSetup StageBounds TernaryCoverScale
open TernaryFrontendResources
open Filter
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

def need (m j F : ℕ) : Light.Need :=
  ⟨LightTernaryPrefixSetup.word m j F,4^(N m j)+2*N m j+9,N m j+4⟩

theorem need_ok {lim : Limits} {m j F free d : ℕ}
    (H : (need m j F).Ok lim free d) :
    endAt free m j≤ lim.space ∧ (LightTernaryPrefixSetup.word m j F:ℤ)≤ lim.word ∧
      d+N m j+4≤ lim.depth := by
  refine ⟨?_,H.word,?_⟩
  · have hh:= H.cells
    dsimp [need,endAt,headerAt,workAt] at hh ⊢
    omega
  · exact H.depth

theorem meets {lim : Limits} {m j F free d : ℕ} (μ : ℕ→ ℤ)
    (H : (need m j F).Ok lim free d) :
    Meets lim LightTernaryPrefixSetup.allocatedProgram 5 d [j,m,F,free] μ
      (allocateTime m j)
      (fun r ν=>r=(headerAt free m j:ℤ) ∧
        Seg ν (headerAt free m j) (header m j F free (workAt free m j)) ∧
        Seg ν free ((TernaryAddresses.codes (N m j) (T m j)).map (fun (c:ℕ)=>(c:ℤ))) ∧
        LightSubsetAddress.Powers ν (workAt free m j) (2*N m j) ∧ Kept μ ν free) := by
  obtain ⟨hs,hw,hd⟩:= need_ok H
  exact allocated_program_meets μ H.space hs hw hd

theorem need_mono_prefix {m j r F : ℕ} (hjr : j≤ r) :
    (need m j F).word≤ (need m r F).word ∧
    (need m j F).cells≤ (need m r F).cells ∧
    (need m j F).depth≤ (need m r F).depth := by
  have hN : N m j≤ N m r := by unfold N; exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hjr)
  have hp:= Nat.pow_le_pow_right (by omega : 1≤ F+1) (Nat.add_le_add_right hjr 1)
  have h4:= Nat.pow_le_pow_right (by decide : 1≤ 4) hN
  have h4':= Nat.pow_le_pow_right (by decide : 1≤ 4) (Nat.add_le_add_right hN 1)
  dsimp [need,LightTernaryPrefixSetup.word]
  exact ⟨by omega,by omega,by omega⟩

def exponent (m F : ℕ) : ℝ :=
  1+|2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)|+
    |2*Real.log (4^TernaryLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)|

theorem exponent_bounds (m F : ℕ) :
    0≤ exponent m F ∧
    2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)≤ exponent m F ∧
    2*Real.log (4^TernaryLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)≤ exponent m F := by
  unfold exponent
  constructor
  · positivity
  constructor <;> linarith [le_abs_self (2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)),
    le_abs_self (2*Real.log (4^TernaryLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)),
    abs_nonneg (2*Real.log (F+1:ℕ)/Real.log (outputSize m:ℝ)),
    abs_nonneg (2*Real.log (4^TernaryLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ))]

theorem dimensions_powerBound {m : ℕ} (hm : 0<m) :
    PowerBound (fun n=>N m (radixLength m n)) 0 := by
  simpa [N,TernaryLocalParameters.fixedLength] using fixed_dimension_powerBound hm

theorem word_powerBound {m : ℕ} (hm : 0<m) (F : ℕ) :
    PowerBound (fun n=>(need m (radixLength m n) F).word) (exponent m F) := by
  obtain ⟨h0,hg,hmk⟩:= exponent_bounds m F
  have hconst (c : ℕ) : PowerBound (fun _=>c) (exponent m F) :=
    (PowerBound.const c).mono_exponent h0
  have hN:= ((PowerBound.const 2).mul (dimensions_powerBound hm)).mono_exponent (by simpa using h0)
  have hr:= (radix_length_powerBound hm).mono_exponent h0
  have hgroups:= ((PowerBound.const (F+1)).mul (fixed_radix_powerBound hm F)).mono_exponent
    (by simpa using hg)
  have hmask:= ((PowerBound.const 4).mul (full_mask_powerBound hm)).mono_exponent
    (by simpa using hmk)
  have hh:= (((((((hconst 100000000).add_same hN).add_same hr).add_same (hconst m)).add_same
    (hconst F)).add_same hgroups).add_same hmask).add_same (hconst 100)
  convert hh using 1
  funext n
  dsimp [need,LightTernaryPrefixSetup.word,N,TernaryLocalParameters.fixedLength]
  simp only [pow_succ]
  ring

theorem cells_powerBound {m : ℕ} (hm : 0<m) (F : ℕ) :
    PowerBound (fun n=>(need m (radixLength m n) F).cells) (exponent m F) := by
  obtain ⟨h0,_,hmk⟩:= exponent_bounds m F
  have hmask:= (full_mask_powerBound hm).mono_exponent hmk
  have hN:= ((PowerBound.const 2).mul (dimensions_powerBound hm)).mono_exponent (by simpa using h0)
  have hh:= (hmask.add_same hN).add_same ((PowerBound.const 9).mono_exponent h0)
  exact hh

theorem depth_powerBound {m : ℕ} (hm : 0<m) (F : ℕ) :
    PowerBound (fun n=>(need m (radixLength m n) F).depth) 0 := by
  exact (dimensions_powerBound hm).add_same (PowerBound.const 4)

theorem polyNeed {m : ℕ} (hm : 0<m) (F : ℕ) :
    Light.PolyNeed (fun n _U=>need m (radixLength m n) F) := by
  apply PolynomialResources.polyNeed_of_separate_envelopes
    (word_powerBound hm F) (cells_powerBound hm F) (depth_powerBound hm F) 0 0 0
  all_goals intro n U; simp

end ThreeSum.TernaryPrefixSetupResources
