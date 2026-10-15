import Submission.ThreeSum.LightTernaryColorPreparation

namespace ThreeSum.TernaryColorPreparationLayout
open LightTernaryColorPreparation
set_option maxHeartbeats 1000000

 theorem color_end {free n W : ℕ} (hn : 0<n) (hW : LightColorParametersCosts.width n≤W) :
    LightTernaryColorPrelude.space free n≤headerAt free n W := by
  obtain ⟨_,hc,hw⟩ := LightTernaryColorPrelude.one_band hn
  unfold LightTernaryColorPrelude.space LightColorBands.space ColorBandBounds.space
  rw [hc,hw]
  unfold LightTernaryColorPrelude.work LightTernaryColorPrelude.ce LightTernaryColorPrelude.cv
    LightTernaryColorPrelude.be LightTernaryColorPrelude.bv LightTernaryColorPrelude.ae
    LightTernaryColorPrelude.av LightTernaryColorPrelude.class2 LightTernaryColorPrelude.class1
    LightTernaryColorPrelude.class0 headerAt
  omega

 theorem matrices_before_work (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)≤work free n W nA nB nC J ∧
    cMatrix free n W nB J+nC*(J+2)≤work free n W nA nB nC J ∧
    oMatrix free n W nA nB nC J+nA*2^J*(J+2)≤work free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J≤work free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)≤work free n W nA nB nC J := by
  unfold work oMatrix positions carry cMatrix bMatrix
  omega

 theorem matrix_separation (free n W nA nB nC J : ℕ) :
    bMatrix free n W+nB*(J+2)=cMatrix free n W nB J ∧
    cMatrix free n W nB J+nC*(J+2)=carry free n W nA nB nC J ∧
    carry free n W nA nB nC J+2^J*(J+1)=positions free n W nA nB nC J ∧
    positions free n W nA nB nC J+nA*2^J=oMatrix free n W nA nB nC J :=
  ⟨rfl,rfl,rfl,rfl⟩

 theorem division_space (free n W nA nB nC J U : ℕ) :
    LightTernarySignedMatrix.space (work free n W nA nB nC J) U≤arenaFree free n W nA nB nC J U ∧
    LightTernaryCarryCodes.space (work free n W nA nB nC J) (2^J)≤arenaFree free n W nA nB nC J U := by
  have hu := Nat.log_le_self 2 (3*U+1)
  have hq := Nat.log_le_self 2 (2^J+1)
  constructor
  · unfold LightTernarySignedMatrix.space LightTernarySignedRow.space LightOutputDecodeDigits.space arenaFree
    apply Nat.add_le_add_left
    calc
      _ ≤ (3*U+1)+2 := Nat.add_le_add_right hu 2
      _ ≤ _ := by nlinarith [Nat.zero_le (2^J)]
  · unfold LightTernaryCarryCodes.space LightOutputDecodeDigits.space arenaFree
    apply Nat.add_le_add_left
    calc
      _ ≤ (2^J+1)+2 := Nat.add_le_add_right hq 2
      _ ≤ _ := by nlinarith [Nat.zero_le (2^J)]

 theorem sources_before_matrix (free n W : ℕ) :
    LightTernaryColorPrelude.av free n+n≤bMatrix free n W ∧
    LightTernaryColorPrelude.bv free n+n≤bMatrix free n W ∧
    LightTernaryColorPrelude.cv free n+n≤bMatrix free n W := by
  unfold LightTernaryColorPrelude.cv LightTernaryColorPrelude.be LightTernaryColorPrelude.bv
    LightTernaryColorPrelude.ae LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
    LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0 bMatrix headerAt
  omega

end ThreeSum.TernaryColorPreparationLayout
