import Submission.ThreeSum.TernaryCodeSemantics
namespace ThreeSum.TernaryAddressDecode
open TernaryJointType TernaryCodeSemantics

def word (N code : ℕ) : TritWord N := fun i =>
  ⟨LightTernaryCodes.digit (2*N) (low i) (high i) code,
    Nat.lt_succ_of_le (LightTernaryCodes.digit_le_two _ _ _ _)⟩

theorem word_address {N : ℕ} (W : TritWord N) : word N (address W)=W := by
  funext i
  apply Fin.ext
  exact digit_eq W i

end ThreeSum.TernaryAddressDecode
