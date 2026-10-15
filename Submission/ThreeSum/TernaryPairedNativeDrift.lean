import Submission.ThreeSum.TernaryOversizeOverhead
import Submission.ThreeSum.TernaryPairedRecurrence

/-! A deliberately generous exact integer margin. Once `(9F)^4≤M`,
the oversized native field gives enough contraction to pay the complete
initial paired score, including original carry choices and logarithmic
minor factors. -/

namespace ThreeSum.TernaryPairedNativeDrift

theorem native_power_lower (K M R S p : ℕ) (hS : M≤S^K)
    (hp : M*R*S^2≤p^2) :
    M^(K+2)*R^K≤p^(2*K) := by
  have hs2 := Nat.pow_le_pow_left hS 2
  have hpK := Nat.pow_le_pow_left hp K
  have he : (S^K)^2=(S^2)^K := by
    rw [←pow_mul,←pow_mul,Nat.mul_comm K 2]
  calc
    _ = (M^K*R^K)*M^2 := by rw [pow_add]; ring
    _ ≤ (M^K*R^K)*(S^K)^2 := Nat.mul_le_mul_left _ hs2
    _ = (M*R*S^2)^K := by rw [he,mul_pow,mul_pow]
    _ ≤ (p^2)^K := hpK
    _ = _ := by rw [←pow_mul]

theorem paired_native_drift (K M R S p F : ℕ)
    (hS : M≤S^K) (hp : M*R*S^2≤p^2) (hF : (9*F)^4≤M) :
    (9*F*M*R^K)^4*M^(4*K+3)≤(p^(2*K))^4 := by
  have hlower := native_power_lower K M R S p hS hp
  calc
    _ = (9*F)^4*M^(4*K+7)*R^(4*K) := by
      rw [mul_pow,mul_pow,←pow_mul,Nat.mul_comm K 4]
      have hm : M^4*M^(4*K+3)=M^(4*K+7) := by
        rw [←pow_add]
        congr 1
        omega
      calc
        _ = (9*F)^4*(M^4*M^(4*K+3))*R^(4*K) := by ring
        _ = _ := by rw [hm]
    _ ≤ M*M^(4*K+7)*R^(4*K) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hF)
    _ = (M^(K+2)*R^K)^4 := by
      rw [mul_pow,←pow_mul,←pow_mul]
      have hm : M*M^(4*K+7)=M^((K+2)*4) := by
        rw [←pow_succ']
        congr 1
        ring
      rw [hm]
      congr 1
      congr 1
      ring
    _ ≤ _ := Nat.pow_le_pow_left hlower 4

end ThreeSum.TernaryPairedNativeDrift
