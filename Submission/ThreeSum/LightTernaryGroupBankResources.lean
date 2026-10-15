import Submission.ThreeSum.LightTernaryGroupedBanks

namespace ThreeSum.LightTernaryGroupBankStep

theorem time_bound (N L n : ℕ) : time N L n≤30000*(N+1)*(N+L+1)*(n+1) := by
  have hb := LightTernaryBankAssembly.time_bound N L n
  have hpos : 1≤(N+1)*(N+L+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_right (n+1) hpos
  unfold time Light.copyTime
  nlinarith only [hb,hs]

end ThreeSum.LightTernaryGroupBankStep
namespace ThreeSum.LightTernaryGroupedBanks

theorem time_bound (groups N L n : ℕ) :
    time groups N L n≤31000*(groups+1)*(N+1)*(N+L+1)*(n+1) := by
  have hb := LightTernaryGroupBankStep.time_bound N L n
  have hm := Nat.mul_le_mul_left groups hb
  have hpos : 1≤(N+1)*(N+L+1)*(n+1) := Nat.succ_le_of_lt (by positivity)
  have hs := Nat.mul_le_mul_left groups hpos
  unfold time
  nlinarith only [hm,hs,hpos]

end ThreeSum.LightTernaryGroupedBanks
