import Submission.ThreeSum.LightTernaryParallelDictionaries
namespace ThreeSum.LightTernaryParallelBudget

/-- Every prefix stage is charged; no source-array generation is free. -/
theorem radix_time_bound (N : ℕ) (hN : 1≤N) : ∀ J,
    LightRadixKeys.time N J ≤ 500*(J+1)*(N^J+N+1) := by
  intro J
  induction J with
  | zero => simp [LightRadixKeys.time]; omega
  | succ J ih =>
    have hp : N^J ≤ N^(J+1) := Nat.pow_le_pow_right hN (by omega)
    have ht : 500*(J+1)*(N^J+N+1) ≤ 500*(J+1)*(N^(J+1)+N+1) :=
      Nat.mul_le_mul_left _ (by omega)
    have hs : LightRadixRows.time N (N^J)+200 ≤ 500*(N^(J+1)+N+1) := by
      unfold LightRadixRows.time LightReportingAffine.time
      rw [pow_succ']
      nlinarith [Nat.zero_le (N*N^J)]
    rw [LightRadixKeys.time]
    have hadd := Nat.add_le_add (ih.trans ht) hs
    nlinarith

theorem dictionary_time_bound (xs : List ℤ) (hm : 1≤xs.length) (J : ℕ) :
    LightFixedRadixDictionary.time xs J ≤ 1000*(J+1)*(xs.length^J+xs.length+1) := by
  have ht := radix_time_bound xs.length hm J
  have hmono : xs.length+1 ≤ (J+1)*(xs.length^J+xs.length+1) := by
    calc
      xs.length+1 ≤ xs.length^J+xs.length+1 := by omega
      _ ≤ (J+1)*(xs.length^J+xs.length+1) := Nat.le_mul_of_pos_left _ (by omega)
  unfold LightFixedRadixDictionary.time
  nlinarith

theorem parallel_time_bound (xs ys zs : List ℤ) (hxy : ys.length=xs.length)
    (hxz : zs.length=xs.length) (hm : 1≤xs.length) (J : ℕ) :
    LightTernaryParallelDictionaries.time xs ys zs J ≤
      4000*(J+1)*(xs.length^J+xs.length+1) := by
  have h0 := dictionary_time_bound xs hm J
  have h1 := dictionary_time_bound ys (by omega) J
  have h2 := dictionary_time_bound zs (by omega) J
  have hpos : 1 ≤ (J+1)*(xs.length^J+xs.length+1) := by
    exact Nat.succ_le_of_lt (Nat.mul_pos (by omega) (by omega))
  rw [hxy] at h1
  rw [hxz] at h2
  unfold LightTernaryParallelDictionaries.time
  nlinarith
end ThreeSum.LightTernaryParallelBudget
