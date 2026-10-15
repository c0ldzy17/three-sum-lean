import Submission.ThreeSum.LightTernarySourceHost
import Submission.ThreeSum.LightTernaryParallelBudget
namespace ThreeSum.LightTernarySourceHostBudget
open LightTernarySourceHost

/-- The source host pays for all three product dictionaries, all emitted
original-position matches, and every map-separated compact bank cell. -/
theorem time_bound (xs ys zs : List ℤ) (hxy : ys.length=xs.length) (hxz : zs.length=xs.length)
    (hm : 1≤xs.length) (p J M NL U L bank groups cap : ℕ) (input : ℕ → ℤ)
    (hcap : ∀ i<NL, LightHistogram.count
      (fun j => WantedResidueKeys.code M 0 (dictionary xs p J j))
      (WantedResidueKeys.code M 0 (input i)) (size xs J)≤cap) :
    time xs ys zs p J M NL U L bank groups input ≤
      4000*(J+1)*(size xs J+xs.length+1)+
      2000*(NL+size xs J+M+NL*cap+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+1)+1)+
      1000*(L+1)*(NL*cap+groups*bank+1)+500 := by
  have hhcap : ∀ i<NL, LightHistogram.count
      (fun j => WantedResidueKeys.code M 0 ((LightTernaryOriginalJoin.keys (p : ℤ) xs J).getD j 0))
      (WantedResidueKeys.code M 0 (input i)) (LightTernaryOriginalJoin.keys (p : ℤ) xs J).length≤cap := by
    simpa only [LightTernaryOriginalJoin.keys,RadixKeyLists.values_length,dictionary,size] using hcap
  have hc := LightTernaryOriginalJoin.joinCount_le_of_cap hhcap
  have hc' : count xs p J M NL input≤NL*cap := by
    change WantedResidueKeys.total M input (fun j => (RadixKeyLists.values (p : ℤ) xs J).getD j 0)
      NL (xs.length^J) 0≤NL*cap
    simpa only [LightTernaryOriginalJoin.joinCount,LightTernaryOriginalJoin.keys,
      RadixKeyLists.values_length] using hc
  have hinit := LightTernaryParallelBudget.parallel_time_bound xs ys zs hxy hxz hm J
  have hjoin := LightTernaryOriginalJoin.time_bound_of_cap (U := U) (D := 0) hhcap
  have hjoin' : LightWantedSetup.time M input (dictionary xs p J) NL (size xs J) U 0 0≤
      2000*(NL+size xs J+M+NL*cap+1)*(Nat.log 2 (U+1)+Nat.log 2 (M+1)+1) := by
    change LightWantedSetup.time M input (fun j => (RadixKeyLists.values (p : ℤ) xs J).getD j 0)
      NL (xs.length^J) U 0 0≤_
    simpa only [LightTernaryOriginalJoin.keys,RadixKeyLists.values_length,size,Nat.add_zero] using hjoin
  have hhist := LightTernaryGroupedSources.time_bound L (count xs p J M NL input) bank groups
  have hhist' : LightTernaryGroupedSources.time L (count xs p J M NL input) bank groups≤
      1000*(L+1)*(NL*cap+groups*bank+1) := hhist.trans (Nat.mul_le_mul_left _ (by omega))
  unfold time
  change _≤4000*(J+1)*(xs.length^J+xs.length+1)+_+_+500
  omega
end ThreeSum.LightTernarySourceHostBudget
