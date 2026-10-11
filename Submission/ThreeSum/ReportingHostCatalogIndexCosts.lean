import Submission.ThreeSum.LightReportingSortedCatalog
import Submission.ThreeSum.LightReportingCatalogLookup

/-!
# The actual sorted index stays within polynomial mask-width overhead

Complete prefix catalogs have at most 2^(2W) records. This bounds both the
merge-sort logarithm and the binary-remainder scratch/time by the mask width,
so lookup contributes no linear factor in the catalog size to a query.
-/

namespace ThreeSum.ReportingHostCatalogIndexCosts

open Light ThreeSum.LightPascal

set_option maxHeartbeats 300000

theorem valueBound_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n ≤ 2^(4*W+1) := by
  have hp : 0 < 2^(2*W) := Nat.two_pow_pos _
  have hn' : n+1 ≤ 2^(2*W+1) := by
    calc
      n+1 ≤ 2^(2*W)+2^(2*W) := by omega
      _ = 2^(2*W+1) := by ring
  calc
    _ ≤ 2^(2*W)*2^(2*W+1) := Nat.mul_le_mul_left _ hn'
    _ = 2^(4*W+1) := by rw [← pow_add]; congr 1; omega

theorem valueBound_add_one_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.valueBound W n+1 ≤ 2^(4*W+2) := by
  have hb := valueBound_le hn
  have hp : 0 < 2^(4*W+1) := Nat.two_pow_pos _
  calc
    _ ≤ 2^(4*W+1)+2^(4*W+1) := by omega
    _ = 2^(4*W+2) := by ring

theorem remainder_log_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    Nat.log 2 (LightReportingCatalogLookup.valueBound W n+1) ≤ 4*W+2 :=
  (Nat.log_le_clog _ _).trans (Nat.clog_le_of_le_pow (valueBound_add_one_le hn))

theorem sort_clog_le {W n : ℕ} (hn : n ≤ 2^(2*W)) : Nat.clog 2 n ≤ 2*W :=
  Nat.clog_le_of_le_pow hn

theorem lookup_time_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingCatalogLookup.time W n ≤ 1000*(W+1) := by
  have hh := remainder_log_le hn
  unfold LightReportingCatalogLookup.time powTableTime LightBandLookup.searchTime
  omega

theorem index_setup_time_le {W n : ℕ} (hn : n ≤ 2^(2*W)) :
    LightReportingSortedCatalog.time W n ≤ 1000*(W+1)*(n+1) := by
  have ht := LightReportingSortedCatalog.time_bound W n
  have hc := sort_clog_le hn
  have hm := Nat.mul_le_mul_left (200*(n+1)) (Nat.add_le_add_right hc 1)
  nlinarith

theorem prefix_lookup_time_le {h J k : ℕ} (hk : k ≤ J) :
    LightReportingCatalogLookup.time (J*(512*h)) (LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(512*h)+1) :=
  lookup_time_le (ReportingHostPackedCatalog.prefix_count_le_pow hk)

theorem prefix_index_setup_time_le {h J k : ℕ} (hk : k ≤ J) :
    LightReportingSortedCatalog.time (J*(512*h)) (LightReportingPrefixCatalog.count h k) ≤
      1000*(J*(512*h)+1)*(LightReportingPrefixCatalog.count h k+1) :=
  index_setup_time_le (ReportingHostPackedCatalog.prefix_count_le_pow hk)

end ThreeSum.ReportingHostCatalogIndexCosts
