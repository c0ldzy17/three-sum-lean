import Submission.ThreeSum.LightReportingSuffixCatalogSetup
import Submission.ThreeSum.ReportingHostPrefixCatalog
import Submission.ThreeSum.ReportingHostSuffixCosts
import Submission.ThreeSum.CostLedger

/-!
# Charging the actual shared suffix catalog to the original finite ledger

The bound uses the exact physically constructed local table size and the
proved full prefix-key cardinality. Physical enumeration and lookup of those
prefix keys remain separate executable components.
-/

namespace ThreeSum.ReportingHostCatalogCosts

set_option maxRecDepth 8000

open ThreeSum.SubsetAddress ThreeSum.LightBlockQuery ThreeSum.BlockIndexedQuery
open ReportingHostPrefixCatalog ReportingHostSuffixCosts

theorem prefix_card_pos (h k : ℕ) : 0 < Fintype.card (Prefix h k) := by
  rw [prefix_card]
  exact Nat.pow_pos (Nat.mul_pos (Nat.choose_pos (by omega)) (Nat.choose_pos (by omega)))

theorem catalog_time_le_layer {W V offset cut n : ℕ} (hfit : offset+V ≤ W)
    (hhalf : cut ≤ V/2) (hn : 0 < n) :
    LightReportingSuffixCatalogSetup.time W V cut offset n ≤
      100000*(W+1)^5*n*V.choose cut := by
  have hcut : cut ≤ V := hhalf.trans (Nat.div_le_self _ _)
  have ht := LightReportingSuffixCatalogSetup.time_bound (n := n) hfit hcut
  have hc := downsetCap_add_one_le_layer hhalf
  have hv : V+2 ≤ 2*(W+1) := by omega
  have hn' : n+1 ≤ 2*n := by omega
  calc
    _ ≤ 23000*(W+1)^4*((V+2)*V.choose cut)*(n+1) :=
      ht.trans (Nat.mul_le_mul_right (n+1) (Nat.mul_le_mul_left (23000*(W+1)^4) hc))
    _ ≤ 23000*(W+1)^4*((2*(W+1))*V.choose cut)*(2*n) :=
      Nat.mul_le_mul (Nat.mul_le_mul_left (23000*(W+1)^4) (Nat.mul_le_mul_right _ hv)) hn'
    _ = 92000*(W+1)^5*n*V.choose cut := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by decide)))

theorem block_catalog_time_le_layer {h J k cut : ℕ} (hk : k ≤ J)
    (hcut : cut ≤ residualSize h J k) :
    LightReportingSuffixCatalogSetup.time (width h J) (suffixStage J (512*h) k) cut (k*(512*h))
      (Fintype.card (Prefix h k)) ≤
      100000*(width h J+1)^5*(((512*h).choose (2*h)*(2*h).choose h)^k)*
        (256*residualSize h J k).choose cut := by
  have hhalf : cut ≤ suffixStage J (512*h) k/2 := by
    rw [suffix_width_eq]
    omega
  calc
    _ ≤ 100000*(width h J+1)^5*(Fintype.card (Prefix h k))*
        (suffixStage J (512*h) k).choose cut :=
      catalog_time_le_layer (W := width h J) (V := suffixStage J (512*h) k)
        (offset := k*(512*h)) (ReportingHostSuffix.block_fit hk) hhalf (prefix_card_pos h k)
    _ = _ := by rw [prefix_card,suffix_width_eq]

theorem prefix_card_eq_ledger {n h k : ℕ} (hsize : 2*h = Scales.muZero n) :
    Fintype.card (Prefix h k) = CostLedger.prefixChoices n k := by
  have hhalf : Scales.muZero n/2 = h := by omega
  have hwidth : 512*h = 256*Scales.muZero n := by omega
  rw [prefix_card,CostLedger.prefixChoices,CostLedger.microOutputs,CostLedger.microPartitions,
    hwidth,hsize,hhalf]

theorem catalog_time_le_prefixBoxes {n h J k : ℕ}
    (hsize : 2*h = Scales.muZero n) (hblocks : J = Scales.blockCount (Scales.inputBits n))
    (hk : k ≤ J) :
    LightReportingSuffixCatalogSetup.time (width h J) (suffixStage J (512*h) k)
      (Switch.residualSize n k-Switch.actualSwitch n k) (k*(512*h))
      (Fintype.card (Prefix h k)) ≤ 100000*(width h J+1)^5*CostLedger.prefixBoxes n k := by
  have hres : residualSize h J k = Switch.residualSize n k := by
    simp only [residualSize,Switch.residualSize,hsize,hblocks]
  have hcount : (((512*h).choose (2*h)*(2*h).choose h)^k) = CostLedger.prefixChoices n k :=
    (prefix_card h k).symm.trans (prefix_card_eq_ledger hsize)
  have hcut : Switch.residualSize n k-Switch.actualSwitch n k ≤ residualSize h J k := by
    rw [hres]
    exact Nat.sub_le _ _
  have ht := block_catalog_time_le_layer hk hcut
  calc
    _ ≤ 100000*(width h J+1)^5*(((512*h).choose (2*h)*(2*h).choose h)^k)*
        (256*residualSize h J k).choose (Switch.residualSize n k-Switch.actualSwitch n k) := ht
    _ = _ := by rw [hcount,hres]; simp only [CostLedger.prefixBoxes,CostLedger.suffixBoxes,Nat.mul_assoc]

theorem actual_catalog_time_le_prefixBoxes {n k : ℕ}
    (hk : k ≤ Scales.blockCount (Scales.inputBits n)) :
    LightReportingSuffixCatalogSetup.time
      (width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n)))
      (suffixStage (Scales.blockCount (Scales.inputBits n))
        (512*Scales.microHalf (Scales.inputBits n)) k)
      (Switch.residualSize n k-Switch.actualSwitch n k)
      (k*(512*Scales.microHalf (Scales.inputBits n)))
      (Fintype.card (Prefix (Scales.microHalf (Scales.inputBits n)) k)) ≤
      100000*(width (Scales.microHalf (Scales.inputBits n)) (Scales.blockCount (Scales.inputBits n))+1)^5*
        CostLedger.prefixBoxes n k :=
  catalog_time_le_prefixBoxes rfl rfl hk

end ThreeSum.ReportingHostCatalogCosts
