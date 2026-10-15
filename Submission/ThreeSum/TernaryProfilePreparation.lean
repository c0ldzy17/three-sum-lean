import Submission.ThreeSum.TernaryConcreteProfile
import Submission.ThreeSum.TernaryGlobalReceiptTransport
import Submission.ThreeSum.TernaryColoredPreparationCall

noncomputable section
namespace ThreeSum.TernaryProfilePreparation
open Light TernaryConcreteProfile LightTernaryFastProgramProof
open TernaryLocalParameters TernaryCanonicalDictionaries
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def menu (P : Profile κ) (n free : ℕ) : ℕ :=
  LightExtensionBackendLayout.physical (LightTernaryGlobalPrelude.backend free)
    (LightTernaryDimensions.dim P.M P.radix P.p P.K n (n^κ))
    (P.p^(LightTernaryDimensions.dim P.M P.radix P.p P.K n (n^κ)))
    (LightTernaryDimensions.J P.M P.radix n (n^κ))

/-- The executed global prelude and the actual coloring frame furnish all
preprocessing reads, including the source segment and the found field menu. -/
theorem meets {lim : Limits} {n free src c depth i : ℕ}
    (P : Profile κ) (x : Fin n→ℤ) (μ ν₀ ν : ℕ→ℤ)
    (hi : i<ColorParameters.count (LightColorParametersCosts.width n))
    (hn : 0<n) (hsrc : src+n≤free)
    (H : Receipt P.M P.radix P.p P.K κ n free c μ ν₀)
    (hkeep : Kept ν₀ ν (scanFree P.M P.radix P.p P.K κ n free))
    (hfields : Seg ν (scanFree P.M P.radix P.p P.K κ n free)
      (ColorParameters.fields (ColorParameters.parameter hi)))
    (hneed : (P.colorNeed n (n^κ)).Ok lim
      (scanFree P.M P.radix P.p P.K κ n free+6) depth)
    (hinput : Seg μ src (List.ofFn x)) (hbound : ∀i,|x i|≤((n^κ:ℕ):ℤ)) :
    Meets lim P.color 50 (depth+1)
      [src,n,LightTernaryGlobalPrelude.params free,scanFree P.M P.radix P.p P.K κ n free,
        scanFree P.M P.radix P.p P.K κ n free+6] ν
      (LightTernaryColorPreparationProof.time n (LightTernaryDimensions.J P.M P.radix n (n^κ)) (n^κ))
      (fun ret ξ=>LightTernaryColorPreparationProof.Output ν ξ
        (scanFree P.M P.radix P.p P.K κ n free+6) (n^κ) (LightTernaryDimensions.r P.M n)
        (LightTernaryDimensions.J P.M P.radix n (n^κ))
        (P.p^(LightTernaryDimensions.dim P.M P.radix P.p P.K n (n^κ)))
        (menu P n free) P.radix (ColorParameters.parameter hi) x ret) := by
  have HH := TernaryGlobalReceiptTransport.receipt_keep H hkeep
  have hr := TernaryGlobalReceiptTransport.preparation_reads HH
  dsimp only at hr
  have hfree : free≤scanFree P.M P.radix P.p P.K κ n free := by
    unfold scanFree LightTernaryGlobalPrelude.finish LightTernaryGlobalPrelude.backend
    omega
  have hread : Seg ν src (List.ofFn x) :=
    hinput.of_kept HH.2.2.2.2 (by simpa only [List.length_ofFn] using hsrc)
  exact TernaryColoredPreparationCall.meets P.allocation ν (ColorParameters.parameter hi) x
    ((TernaryExecutable.leftRecords P.maps P.cap).map (native false P.maps))
    ((TernaryExecutable.leftRecords P.maps P.cap).map wordCode)
    ((TernaryExecutable.leftRecords P.maps P.cap).map mapCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map (native true P.maps))
    ((TernaryExecutable.rightRecords P.maps P.cap).map wordCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map mapCode)
    (TernaryGoodOutputCatalog.raws P.maps P.threshold)
    (TernaryGoodOutputCatalog.wordCodes P.maps P.threshold)
    (TernaryGoodOutputCatalog.mapCodes P.maps P.threshold)
    P.radix (P.p^(2*P.K)) P.drift P.scale (4^fixedLength P.m)
    (fixedAlpha P.m 2) (TernaryArenaSourceSetup.alphaRank P.m)
    (TernaryCodeSemantics.address P.output.val) (fixedLength P.m)
    (TernaryExecutable.reportingMain (p:=P.p) P.K) (TernaryExecutable.reporting P.maps P.cap P.K)
    hn P.radix_gt_one hneed ((hsrc.trans hfree).trans (Nat.le_add_right _ 6))
    hr.2.1 hr.1 (le_refl _) hr.2.2.1
    hr.2.2.2.1 hr.2.2.2.2.1 hr.2.2.2.2.2.1 hr.2.2.2.2.2.2.1 hr.2.2.2.2.2.2.2.1
    hr.2.2.2.2.2.2.2.2 hfields hread hbound

end ThreeSum.TernaryProfilePreparation
