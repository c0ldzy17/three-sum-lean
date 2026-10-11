import Submission.ThreeSum.EncodedColorWantedConsumerData

/-!
# All persistent wanted-consumer inputs precede the mutable counter

The bounds use the actual packed source and wanted extents. In particular,
the pair-array endpoint is the source-control base, and the occurrence rows
end exactly at the shared source-bank header.
-/

namespace ThreeSum.EncodedColorWantedConsumerData

open Light Scales BandScales EncodedColorNormalizedData ThreeSumWantedHostData

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

structure PersistentEnds (cfg : LightReportingWantedDispatch.Config)
    (positions occ g cut rowCount wantedCount : ℕ) : Prop where
  values : cfg.vals+cfg.N≤cfg.counter
  owners : cfg.owners+cfg.N≤cfg.counter
  positions : positions+cfg.N≤cfg.counter
  records : cfg.records+4*rowCount≤cfg.counter
  srcB : cfg.srcB+cfg.NB≤cfg.counter
  srcC : cfg.srcC+cfg.NC≤cfg.counter
  pair : SourceBandPairData.next cfg.pair cfg.NB cfg.NC g
    (BlockSourceEncoding.modulus cfg.h cfg.J)≤cfg.counter
  bank : SourceBandBankData.finish cfg.bank cfg.NB cfg.NC g cfg.h cfg.J cut≤cfg.report
  occurrence : occ+LightBlockSourceCatalog.count cfg.h cfg.J*cfg.J≤cfg.bank
  cover : LightCoverKeyData.keyEnd cfg.cover cfg.h cfg.J≤cfg.counter
  report : SharedReportingBankHeader.finish cfg.report cfg.h cfg.J cfg.NB cfg.NC g≤cfg.counter
  pairs : cfg.pairs+2*wantedCount≤cfg.counter
  masks : cfg.masks+cfg.layerCount≤cfg.counter
  reportBeforeCounter : cfg.report+9≤cfg.counter

variable {μ : ℕ→ℤ} {free n : ℕ}
  {color : Coloring.Parameter (inputBits n+1)} {x : Fin n→ℤ} {A B C : List ℤ}
  {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}

theorem normalized_ends (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    let cfg := config free n A B C hsA hsB hsC
    cfg.vals+cfg.N≤cfg.cover ∧ cfg.owners+cfg.N≤cfg.cover ∧
      positions free n A B C hsA hsB hsC+cfg.N≤cfg.cover ∧
      cfg.records+4*recordCount n A B C hsA hsB hsC≤cfg.cover ∧
      cfg.srcB+cfg.NB≤cfg.cover ∧ cfg.srcC+cfg.NC≤cfg.cover := by
  let cfg := config free n A B C hsA hsB hsC
  have hN := incidence_length_le_records free n A B C hsA hsB hsC
  have hR := record_count_le H
  obtain ⟨_,hB,hC⟩ := ThreeSumColorBudgets.normalized_lengths H
  have hmul := Nat.mul_le_mul_left (bandSize n) hR
  obtain ⟨_,_,hsrcB,_,hsrcC,_,_,hrecords,hspace⟩ :=
    EncodedColorLayout.normalized_ends_cover free n (bandSize n) (radix n) (primeWindow n)
  have howner : cfg.owners=cfg.vals+bandSize n*recordCount n A B C hsA hsB hsC := rfl
  have hpos : positions free n A B C hsA hsB hsC=
      cfg.vals+bandSize n*recordCount n A B C hsA hsB hsC+
        bandSize n*recordCount n A B C hsA hsB hsC := rfl
  change cfg.N≤bandSize n*recordCount n A B C hsA hsB hsC at hN
  change cfg.NB≤n at hB
  change cfg.NC≤n at hC
  change cfg.srcB+n≤cfg.cover at hsrcB
  change cfg.srcC+n≤cfg.cover at hsrcC
  change cfg.records+4*ColorBandBounds.count n (bandSize n)≤cfg.cover at hrecords
  change cfg.vals+bandSize n*ColorBandBounds.count n (bandSize n)+
    bandSize n*ColorBandBounds.count n (bandSize n)+
    bandSize n*ColorBandBounds.count n (bandSize n)≤cfg.cover at hspace
  change cfg.vals+cfg.N≤cfg.cover ∧ cfg.owners+cfg.N≤cfg.cover ∧
    positions free n A B C hsA hsB hsC+cfg.N≤cfg.cover ∧
    cfg.records+4*recordCount n A B C hsA hsB hsC≤cfg.cover ∧
    cfg.srcB+cfg.NB≤cfg.cover ∧ cfg.srcC+cfg.NC≤cfg.cover
  omega

theorem pairs_end_eq_controls (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    (config free n A B C hsA hsB hsC).pairs+2*ThreeSumWantedHostData.count n A B C hsA hsB hsC=
      EncodedColorPipelineData.controls free n A B C hsA hsB hsC := rfl

theorem occurrence_end_eq_bank (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    occurrence free n A B C hsA hsB hsC+
      LightBlockSourceCatalog.count (config free n A B C hsA hsB hsC).h
        (config free n A B C hsA hsB hsC).J*(config free n A B C hsA hsB hsC).J=
      (config free n A B C hsA hsB hsC).bank := rfl

theorem bank_end_add_eight_eq_report (free n : ℕ) (A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) :
    let cfg := config free n A B C hsA hsB hsC
    SourceBandBankData.finish cfg.bank cfg.NB cfg.NC (bandSize n) cfg.h cfg.J (mu n)+8=cfg.report := rfl

theorem persistent_ends (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    PersistentEnds (config free n A B C hsA hsB hsC)
      (positions free n A B C hsA hsB hsC) (occurrence free n A B C hsA hsB hsC)
      (bandSize n) (mu n) (recordCount n A B C hsA hsB hsC)
      (ThreeSumWantedHostData.count n A B C hsA hsB hsC) := by
  let cfg := config free n A B C hsA hsB hsC
  have hbefore : cfg.report+9≤cfg.counter := ThreeSumReportingSetupData.report_le_counter ..
  have hcover : cfg.cover≤cfg.report := (ThreeSumReportingSetupData.prefix_le_report free n A B C hsA hsB hsC).2
  obtain ⟨hvals,howners,hpositions,hrecords,hsrcB,hsrcC⟩ := normalized_ends H
  have hsource := SourceFiniteData.source_ends (EncodedColorPipelineData.controls free n A B C hsA hsB hsC)
    B.length C.length (bandSize n) (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n)
  have hbank := bank_end_add_eight_eq_report free n A B C hsA hsB hsC
  have hpair : SourceBandPairData.next cfg.pair cfg.NB cfg.NC (bandSize n)
      (BlockSourceEncoding.modulus cfg.h cfg.J)≤
      SourceBandBankData.finish cfg.bank cfg.NB cfg.NC (bandSize n) cfg.h cfg.J (mu n) := hsource.2.1
  have hkey : LightCoverKeyData.keyEnd cfg.cover cfg.h cfg.J≤cfg.report :=
    ThreeSumReportingSetupData.cover_end_le_report ..
  have hpairs := pairs_end_eq_controls free n A B C hsA hsB hsC
  have hcontrols : EncodedColorPipelineData.controls free n A B C hsA hsB hsC+3≤
      SourceBandBankData.finish cfg.bank cfg.NB cfg.NC (bandSize n) cfg.h cfg.J (mu n) := hsource.1
  have hmask : cfg.masks+cfg.layerCount≤LightCoverKeys.keyHeader cfg.cover cfg.h cfg.J :=
    LightCoverKeyData.layer_end_le_header ..
  have hmaskKey : LightCoverKeys.keyHeader cfg.cover cfg.h cfg.J≤LightCoverKeyData.keyEnd cfg.cover cfg.h cfg.J := by
    unfold LightCoverKeyData.keyEnd
    omega
  have hreport : SharedReportingBankHeader.finish cfg.report cfg.h cfg.J cfg.NB cfg.NC (bandSize n)=cfg.counter := rfl
  change SourceBandBankData.finish cfg.bank cfg.NB cfg.NC (bandSize n) cfg.h cfg.J (mu n)+8=cfg.report at hbank
  have hreportCounter : cfg.report≤cfg.counter := by omega
  have hcoverCounter : cfg.cover≤cfg.counter := hcover.trans hreportCounter
  have hbankReport : SourceBandBankData.finish cfg.bank cfg.NB cfg.NC (bandSize n) cfg.h cfg.J (mu n)≤cfg.report := by omega
  have hpairsReport : cfg.pairs+2*ThreeSumWantedHostData.count n A B C hsA hsB hsC≤cfg.report := by
    change cfg.pairs+2*ThreeSumWantedHostData.count n A B C hsA hsB hsC=
      EncodedColorPipelineData.controls free n A B C hsA hsB hsC at hpairs
    omega
  exact ⟨hvals.trans hcoverCounter,howners.trans hcoverCounter,hpositions.trans hcoverCounter,
    hrecords.trans hcoverCounter,hsrcB.trans hcoverCounter,hsrcC.trans hcoverCounter,
    hpair.trans (hbankReport.trans hreportCounter),hbankReport,(occurrence_end_eq_bank ..).le,
    hkey.trans hreportCounter,hreport.le,hpairsReport.trans hreportCounter,
    hmask.trans (hmaskKey.trans (hkey.trans hreportCounter)),hbefore⟩

theorem masks_read (H : EncodedColorPipelineData.Stored μ free n color x A B C hsA hsB hsC) :
    ∀ j<(config free n A B C hsA hsB hsC).layerCount,
      μ ((config free n A B C hsA hsB hsC).masks+j)=
        (LocalMaskGraph.maskAt (512*(config free n A B C hsA hsB hsC).h)
          (2*(config free n A B C hsA hsB hsC).h) j : ℤ) := H.cover.masks

end ThreeSum.EncodedColorWantedConsumerData
