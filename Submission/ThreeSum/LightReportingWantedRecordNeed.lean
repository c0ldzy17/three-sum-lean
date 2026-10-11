import Submission.ThreeSum.LightReportingWantedRecord
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedRecord
import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedGuardMass

/-! # The concrete wanted Need runs the original-owner record call -/

namespace ThreeSum.LightReportingWantedRecordNeed

open Light Finset BandRawA BandCandidateRows GlobalEncoding LocalCoverBounds
open RawIncidences RawReporting BlockEncoding BlockForced BlockMaskLayout BlockCoefficientRows
open ReportingHostWantedOriginal ReportingHostWantedControls ReportingHostWantedLayout
open ReportingHostFrontierLayout ReportingHostSourceSelectionStored OutputDecodeRecords
open ReportingHostWantedRecordData SharedReportingBankResourceBounds

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000
set_option linter.unusedSectionVars false

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n U NA NB NC pair bank cover p occ srcB srcC records report output dst counter K old threshold d i : ℕ}
    {rs : List Record} {shift : ℤ}
    (w : Wanted (half n) (blocks n) (AType NA (BandScales.bandSize n) rs))
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC (BandScales.bandSize n) p
      (BlockSourceEncoding.modulus (half n) (blocks n)) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC (BandScales.bandSize n) (half n) (blocks n)
      (LightBlockQuery.sourceCut (half n) (blocks n)) occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover (half n) (blocks n))
    (HQ : SharedReportingBankHeader.Stored μ report (half n) (blocks n) NB NC
      (BandScales.bandSize n) fB fC (p : ℤ) shift)
    (hi : (ownerRecord NA (BandScales.bandSize n) rs w.1.val).b<BandPartition.size NB (BandScales.bandSize n))
    (hj : (ownerRecord NA (BandScales.bandSize n) rs w.1.val).c<BandPartition.size NC (BandScales.bandSize n))
    (houtput : output<localCount (half n)^blocks n)
    (he : w.2.2=LightOutputDecodeOriginal.output (half n) (blocks n) output)
    (hp : 0<p) (hguard : 4*(p : ℤ)≤globalModulus (half n) (blocks n))
    (hK : K≤LightSwitchDepth.depth (blocks n)) (hKJ : K≤blocks n)
    (hkey : globalModulus (half n) (blocks n)∣valueAt NA (BandScales.bandSize n) rs fA w.1.val%(p : ℤ)+
      lift w.2.1*(p : ℤ)+shift-globalKey w.2.2)
    (hselected : Seg μ (access dst (blocks n))
      (record (selected fA NA NB NC (BandScales.bandSize n) pair bank cover (half n) (blocks n)
        occ srcB srcC report rs w output)))
    (hlayout : SegN μ dst (values (LightReportingWantedLayout.layout dst (half n) (blocks n) K
      (items NA (BandScales.bandSize n) rs).length NB NC)))
    (hdecoded : LightWantedDecode.Stored μ (decoded dst)
      (items NA (BandScales.bandSize n) rs).length (half n) (blocks n) i output)
    (hcounter : counter+4≤dst)
    (hcounterRead : μ counter=(old : ℤ)) (hthresholdRead : μ (counter+1)=(threshold : ℤ))
    (hends : WantedSourceEnds
      (LightReportingWantedAccess.selection NA (BandScales.bandSize n) rs w.1.val pair bank cover NB NC
        (half n) (blocks n) (LightBlockQuery.sourceCut (half n) (blocks n)) occ
        (OutputDecodeOccurrenceCode.code (scheduleSize (half n)) (layerCount (half n)) (blocks n) output))
      pair bank cover srcB srcC (ownerRecord NA (BandScales.bandSize n) rs w.1.val).b
      (ownerRecord NA (BandScales.bandSize n) rs w.1.val).c
      (OutputDecodeOccurrenceCode.code (scheduleSize (half n)) (layerCount (half n)) (blocks n) output)
      (half n) (blocks n) (LightBlockQuery.sourceCut (half n) (blocks n)) counter)
    (hrecords : records+4*rs.length≤counter) (hsrcB : srcB+NB≤counter) (hsrcC : srcC+NC≤counter)
    (hbank : SourceBandBankData.finish bank NB NC (BandScales.bandSize n) (half n) (blocks n)
      (LightBlockQuery.sourceCut (half n) (blocks n))≤report)
    (hreport : SharedReportingBankHeader.finish report (half n) (blocks n) NB NC (BandScales.bandSize n)≤counter)
    (hN : (items NA (BandScales.bandSize n) rs).length≤3*(magnitude n)^3)
    (hB : NB≤n) (hC : NC≤n)
    (hold : old≤3*(magnitude n)^7)
    (hmass : rootMass (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w≤3*(magnitude n)^7)
    (hthreshold : threshold≤9*(magnitude n)^8)
    (hreadB : ∀ j<NB, μ (srcB+j)=fB j) (hreadC : ∀ j<NC, μ (srcC+j)=fC j)
    (hvaluesB : ∀ j<NB, |fB j|≤(U : ℤ)) (hvaluesC : ∀ j<NC, |fC j|≤(U : ℤ))
    (hvalue : |fA (BandRawA.labelAt NA (BandScales.bandSize n) rs w.1.val).position|≤(U : ℤ))
    (hok : (wantedNeed n U).Ok lim dst d) :
    let S := selected fA NA NB NC (BandScales.bandSize n) pair bank cover (half n) (blocks n)
      occ srcB srcC report rs w output
    let D := catalogs NA NB NC (BandScales.bandSize n) report (half n) (blocks n) rs w output
    Meets lim LightReportingWantedRecordCall.program 138 d
      [access dst (blocks n),dst,half n,blocks n,K,BlockSourceEncoding.modulus (half n) (blocks n),cover,counter] μ
      (LightReportingWanted.time p shift (left rs fB w) (right rs fC w) S.NL S.NR old threshold
        (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w D K+4000)
      (fun r ν => (r=0 ∨ r=1) ∧
        (r=1 ↔ threshold<old+rootMass
          (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w ∨
          Terminal (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w K) ∧
        ν counter=((old+rootMass
          (localItems (half n) (blocks n) NA NB NC (BandScales.bandSize n) p rs fA fB fC shift w) w : ℕ) : ℤ) ∧
        KeptBut μ ν (packed dst (blocks n)) counter 1) := by
  have hs : counter≤lim.space := by have hh := hok.cells; omega
  have hc : cover+8≤dst := by have hh := hends.coverHeader; omega
  have hav := wanted_integer_word_of_ok hvalue hok
  have hva : |valueAt NA (BandScales.bandSize n) rs fA w.1.val|≤(U : ℤ) := by
    simpa only [valueAt,values_getD fA w.1.isLt] using hvalue
  have hw := wanted_record_values_of_allocation hends w.1.isLt hi hj
    (OutputDecodeOccurrenceCode.source_code_lt (half n) (blocks n) output)
    hrecords hsrcB hsrcC hreport hs hok.space hav
  exact LightReportingWantedRecord.program_meets w HP HB HC HQ hi hj houtput he
    (BandScales.bandSize_pos n) hp hguard hK hKJ hkey hselected hlayout hdecoded
    hcounter hcounterRead hthresholdRead hends hbank hreport
    (wanted_buffers_of_ok hKJ hN hB hC hok)
    (fun k hk => wanted_query_scratch_of_ok hKJ hN hB hC (hk.trans hK) hok)
    hok.space (wanted_record_space_of_ok hKJ hN hB hC hc (by omega) hok) hw
    (wanted_guard_word_of_mass_bound hold hmass hthreshold hok) (wanted_words_of_ok hN hok).1
    hreadB hreadC (fun j hj' => wanted_integer_word_of_ok (hvaluesB j hj') hok)
    (fun j hj' => wanted_integer_word_of_ok (hvaluesC j hj') hok)
    (fun j hj' => wanted_sum_word_of_ok hva (hvaluesB j hj') hok)
    (wanted_count_word_of_ok hB hC hok) (wanted_depth_of_ok hKJ hN hB hC hok)

end ThreeSum.LightReportingWantedRecordNeed
