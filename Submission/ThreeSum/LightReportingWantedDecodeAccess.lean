import Submission.ThreeSum.LightReportingWantedAccess
import Submission.ThreeSum.LightWantedDecode

/-!
# Decode and select one physical wanted slot

The actual emitted pair is decoded before selecting the physical A owner,
both original bands, the retained occurrence sources and the shared catalog
row. The original decoded Q rows survive the selection for mask packing.
-/

namespace ThreeSum.LightReportingWantedDecodeAccess

open Light BandRawA BandCandidateRows BlockSourceEncoding GlobalEncoding
open OutputDecodeRecords
open ReportingHostSourceSelection LightReportingWantedAccess

set_option maxHeartbeats 4000000
set_option maxRecDepth 18000
set_option linter.unusedVariables false

def body (pDecode pAccess : ℕ) : Stmt :=
  .call pDecode [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8] 19 ;;
  .set 20 (M (v 7)) ;;
  .call pAccess [v 9,v 10,v 11,v 20,v 12,v 13,v 14,v 15,v 16,v 19,v 3,v 17,v 18] 0

def libraries : Program := ReportingHostRelocation.program
  LightWantedDecode.program LightReportingWantedAccess.program
def program : Program := libraries ++ [body 4 8]
def time (J V : ℕ) : ℕ := LightWantedDecode.time J V+8300

theorem decoded_of_kept {μ ν : ℕ→ℤ} {dst N h J i j stop : ℕ}
    (H : LightWantedDecode.Stored μ dst N h J i j)
    (hk : Kept μ ν stop) (he : dst+4+J+J≤stop) :
    LightWantedDecode.Stored ν dst N h J i j := by
  refine ⟨?_,?_,?_,?_,⟨?_,?_⟩⟩
  · exact (hk _ (by omega)).trans H.position
  · exact (hk _ (by omega)).trans H.liftIndex
  · exact (hk _ (by omega)).trans H.outputIndex
  · exact (hk _ (by omega)).trans H.bankIndex
  · intro t
    exact (hk _ (by omega)).trans (H.rows.occurrences t)
  · intro t
    exact (hk _ (by omega)).trans (H.rows.masks t)

theorem program_meets_fits {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n g vals owners positions records pair bank cover NB NC p h J cut occ srcB srcC report decoded dst work d : ℕ}
    {pairs slot i j V masks : ℕ} {rs : List Record} {shift : ℤ}
    (HA : BandRawA.Stored μ vals owners positions fA (items n g rs))
    (HR : Seg μ records (cells rs)) (hiRaw : i<3*(items n g rs).length)
    (hjKey : j<OutputDecodeRecords.localCount h^J) (hiV : i≤V) (hjV : j≤V)
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs (i%(items n g rs).length)).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs (i%(items n g rs).length)).c<BandPartition.size NC g)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hvals : vals+(items n g rs).length≤decoded)
    (howners : owners+(items n g rs).length≤decoded)
    (hpositions : positions+(items n g rs).length≤decoded)
    (hrecords : records+4*rs.length≤decoded)
    (hsrcB : srcB+NB≤decoded) (hsrcC : srcC+NC≤decoded)
    (hpair : SourceBandPairData.next pair NB NC g (modulus h J)≤decoded)
    (hbank : SourceBandBankData.finish bank NB NC g h J cut≤decoded)
    (hocc : occ+LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : LightCoverKeyData.keyEnd cover h J≤decoded)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤decoded)
    (hdecoded : decoded+4+J+J≤dst) (hwork : dst+20≤work)
    (hpairs : pairs+2*slot+2≤decoded) (hmasks : masks+layerCount h≤decoded)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s<layerCount h,
      μ (masks+s)=(LocalMaskGraph.maskAt (512*h) (2*h) s : ℤ))
    (hdecoderSpace : LightWantedDecode.space work V≤lim.space)
    (hdecoderWord : (LightWantedDecode.word V (items n g rs).length h J : ℤ)≤lim.word)
    (hspace : Fits
      (selection n g rs (i%(items n g rs).length) pair bank cover NB NC h J cut occ
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j))
      pair bank cover srcB srcC
      (ownerRecord n g rs (i%(items n g rs).length)).b
      (ownerRecord n g rs (i%(items n g rs).length)).c
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j) J (dst+5) lim.space)
    (hvalue : |fA (labelAt n g rs (i%(items n g rs).length)).position|≤lim.word) :
    Meets lim program 9 d
      [pairs,slot,(items n g rs).length,J,scheduleSize h,layerCount h,masks,decoded,work,
        vals,owners,records,pair,bank,cover,srcB,srcC,report,dst]
      μ (time J V)
      (fun result ν => result=(dst : ℤ) ∧
        LightWantedDecode.Stored ν decoded (items n g rs).length h J i j ∧
        Seg ν dst (record fA n g rs (i%(items n g rs).length) pair bank cover NB NC h J cut occ
          (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j) srcB srcC report) ∧
        Kept μ ν decoded) := by
  have hn : 0<(items n g rs).length := by omega
  let idx := i%(items n g rs).length
  let code := OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j
  have hidx : idx<(items n g rs).length := Nat.mod_lt _ hn
  have hk : code<LightBlockSourceCatalog.count h J :=
    OutputDecodeOccurrenceCode.code_lt (schedule_pos h) (layerCount_pos h) J j
  have hdst : decoded≤dst := by omega
  have hout : dst+20≤lim.space := by have hh := hspace.output; omega
  apply Meets.of_body (p := 9) (by rfl : program[9]?=some (body 4 8))
  unfold body time
  have hdecode := (LightWantedDecode.program_meets (d := d+1) (N := (items n g rs).length)
    hw (by omega) hn hiV hjV hjKey hpairs hmasks (by omega)
    hdecoderSpace hdecoderWord hleft hright hread).append
    (LightReportingWantedAccess.program.map (ReportingHostRelocation.relocate 5) ++ [body 4 8])
  change Meets lim program 4 (d+1) _ μ _ _ at hdecode
  light_call hdecode with bankCode μ₁ ⟨hcode,hdecoded₁,hkeep₁⟩
  have hposition : μ₁ decoded=(idx : ℤ) := hdecoded₁.position
  light_set (idx : ℕ) using hposition
  have HA₁ := HA.of_kept hkeep₁ hvals howners hpositions
  have HR₁ := HR.of_kept hkeep₁ (by simpa only [cells_length] using hrecords)
  have HP₁ := HP.of_kept (modulus_pos h J) hkeep₁ hpair
  have HB₁ := HB.of_kept hkeep₁ hocc hbank
  have HC₁ := HC.of_kept (fun a ha => hkeep₁ a (ha.trans_le hcover))
  have HQ₁ := HQ.of_kept hkeep₁ hreport
  have haccess := LightReportingWantedAccess.program_meets_fits (μ := μ₁) (d := d+1) (dst := dst)
    HA₁ HR₁ hidx HP₁ HB₁ HC₁ HQ₁ hi hj hk hw (by omega)
    (hvals.trans hdst) (howners.trans hdst) (hrecords.trans hdst)
    (hsrcB.trans hdst) (hsrcC.trans hdst) (hpair.trans hdst) (hbank.trans hdst) hocc
    (hcover.trans hdst) (hreport.trans hdst) hspace hvalue
  have haccessRun := (ReportingHostRelocation.meets haccess LightWantedDecode.program).append [body 4 8]
  change Meets lim program 8 (d+1) _ μ₁ 8100 _ at haccessRun
  have hcode' : bankCode=(code : ℤ) := hcode
  light_call haccessRun using hcode' with result ν ⟨hresult,hselected,hkeep₂⟩
  exact ⟨hresult,decoded_of_kept hdecoded₁ hkeep₂ hdecoded,hselected,
    fun a ha => (hkeep₂ a (ha.trans_le hdst)).trans (hkeep₁ a ha)⟩

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n g vals owners positions records pair bank cover NB NC p h J cut occ srcB srcC report decoded dst work d : ℕ}
    {pairs slot i j V masks : ℕ} {rs : List Record} {shift : ℤ}
    (HA : BandRawA.Stored μ vals owners positions fA (items n g rs))
    (HR : Seg μ records (cells rs)) (hiRaw : i<3*(items n g rs).length)
    (hjKey : j<OutputDecodeRecords.localCount h^J) (hiV : i≤V) (hjV : j≤V)
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs (i%(items n g rs).length)).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs (i%(items n g rs).length)).c<BandPartition.size NC g)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d+4<lim.depth)
    (hvals : vals+(items n g rs).length≤decoded)
    (howners : owners+(items n g rs).length≤decoded)
    (hpositions : positions+(items n g rs).length≤decoded)
    (hrecords : records+4*rs.length≤decoded)
    (hsrcB : srcB+NB≤decoded) (hsrcC : srcC+NC≤decoded)
    (hpair : SourceBandPairData.next pair NB NC g (modulus h J)≤decoded)
    (hbank : SourceBandBankData.finish bank NB NC g h J cut≤decoded)
    (hocc : occ+LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : LightCoverKeyData.keyEnd cover h J≤decoded)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤decoded)
    (hdecoded : decoded+4+J+J≤dst) (hwork : dst+20≤work)
    (hpairs : pairs+2*slot+2≤decoded) (hmasks : masks+layerCount h≤decoded)
    (hleft : μ (pairs+2*slot)=(i : ℤ)) (hright : μ (pairs+2*slot+1)=(j : ℤ))
    (hread : ∀ s<layerCount h,
      μ (masks+s)=(LocalMaskGraph.maskAt (512*h) (2*h) s : ℤ))
    (hdecoderSpace : LightWantedDecode.space work V≤lim.space)
    (hdecoderWord : (LightWantedDecode.word V (items n g rs).length h J : ℤ)≤lim.word)
    (hspace : space
      (selection n g rs (i%(items n g rs).length) pair bank cover NB NC h J cut occ
        (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j))
      pair bank cover srcB srcC
      (ownerRecord n g rs (i%(items n g rs).length)).b
      (ownerRecord n g rs (i%(items n g rs).length)).c
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j) J (dst+5)≤lim.space)
    (hvalue : |fA (labelAt n g rs (i%(items n g rs).length)).position|≤lim.word) :
    Meets lim program 9 d
      [pairs,slot,(items n g rs).length,J,scheduleSize h,layerCount h,masks,decoded,work,
        vals,owners,records,pair,bank,cover,srcB,srcC,report,dst]
      μ (time J V)
      (fun result ν => result=(dst : ℤ) ∧
        LightWantedDecode.Stored ν decoded (items n g rs).length h J i j ∧
        Seg ν dst (record fA n g rs (i%(items n g rs).length) pair bank cover NB NC h J cut occ
          (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J j) srcB srcC report) ∧
        Kept μ ν decoded) :=
  program_meets_fits HA HR hiRaw hjKey hiV hjV HP HB HC HQ hi hj hw hd
    hvals howners hpositions hrecords hsrcB hsrcC hpair hbank hocc hcover hreport
    hdecoded hwork hpairs hmasks hleft hright hread hdecoderSpace hdecoderWord
    (fits_of_space _ _ _ _ _ _ _ _ _ _ _ _ hspace) hvalue

end ThreeSum.LightReportingWantedDecodeAccess
