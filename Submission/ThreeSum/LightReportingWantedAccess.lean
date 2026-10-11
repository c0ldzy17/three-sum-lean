import Submission.ThreeSum.LightReportingOwnerSelect
import Submission.ThreeSum.ReportingHostSourceSelectionStored
import Submission.ThreeSum.LightSharedReportingLookup
import Submission.ThreeSum.ReportingHostRelocation

/-!
# Actual owner, independent sources and shared reporting-row access

A physical A incidence selects its owner and original value. The owner
selects both original bands, the decoded occurrence selects their retained
source families, and one constant-time lookup selects the shared catalog
row. The resulting twenty-cell record is ready for the guarded reporter.
-/

namespace ThreeSum.LightReportingWantedAccess

open Light BandRawA BandCandidateRows BlockSourceEncoding
open ReportingHostSourceSelection ReportingHostSourceSelectionStored

set_option maxHeartbeats 3300000
set_option maxRecDepth 15000
set_option linter.unusedVariables false

def selection (n g : ℕ) (rs : List Record) (idx pair bank cover NB NC h J cut occ code : ℕ) : Pointers :=
  retained pair bank cover NB NC g h J cut occ
    (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c code

def catalog (n g : ℕ) (rs : List Record) (idx report J NB NC code : ℕ) : ℕ :=
  SharedReportingBankAccess.recordAt report J NB NC g code
    (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c

def record (f : ℕ→ℤ) (n g : ℕ) (rs : List Record)
    (idx pair bank cover NB NC h J cut occ code srcB srcC report : ℕ) : List ℤ :=
  LightReportingOwnerSelect.row f n g rs idx ++
    (catalog n g rs idx report J NB NC code : ℤ)::
      (ReportingHostSourceSelection.values (selection n g rs idx pair bank cover NB NC h J cut occ code)
        srcB srcC code J).map (fun t => (t : ℤ))

/-- Packed A values and owner labels, owner records, incidence, source pair,
source banks, cover, original B/C, occurrence code, J, reporting banks, dst. -/
def body (pOwner pSource pLookup : ℕ) : Stmt :=
  .call pOwner [v 0,v 1,v 2,v 3,v 12] 13 ;;
  .set 14 (M (v 12 +' k 2)) ;;
  .set 15 (M (v 12 +' k 3)) ;;
  .set 16 (v 12 +' k 5) ;;
  .call pSource [v 4,v 5,v 6,v 7,v 8,v 14,v 15,v 9,v 10,v 16] 17 ;;
  .call pLookup [v 11,v 9,v 14,v 15] 18 ;;
  .store (v 12 +' k 4) (v 18) ;;
  .set 0 (v 12)

def initialLibraries : Program := ReportingHostRelocation.program
  LightReportingOwnerSelect.program LightReportingSourceSelect.program
def libraries : Program := ReportingHostRelocation.program initialLibraries LightSharedReportingLookup.program
def program : Program := libraries ++ [body 0 1 2]

theorem program_meets_fits {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n g vals owners positions records idx pair bank cover NB NC p h J cut occ code srcB srcC report dst d : ℕ}
    {rs : List Record} {shift : ℤ}
    (HA : BandRawA.Stored μ vals owners positions fA (items n g rs))
    (HR : Seg μ records (cells rs)) (hidx : idx<(items n g rs).length)
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs idx).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs idx).c<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hvals : vals+(items n g rs).length≤dst) (howners : owners+(items n g rs).length≤dst)
    (hrecords : records+4*rs.length≤dst) (hsrcB : srcB+NB≤dst) (hsrcC : srcC+NC≤dst)
    (hpair : SourceBandPairData.next pair NB NC g (modulus h J)≤dst)
    (hbank : SourceBandBankData.finish bank NB NC g h J cut≤dst)
    (hocc : occ+LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : LightCoverKeyData.keyEnd cover h J≤dst)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤dst)
    (hspace : Fits (selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c code J (dst+5) lim.space)
    (hvalue : |fA (labelAt n g rs idx).position|≤lim.word) :
    Meets lim program 3 d [vals,owners,records,idx,pair,bank,cover,srcB,srcC,code,J,report,dst] μ 8100
      (fun result ν => result=(dst : ℤ) ∧
        Seg ν dst (record fA n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report) ∧
        Kept μ ν dst) := by
  let i := (ownerRecord n g rs idx).b
  let j := (ownerRecord n g rs idx).c
  let X := selection n g rs idx pair bank cover NB NC h J cut occ code
  let cat := catalog n g rs idx report J NB NC code
  have hout : dst+20≤lim.space := by have hh := hspace.output; omega
  have hiSpace : i≤lim.space := by have hh:=hi.trans_le (BandPartition.size_le NB g); omega
  have hjSpace : j≤lim.space := by have hh:=hj.trans_le (BandPartition.size_le NC g); omega
  have hcatSpace : cat≤lim.space := by
    have he := SharedReportingBankAccess.record_end (free := report) (J := J) hk hi hj
    have hf := SharedReportingBankHeader.payload_le_finish report h J NB NC g
    dsimp only [cat,catalog]
    omega
  apply Meets.of_body (p := 3) (by rfl : program[3]?=some (body 0 1 2))
  unfold body
  have howner := (LightReportingOwnerSelect.program_meets (μ := μ) (d := d+1) (dst := dst)
    HA HR hidx hw (by omega) (by omega) (by omega) (by omega) hvalue hiSpace hjSpace).append
      (LightReportingSourceSelect.program.map (ReportingHostRelocation.relocate 1) ++
        LightSharedReportingLookup.program.map (ReportingHostRelocation.relocate 2) ++ [body 0 1 2])
  change Meets lim program 0 (d+1) _ μ 700 _ at howner
  light_call howner with unused μ₁ ⟨_,hrow,hkeepOwner⟩
  have hkeep₁ : Kept μ μ₁ dst := fun a ha => hkeepOwner a (Or.inl ha)
  have hreadB : μ₁ (dst+2)=(i : ℤ) := by
    simpa only [LightReportingOwnerSelect.row,List.getD_cons_succ,List.getD_cons_zero]
      using hrow.getD (i := 2) (by simp [LightReportingOwnerSelect.row]) 0
  have hreadC : μ₁ (dst+3)=(j : ℤ) := by
    simpa only [LightReportingOwnerSelect.row,List.getD_cons_succ,List.getD_cons_zero]
      using hrow.getD (i := 3) (by simp [LightReportingOwnerSelect.row]) 0
  have hreadBZ : μ₁ (((dst : ℤ)+2).toNat)=(i : ℤ) := by
    rw [show ((dst : ℤ)+2).toNat=dst+2 by omega]; exact hreadB
  have hreadCZ : μ₁ (((dst : ℤ)+3).toNat)=(j : ℤ) := by
    rw [show ((dst : ℤ)+3).toNat=dst+3 by omega]; exact hreadC
  light_set (i : ℕ) using hreadB,hreadBZ
  light_set (j : ℕ) using hreadC,hreadCZ
  light_set (dst+5 : ℕ)
  have HP₁ := HP.of_kept (modulus_pos h J) hkeep₁ hpair
  have HB₁ := HB.of_kept hkeep₁ hocc hbank
  have HC₁ := HC.of_kept (fun a ha => hkeep₁ a (ha.trans_le hcover))
  have hsource := ReportingHostSourceSelectionStored.program_meets_fits (μ := μ₁) (d := d+1) (dst := dst+5)
    (srcB := srcB) (srcC := srcC) HP₁ HB₁ HC₁ hi hj hk hw hspace
  have hsourceRun := (ReportingHostRelocation.meets hsource LightReportingOwnerSelect.program).append
    (LightSharedReportingLookup.program.map (ReportingHostRelocation.relocate 2) ++ [body 0 1 2])
  change Meets lim program 1 (d+1) _ μ₁ 6000 _ at hsourceRun
  light_call hsourceRun with unused μ₂ ⟨_,hselected,hkeepSource⟩
  have hkeep₂ : Kept μ₁ μ₂ (dst+5) := fun a ha => hkeepSource a (Or.inl ha)
  have hkeep : Kept μ μ₂ dst := fun a ha => (hkeep₂ a (by omega)).trans (hkeep₁ a ha)
  have HQ₂ := HQ.of_kept hkeep hreport
  have hlookup := LightSharedReportingLookup.program_meets (d := d+1) HQ₂ hk hi hj hw (by omega)
  have hlookupRun := (ReportingHostRelocation.meets hlookup initialLibraries).append [body 0 1 2]
  change Meets lim program 2 (d+1) _ μ₂ 500 _ at hlookupRun
  light_call hlookupRun with catalogResult μ₃ ⟨hcat,hmem⟩
  subst μ₃
  change catalogResult=(cat : ℤ) at hcat
  light_store (dst+4) (cat : ℕ) using hcat
  light_set (dst : ℕ)
  refine ⟨rfl,?_,?_⟩
  · change Seg (Function.update μ₂ (dst+4) (cat : ℤ)) dst
      (LightReportingOwnerSelect.row fA n g rs idx ++ (cat : ℤ)::
        (ReportingHostSourceSelection.values X srcB srcC code J).map (fun t => (t : ℤ)))
    apply seg_append.mpr
    constructor
    · apply (hrow.of_kept hkeep₂ (by simp [LightReportingOwnerSelect.row])).update_out
        (Or.inr (by simp [LightReportingOwnerSelect.row]))
    · change Seg (Function.update μ₂ (dst+4) (cat : ℤ)) (dst+4)
        ((cat : ℤ)::(ReportingHostSourceSelection.values X srcB srcC code J).map (fun t => (t : ℤ)))
      apply seg_cons.mpr
      refine ⟨by simp,?_⟩
      change SegN (Function.update μ₂ (dst+4) (cat : ℤ)) (dst+5)
        (ReportingHostSourceSelection.values X srcB srcC code J)
      exact hselected.update_out (Or.inl (by omega)) _
  · intro a ha
    exact (Function.update_of_ne (show a≠dst+4 by omega) _ _).trans (hkeep a ha)

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {fA fB fC : ℕ→ℤ}
    {n g vals owners positions records idx pair bank cover NB NC p h J cut occ code srcB srcC report dst d : ℕ}
    {rs : List Record} {shift : ℤ}
    (HA : BandRawA.Stored μ vals owners positions fA (items n g rs))
    (HR : Seg μ records (cells rs)) (hidx : idx<(items n g rs).length)
    (HP : SourceBandPairData.Stored μ fB fC pair NB NC g p (modulus h J) shift)
    (HB : SourceBandBankData.Stored μ fB fC bank NB NC g h J cut occ (p : ℤ) shift)
    (HC : LightCoverKeyData.Stored μ cover h J)
    (HQ : SharedReportingBankHeader.Stored μ report h J NB NC g fB fC (p : ℤ) shift)
    (hi : (ownerRecord n g rs idx).b<BandPartition.size NB g)
    (hj : (ownerRecord n g rs idx).c<BandPartition.size NC g)
    (hk : code<LightBlockSourceCatalog.count h J)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hvals : vals+(items n g rs).length≤dst) (howners : owners+(items n g rs).length≤dst)
    (hrecords : records+4*rs.length≤dst) (hsrcB : srcB+NB≤dst) (hsrcC : srcC+NC≤dst)
    (hpair : SourceBandPairData.next pair NB NC g (modulus h J)≤dst)
    (hbank : SourceBandBankData.finish bank NB NC g h J cut≤dst)
    (hocc : occ+LightBlockSourceCatalog.count h J*J≤bank)
    (hcover : LightCoverKeyData.keyEnd cover h J≤dst)
    (hreport : SharedReportingBankHeader.finish report h J NB NC g≤dst)
    (hspace : space (selection n g rs idx pair bank cover NB NC h J cut occ code)
      pair bank cover srcB srcC (ownerRecord n g rs idx).b (ownerRecord n g rs idx).c code J (dst+5)≤lim.space)
    (hvalue : |fA (labelAt n g rs idx).position|≤lim.word) :
    Meets lim program 3 d [vals,owners,records,idx,pair,bank,cover,srcB,srcC,code,J,report,dst] μ 8100
      (fun result ν => result=(dst : ℤ) ∧
        Seg ν dst (record fA n g rs idx pair bank cover NB NC h J cut occ code srcB srcC report) ∧
        Kept μ ν dst) :=
  program_meets_fits HA HR hidx HP HB HC HQ hi hj hk hw hd
    hvals howners hrecords hsrcB hsrcC hpair hbank hocc hcover hreport
    (fits_of_space _ _ _ _ _ _ _ _ _ _ _ _ hspace) hvalue

end ThreeSum.LightReportingWantedAccess
