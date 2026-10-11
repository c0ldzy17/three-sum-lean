import Submission.ThreeSum.LightSourceBandPair
import Submission.ThreeSum.LightSourceBandBanksProgram

/-!
# Original normalized source arrays to the complete shared source-bank host

The first call reads physical normalized headers and the selected offset,
and constructs the retained histograms and original-position buckets once.
The second call constructs one occurrence table and all common-band source
banks. The complete host assumes no precomputed source histogram or stage.
-/

namespace ThreeSum.LightSourceBandHost

open Light GlobalEncoding BlockSourceEncoding LocalCoverBounds SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def occurrenceBase (base NL NR g h J : ℕ) : ℕ :=
  SourceBandPairData.next base NL NR g (modulus h J)

def bankHeader (base NL NR g h J : ℕ) : ℕ :=
  occurrenceBase base NL NR g h J+LightBlockSourceCatalog.count h J*J

def finish (base NL NR g h J cut : ℕ) : ℕ :=
  SourceBandBankData.finish (bankHeader base NL NR g h J) NL NR g h J cut

def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceBandPair.space base NL NR g p (modulus h J) U D)
    (LightSourceBandBanks.space (bankHeader base NL NR g h J) NL NR g h J cut)

def word (NL NR g p h J U D : ℕ) : ℕ :=
  max (LightSourceBandPair.word NL NR g p (modulus h J) U D)
    (LightSourceBandBanks.word NL NR h J)

def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  LightSourceBandPair.time NL NR g p (modulus h J) U D+
    LightSourceBandBanks.time NL NR g h J cut+500

/-- J,L,h,local prime/cap,cut,modulus,cover arrays, original source value and
endpoint pointers,g,selected original prime,offset cell,free pointer,and
the ordinary compact-capacity/occurrence-count/schedule-size/band-stride controls. -/
def body (pPair pBanks : ℕ) : Stmt :=
  .call pPair [v 11,v 12,v 13,v 14,v 15,v 16,v 6,v 17,v 18] 23 ;;
  .set 24 (v 23 +' v 20 *' v 0) ;;
  .call pBanks [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 23,v 7,v 8,v 9,v 10,v 18,v 24,
    v 19,v 20,v 21,v 22] 25 ;;
  .set 0 (v 25)

structure Procs (P : Program) (pMain : ℕ) where
  pPair : ℕ
  pBanks : ℕ
  pair : LightSourceBandPair.Procs P pPair
  banks : LightSourceBandBanks.Procs P pBanks
  main : P[pMain]?=some (body pPair pBanks)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {srcL headL srcR headR shiftCell base NL NR g p h J cut U D maps candidates histL histR : ℕ}
    {shift : ℤ} (fL fR : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+15 ≤ lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hsrcL : srcL+NL ≤ base) (hsrcR : srcR+NR ≤ base)
    (hheadL : headL+2 ≤ base) (hheadR : headR+2 ≤ base) (hshiftCell : shiftCell < base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ base)
    (hcandidates : candidates+scheduleSize h ≤ base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hspace : space base NL NR g p h J cut U D ≤ lim.space)
    (hword : (word NL NR g p h J U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ))
    (hlenL : μ headL=(NL : ℤ)) (hlenR : μ headR=(NR : ℤ))
    (hcountL : μ (headL+1)=(BandPartition.size NL g : ℤ))
    (hcountR : μ (headR+1)=(BandPartition.size NR g : ℤ)) (hshiftRead : μ shiftCell=shift)
    (hreadL : ∀ j < NL, μ (srcL+j)=fL j) (hreadR : ∀ j < NR, μ (srcR+j)=fR j)
    (hvaluesL : ∀ j < NL, |fL j| ≤ (U : ℤ)) (hvaluesR : ∀ j < NR, |fR j| ≤ (U : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,maps,candidates,histL,histR,
        srcL,headL,srcR,headR,g,p,shiftCell,base,downsetCap (J*(512*h)) cut,
        LightBlockSourceCatalog.count h J,scheduleSize h,SourceBandBankLayout.span h J cut]
      μ (time NL NR g p h J cut U D) (fun r ν =>
        r=(finish base NL NR g h J cut : ℤ) ∧
        SourceBandPairData.Stored ν fL fR base NL NR g p (modulus h J) shift ∧
        SourceBandBankData.Stored ν fL fR (bankHeader base NL NR g h J) NL NR g h J cut
          (occurrenceBase base NL NR g h J) (p : ℤ) shift ∧ Kept μ ν base) := by
  have hm := modulus_pos h J
  have hsPair : LightSourceBandPair.space base NL NR g p (modulus h J) U D ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsBanks : LightSourceBandBanks.space (bankHeader base NL NR g h J) NL NR g h J cut ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwPair : (LightSourceBandPair.word NL NR g p (modulus h J) U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwBanks : (LightSourceBandBanks.word NL NR h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hsDigits := (le_max_left _ _).trans hsBanks
  have hsEnd : finish base NL NR g h J cut ≤ lim.space := by
    unfold LightOutputDecodeDigits.space at hsDigits
    unfold finish
    omega
  have hheader : bankHeader base NL NR g h J+5 ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  have hprod : (LightBlockSourceCatalog.count h J : ℤ)*(J : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show LightBlockSourceCatalog.count h J*J ≤ lim.space by
      unfold bankHeader at hheader; omega) :
      (LightBlockSourceCatalog.count h J : ℤ)*(J : ℤ) ≤ lim.space).trans hw
  have hprodNonneg : (0 : ℤ) ≤ (LightBlockSourceCatalog.count h J : ℤ)*(J : ℤ) := by positivity
  have hheaderAddr : (occurrenceBase base NL NR g h J : ℤ)+
      (LightBlockSourceCatalog.count h J : ℤ)*(J : ℤ) ≤ lim.word :=
    (by exact_mod_cast (show bankHeader base NL NR g h J ≤ lim.space by omega) :
      (occurrenceBase base NL NR g h J : ℤ)+(LightBlockSourceCatalog.count h J : ℤ)*(J : ℤ) ≤ lim.space).trans hw
  have ho := SourceBandPairData.ordered base NL NR g (modulus h J)
  have hbaseOcc : base ≤ occurrenceBase base NL NR g h J := by
    unfold SourceBandPairData.leftBase at ho
    change base ≤ SourceBandPairData.next base NL NR g (modulus h J)
    omega
  apply Meets.of_body C.main
  unfold body time
  have hrunPair := C.pair.meets (d := d+1) (μ := μ) (srcL := srcL) (headL := headL)
    (srcR := srcR) (headR := headR) (shiftCell := shiftCell) (base := base)
    (NL := NL) (NR := NR) (g := g) (p := p) (m := modulus h J) (U := U) (D := D) (shift := shift)
    fL fR hw (by omega) hg hp hm hsrcL hsrcR hheadL hheadR hshiftCell hsPair hwPair hshift
    hlenL hlenR hcountL hcountR hshiftRead hreadL hreadR hvaluesL hvaluesR
  light_call hrunPair with rPair ν₁ ⟨hrPair,pairData,keptPair⟩
  have hrPair' : rPair=(occurrenceBase base NL NR g h J : ℤ) := hrPair
  light_set (bankHeader base NL NR g h J : ℕ) using bankHeader,hrPair'
  have cover₁ := hcover.of_kept keptPair hmaps hcandidates hleft hright
  have hrunBanks := C.banks.meets (d := d+1) (μ := ν₁) (base := bankHeader base NL NR g h J)
    (occ := occurrenceBase base NL NR g h J) pairData hw (by omega) hg hcut le_rfl le_rfl
    (hmaps.trans hbaseOcc) (hcandidates.trans hbaseOcc) (hleft.trans hbaseOcc) (hright.trans hbaseOcc)
    hsBanks hwBanks cover₁
  light_call hrunBanks using hrPair' with rBanks ν₂ ⟨hrBanks,bankData,keptBanks⟩
  have hrBanks' : rBanks=(finish base NL NR g h J cut : ℤ) := hrBanks
  light_set (finish base NL NR g h J cut : ℕ) using hrBanks'
  exact ⟨rfl,pairData.of_kept hm keptBanks le_rfl,bankData,
    fun a ha => (keptBanks a (by omega)).trans (keptPair a ha)⟩

end ThreeSum.LightSourceBandHost
