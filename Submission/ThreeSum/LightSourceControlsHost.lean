import Submission.ThreeSum.LightSourceControlsProgram
import Submission.ThreeSum.SourceBandHostCosts

/-!
# Shared source construction with its size controls computed by the program

Three persistent control cells precede the complete source host. The
capacity initializer's polynomial scratch is reclaimed by the source host.
Occurrence count, compact capacity, and bank stride are read from the
constructed cells or the initializer result, never supplied as arguments.
-/

namespace ThreeSum.LightSourceControlsHost

open Light GlobalEncoding BlockSourceEncoding LocalCoverBounds SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def sourceBase (base : ℕ) : ℕ := base+3

def finish (base NL NR g h J cut : ℕ) : ℕ :=
  LightSourceBandHost.finish (sourceBase base) NL NR g h J cut

def space (base NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceControls.space (sourceBase base) h J)
    (LightSourceBandHost.space (sourceBase base) NL NR g p h J cut U D)

def word (NL NR g p h J cut U D : ℕ) : ℕ :=
  max (LightSourceControls.word h J cut) (LightSourceBandHost.word NL NR g p h J U D)

def time (NL NR g p h J cut U D : ℕ) : ℕ :=
  LightSourceControls.time h J+LightSourceBandHost.time NL NR g p h J cut U D+500

/-- The source host's original inputs and local schedule size; none of
the occurrence count, compact capacity, or bank span is an input. -/
def body (pControls pSource : ℕ) : Stmt :=
  .set 20 (v 18 +' k 3) ;;
  .call pControls [v 0,v 1,v 3,v 5,v 19,v 6,v 18,v 20] 21 ;;
  .set 22 (M (v 18)) ;;
  .set 23 (M (v 18 +' k 1)) ;;
  .call pSource [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,
    v 11,v 12,v 13,v 14,v 15,v 16,v 17,v 20,v 22,v 23,v 19,v 21] 24 ;;
  .set 0 (v 24)

structure Procs (P : Program) (pMain : ℕ) where
  pControls : ℕ
  pSource : ℕ
  controls : LightSourceControls.Procs P pControls
  source : LightSourceBandHost.Procs P pSource
  main : P[pMain]?=some (body pControls pSource)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {srcL headL srcR headR shiftCell base NL NR g p h J cut U D maps candidates histL histR : ℕ}
    {shift : ℤ} (fL fR : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+16 ≤ lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hsrcL : srcL+NL ≤ base) (hsrcR : srcR+NR ≤ base)
    (hheadL : headL+2 ≤ base) (hheadR : headR+2 ≤ base) (hshiftCell : shiftCell < base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ base)
    (hcandidates : candidates+scheduleSize h ≤ base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hspace : space base NL NR g p h J cut U D ≤ lim.space)
    (hword : (word NL NR g p h J cut U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ))
    (hlenL : μ headL=(NL : ℤ)) (hlenR : μ headR=(NR : ℤ))
    (hcountL : μ (headL+1)=(BandPartition.size NL g : ℤ))
    (hcountR : μ (headR+1)=(BandPartition.size NR g : ℤ)) (hshiftRead : μ shiftCell=shift)
    (hreadL : ∀ j < NL, μ (srcL+j)=fL j) (hreadR : ∀ j < NR, μ (srcR+j)=fR j)
    (hvaluesL : ∀ j < NL, |fL j| ≤ (U : ℤ)) (hvaluesR : ∀ j < NR, |fR j| ≤ (U : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,maps,candidates,histL,histR,
        srcL,headL,srcR,headR,g,p,shiftCell,base,scheduleSize h]
      μ (time NL NR g p h J cut U D) (fun r ν =>
        r=(finish base NL NR g h J cut : ℤ) ∧
        Seg ν base (SourceControlLayout.values h J cut) ∧
        SourceBandPairData.Stored ν fL fR (sourceBase base) NL NR g p (modulus h J) shift ∧
        SourceBandBankData.Stored ν fL fR
          (LightSourceBandHost.bankHeader (sourceBase base) NL NR g h J) NL NR g h J cut
          (LightSourceBandHost.occurrenceBase (sourceBase base) NL NR g h J) (p : ℤ) shift ∧
        Kept μ ν base) := by
  have hsControl : LightSourceControls.space (sourceBase base) h J ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hsSource : LightSourceBandHost.space (sourceBase base) NL NR g p h J cut U D ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hwControl : (LightSourceControls.word h J cut : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hwSource : (LightSourceBandHost.word NL NR g p h J U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hbaseSource : base ≤ sourceBase base := Nat.le_add_right _ _
  have hbaseBound : sourceBase base ≤ lim.space := by unfold LightSourceControls.space at hsControl; omega
  have hsourceBound : base+3 ≤ lim.space := hbaseBound
  have hK : (downsetCap (J*(512*h)) cut : ℤ) ≤ lim.word := by
    apply (Int.ofNat_le.mpr (show downsetCap (J*(512*h)) cut ≤ LightSourceControls.word h J cut from ?_)).trans hwControl
    unfold LightSourceControls.word LightSourceControls.spanWord SourceControlLayout.word
    omega
  have hS : (LightBlockSourceCatalog.count h J : ℤ) ≤ lim.word := by
    apply (Int.ofNat_le.mpr (show LightBlockSourceCatalog.count h J ≤ LightSourceControls.word h J cut from ?_)).trans hwControl
    unfold LightSourceControls.word LightSourceControls.spanWord SourceControlLayout.word
    omega
  have hsEnd : finish base NL NR g h J cut ≤ lim.space := by
    have hsb := (le_max_right _ _).trans hsSource
    have hsd := (le_max_left _ _).trans hsb
    unfold LightOutputDecodeDigits.space at hsd
    unfold finish LightSourceBandHost.finish
    omega
  apply Meets.of_body C.main
  unfold body time
  light_set (sourceBase base : ℕ) using sourceBase
  have hcontrolsCall := C.controls.meets (d := d+1) (μ := μ) (dst := base) (work := sourceBase base)
    hw (by omega) hcut le_rfl hsControl hwControl
  light_call hcontrolsCall with rSpan ν₁ ⟨hrSpan,controlData,keptControl⟩
  have hreadK : ν₁ base=(downsetCap (J*(512*h)) cut : ℤ) := by
    simpa [SourceControlLayout.values] using controlData.getD (i := 0) (by simp [SourceControlLayout.values]) 0
  have hreadS : ν₁ (base+1)=(LightBlockSourceCatalog.count h J : ℤ) := by
    simpa [SourceControlLayout.values] using controlData.getD (i := 1) (by simp [SourceControlLayout.values]) 0
  have haddr : ((base : ℤ)+1).toNat=base+1 := by omega
  light_set (downsetCap (J*(512*h)) cut : ℕ) using hreadK,sourceBase
  light_set (LightBlockSourceCatalog.count h J : ℕ) using hreadS,haddr,sourceBase
  have cover₁ := hcover.of_kept keptControl hmaps hcandidates hleft hright
  have hsourceCall := C.source.meets (d := d+1) (μ := ν₁) (srcL := srcL) (headL := headL)
    (srcR := srcR) (headR := headR) (shiftCell := shiftCell) (base := sourceBase base)
    (NL := NL) (NR := NR) (g := g) (p := p) (h := h) (J := J) (cut := cut) (U := U) (D := D) (shift := shift)
    fL fR hw (by omega) hg hp hcut (hsrcL.trans hbaseSource) (hsrcR.trans hbaseSource)
    (hheadL.trans hbaseSource) (hheadR.trans hbaseSource) (hshiftCell.trans_le hbaseSource)
    (hmaps.trans hbaseSource) (hcandidates.trans hbaseSource) (hleft.trans hbaseSource) (hright.trans hbaseSource)
    hsSource hwSource hshift
    ((keptControl _ (by omega)).trans hlenL) ((keptControl _ (by omega)).trans hlenR)
    ((keptControl _ (by omega)).trans hcountL) ((keptControl _ (by omega)).trans hcountR)
    ((keptControl _ hshiftCell).trans hshiftRead)
    (fun j hj => (keptControl _ (by omega)).trans (hreadL j hj))
    (fun j hj => (keptControl _ (by omega)).trans (hreadR j hj)) hvaluesL hvaluesR cover₁
  light_call hsourceCall using hrSpan with rSource ν₂ ⟨hrSource,pairData,bankData,keptSource⟩
  have hrSource' : rSource=(finish base NL NR g h J cut : ℤ) := hrSource
  light_set (finish base NL NR g h J cut : ℕ) using hrSource'
  refine ⟨rfl,?_,pairData,bankData,?_⟩
  · intro i hi
    have hi' : i < 3 := by simpa [SourceControlLayout.values] using hi
    exact (keptSource _ (by unfold sourceBase; omega)).trans (controlData i hi)
  · intro a ha
    exact (keptSource _ (ha.trans_le hbaseSource)).trans (keptControl a ha)

end ThreeSum.LightSourceControlsHost
