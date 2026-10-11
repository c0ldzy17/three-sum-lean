import Submission.ThreeSum.EncodedColorWantedData
import Submission.ThreeSum.EncodedColorCoverData
import Submission.ThreeSum.LightSourceFinitePrepared

/-!
# Source banks from the actual cover and wanted output headers

The program reads its reusable destination from wanted+2, reads all local
source controls and pointers from the constructed cover header, computes
localPrime^J with the existing scalar-power procedure, and invokes the
complete shared source host. No source dimension or cover pointer is an
externally supplied control.
-/

namespace ThreeSum.LightEncodedColorSources

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SourceFiniteInputs

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

def sourceBase (free p M h J : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  EncodedColorWantedData.nextFree (LightGuardedWanted.wantedFree free h J xs.length) M
    (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J) (3*xs.length)
    (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J : ℤ)

/-- h,J,cut,B value/header,C value/header,g,P,wanted header,cover header. -/
def body (pPower pSource : ℕ) : Stmt :=
  .set 11 (M (v 9 +' k 2)) ;;
  .set 12 (v 9 +' k 3) ;;
  .set 13 (M (v 10 +' k 6)) ;;
  .call pPower [v 13,v 1] 14 ;;
  .set 15 (M (v 10 +' k 8)) ;;
  .set 16 (M (v 10 +' k 7)) ;;
  .set 17 (M (v 10 +' k 10)) ;;
  .set 18 (M (v 10 +' k 12)) ;;
  .set 19 (M (v 10 +' k 13)) ;;
  .set 20 (M (v 10 +' k 14)) ;;
  .set 21 (M (v 10 +' k 15)) ;;
  .call pSource [v 1,v 15,v 0,v 13,v 16,v 2,v 14,v 18,v 19,v 20,v 21,
    v 3,v 4,v 5,v 6,v 7,v 8,v 12,v 11,v 17] 0

def program : Program := LightSourceControlsHostProgram.program ++ [body 74 79]

theorem program_length : program.length=81 := rfl

def time (NL NR g p h J cut U M : ℕ) : ℕ :=
  LightNatPower.time J+LightSourceControlsHost.time NL NR g p h J cut U M+1000

variable {lim : Limits} {d : ℕ}

theorem program_meets {μ : ℕ → ℤ} {free bv be cv ce g p M h J cut U : ℕ} [NeZero M]
    {hg : 0 < g} {originalB originalC B C xs : List ℤ}
    {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+17 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hbv : bv+originalB.length ≤ free) (hcv : cv+originalC.length ≤ free)
    (hbe : be+2 ≤ free) (hce : ce+2 ≤ free)
    (hspace : LightSourceControlsHost.space (sourceBase free p M h J xs)
      B.length C.length g p h J cut U M ≤ lim.space)
    (hword : (LightSourceControlsHost.word B.length C.length g p h J cut U M : ℤ) ≤ lim.word)
    (hB : LightBandPreprocessing.Represents μ bv be g hg originalB B hsB)
    (hC : LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (hcover : LightCoverKeyData.Stored μ free h J)
    (hwanted : LightWantedSetup.Output μ (LightGuardedWanted.wantedFree free h J xs.length) M
      (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J)
      (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J)) :
    Meets lim program 80 d [h,J,cut,bv,be,cv,ce,g,p,LightGuardedWanted.wantedFree free h J xs.length,free] μ
      (time B.length C.length g p h J cut U M)
      (fun r ν =>
        SourceFiniteData.Stored ν (sourceBase free p M h J xs) g p h J cut B C
          (RawAKeyLists.selected M p xs h J : ℤ) r ∧
        LightCoverKeyData.Stored ν free h J ∧
        LightWantedSetup.Output ν (LightGuardedWanted.wantedFree free h J xs.length) M
          (LightGuardedWanted.left p xs) (LightGuardedWanted.right h J)
          (3*xs.length) (LightGuardedWanted.totalKeys h J) (RawAKeyLists.selected M p xs h J) ∧
        Kept μ ν (sourceBase free p M h J xs)) := by
  let base := sourceBase free p M h J xs
  let out := LightGuardedWanted.wantedFree free h J xs.length
  have hout : out=LightCoverKeyData.keyEnd free h J+3*xs.length := rfl
  have hheader : out+4 ≤ base := EncodedColorWantedData.header_le_nextFree ..
  have hkey : LightCoverKeyData.keyEnd free h J ≤ base := by omega
  have hfree20 : free+20 ≤ base := (EncodedColorCoverData.header_end free h J).trans hkey
  have hcontrolSpace : LightSourceControls.space (LightSourceControlsHost.sourceBase base) h J ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hbase : base+3 ≤ lim.space := by
    unfold LightSourceControls.space LightSourceControlsHost.sourceBase at hcontrolSpace
    omega
  have hcontrolWord : (LightSourceControls.word h J cut : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hall (z : ℕ) (hz : z ≤ LightSourceControls.word h J cut) : (z : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hz).trans hcontrolWord
  have hJ := hall J (by unfold LightSourceControls.word; omega)
  have hLP := hall (localPrime h) (by unfold LightSourceControls.word; omega)
  have hL := hall (512*h) (by unfold LightSourceControls.word; omega)
  have hT := hall (scheduleSize h) (by unfold LightSourceControls.word; omega)
  have hMod := hall (modulus h J) (by unfold LightSourceControls.word; omega)
  have hcap : (localBucketCap h : ℤ) ≤ lim.word := by
    have hhost : (LightSourceBandHost.word B.length C.length g p h J U M : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
    have hbanks : (LightSourceBandBanks.word B.length C.length h J : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (le_max_right _ _)).trans hhost
    have hh : (LightSourceBandBankStep.word B.length C.length h J : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (le_max_left _ _)).trans hbanks
    have hsmall : localBucketCap h ≤ LightSourceBandBankStep.word B.length C.length h J := by
      unfold LightSourceBandBankStep.word LightBlockSourceRetainedHost.word
        LightSourcePreparation.word LightSourceMaskFlags.word LightSourceRowFlag.word
      generalize 2^(J*(512*h)+1)=power
      omega
    exact (Int.ofNat_le.mpr hsmall).trans hh
  have hpower (i : ℕ) (hi : i ≤ J) : ((localPrime h^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (localPrime_pos h) hi)).trans hMod
  obtain ⟨rLP,rCap,rL,rT,rMaps,rCandidates,rLeft,rRight⟩ := EncodedColorCoverData.source_controls hcover
  obtain ⟨eMaps,eCandidates,eLeft,eRight⟩ := cover_ends free h J
  have hmaps : (maps free h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show maps free h ≤ lim.space by omega)).trans hw
  have hcandidates : (candidates free h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show candidates free h ≤ lim.space by omega)).trans hw
  have hleft : (leftCounts free h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show leftCounts free h ≤ lim.space by omega)).trans hw
  have hright : (rightCounts free h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show rightCounts free h ≤ lim.space by omega)).trans hw
  have readBase : μ (out+2)=(base : ℤ) := EncodedColorWantedData.nextFree_read hwanted
  have readBaseRuntime : μ (((LightGuardedWanted.wantedFree free h J xs.length : ℤ)+2).toNat)=
      (base : ℤ) := by
    rw [show ((LightGuardedWanted.wantedFree free h J xs.length : ℤ)+2).toNat=out+2 by
      dsimp only [out]; omega]
    exact readBase
  have addFree6 : ((free : ℤ)+6).toNat=free+6 := by omega
  have addFree7 : ((free : ℤ)+7).toNat=free+7 := by omega
  have addFree8 : ((free : ℤ)+8).toNat=free+8 := by omega
  have addFree10 : ((free : ℤ)+10).toNat=free+10 := by omega
  have addFree12 : ((free : ℤ)+12).toNat=free+12 := by omega
  have addFree13 : ((free : ℤ)+13).toNat=free+13 := by omega
  have addFree14 : ((free : ℤ)+14).toNat=free+14 := by omega
  have addFree15 : ((free : ℤ)+15).toNat=free+15 := by omega
  apply Meets.of_body (p := 80) (by rfl : program[80]?=some (body 74 79))
  unfold body time
  light_set (base : ℕ) using readBaseRuntime
  light_set (out+3 : ℕ)
  light_set (localPrime h : ℕ) using rLP,addFree6
  light_call (LightNatPower.meets (d := d+1) (by rfl : program[74]?=some LightNatPower.body) μ hJ hpower)
    with rMod ν₀ ⟨hrMod,hmem⟩
  subst ν₀
  have hrMod' : rMod=(modulus h J : ℤ) := hrMod
  light_set (512*h : ℕ) using rL,addFree8
  light_set (localBucketCap h : ℕ) using rCap,addFree7
  light_set (scheduleSize h : ℕ) using rT,addFree10
  light_set (maps free h : ℕ) using rMaps,addFree12
  light_set (candidates free h : ℕ) using rCandidates,addFree13
  light_set (leftCounts free h : ℕ) using rLeft,addFree14
  light_set (rightCounts free h : ℕ) using rRight,addFree15
  have hSource := (LightSourceFinitePrepared.meets LightSourceControlsHostProgram.programProcs
    (d := d+1) (μ := μ) (free := free) (base := base) (p := p) (h := h) (J := J) (cut := cut) (U := U) (M := M)
    (xs := xs) hw (by omega) hp hcut (by omega) (by omega) (by omega) (by omega)
    (by change out+3 < base; omega) hspace hword hB hC hboundB hboundC hcover hwanted).append [body 74 79]
  light_call hSource using LightSourceFinitePrepared.args,hrMod' with r ν ⟨sources,cover,kept⟩
  exact ⟨sources,cover,EncodedColorWantedData.of_kept hwanted kept le_rfl,kept⟩

end ThreeSum.LightEncodedColorSources
