import Submission.ThreeSum.LightSourceBandBankStep

/-! # Actual source-bank catalog loop over common padded band indices -/

namespace ThreeSum.LightSourceBandBankBatch

open Light GlobalEncoding BlockEncoding BlockCoefficientRows BlockSourceEncoding
open LocalCoverBounds SubsetAddress BlockSourceOccurrenceOrder SourceBandBankLayout

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def body (pStep : ℕ) : Stmt :=
  .for 18 (v 16) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
      v 13 +' v 18 *' v 17,v 14,v 15,v 18] 19)

def time (NL NR g h J cut : ℕ) : ℕ :=
  SourceBandPairSlices.count NL NR g*(LightSourceBandBankStep.time h J cut+200)+20

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightSourceBandBankStep.Procs P pStep
  main : P[pMain]?=some (body pStep)

def Inv (μ : ℕ → ℤ) (fL fR : ℕ → ℤ)
    (pair NL NR g p h J cut occ maps candidates histL histR base : ℕ) (shift : ℤ)
    (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,
      histL,histR,pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,
      SourceBandPairSlices.count NL NR g,span h J cut,i,r],ν⟩ ∧
    (∀ j < i, At ν fL fR base NL NR g h J cut (p : ℤ) shift j) ∧ Kept μ ν base

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p h J cut occ maps candidates histL histR base : ℕ}
    {shift : ℤ} (H : SourceBandPairData.Stored μ fL fR pair NL NR g p (modulus h J) shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+13 ≤ lim.depth)
    (hg : 0 < g) (hcut : cut ≤ J*(512*h))
    (hpair : SourceBandPairData.next pair NL NR g (modulus h J) ≤ base)
    (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hmaps : maps+2*(512*h)*scheduleSize h ≤ base)
    (hcandidates : candidates+scheduleSize h ≤ base)
    (hleft : histL+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hright : histR+LightLocalCoverSchedule.rows h*localPrime h ≤ base)
    (hspace : baseAt base h J cut (SourceBandPairSlices.count NL NR g) ≤ lim.space)
    (hword : (LightSourceBandBankStep.word NL NR h J : ℤ) ≤ lim.word)
    (hoccRead : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
      μ (occ+k*J+j)=(occurrenceIndices (outputOccurrences (representative h J k)) j : ℤ))
    (hcover : BlockSourceCoverInput.Input μ h maps candidates histL histR) :
    Meets lim P pMain d
      [J,512*h,h,localPrime h,localBucketCap h,cut,modulus h J,occ,maps,candidates,histL,histR,
        pair,base,downsetCap (J*(512*h)) cut,LightBlockSourceCatalog.count h J,
        SourceBandPairSlices.count NL NR g,span h J cut]
      μ (time NL NR g h J cut) (fun _ ν =>
        (∀ i < SourceBandPairSlices.count NL NR g,
          At ν fL fR base NL NR g h J cut (p : ℤ) shift i) ∧ Kept μ ν base) := by
  have hm := modulus_pos h J
  have hbase : base ≤ lim.space := by unfold baseAt at hspace; omega
  have hNL := BandPartition.size_le NL g
  have hNR := BandPartition.size_le NR g
  have hcount : SourceBandPairSlices.count NL NR g ≤ NL+NR := by unfold SourceBandPairSlices.count; omega
  have hcountWord : (SourceBandPairSlices.count NL NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show SourceBandPairSlices.count NL NR g ≤ LightSourceBandBankStep.word NL NR h J by
      unfold LightSourceBandBankStep.word; omega)).trans hword
  apply Meets.of_body C.main
  unfold body time
  refine Ends.for (Inv μ fL fR pair NL NR g p h J cut occ maps candidates histL histR base shift)
    (SourceBandPairSlices.count NL NR g) (LightSourceBandBankStep.time h J cut+192)
    ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi
      omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hiEnd := (baseAt_mono base h J cut (show i+1 ≤ SourceBandPairSlices.count NL NR g by omega)).trans hspace
    have hiSpace : LightBlockSourceRetainedHost.space
        (LightBlockSourceBatchLayout.work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut)
        h J ≤ lim.space := by rw [complete_end]; exact hiEnd
    have hiBase : base ≤ baseAt base h J cut i := Nat.le_add_right _ _
    have hnewBase : baseAt base h J cut i ≤ lim.space :=
      (baseAt_mono base h J cut (show i ≤ i+1 by omega)).trans hiEnd
    have hprod : (i : ℤ)*(span h J cut : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show i*span h J cut ≤ lim.space by unfold baseAt at hnewBase; omega) :
        (i : ℤ)*(span h J cut : ℤ) ≤ lim.space).trans hw
    have hprodNonneg : (0 : ℤ) ≤ (i : ℤ)*(span h J cut : ℤ) := by positivity
    have hbaseExpr : (base : ℤ)+(i : ℤ)*(span h J cut : ℤ) ≤ lim.word :=
      (by exact_mod_cast hnewBase : (base : ℤ)+(i : ℤ)*(span h J cut : ℤ) ≤ lim.space).trans hw
    have H' := H.of_kept hm kept hpair
    have hcover' := hcover.of_kept kept hmaps hcandidates hleft hright
    have hrows : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
        ν (occ+k*J+j)=(occurrenceIndices (outputOccurrences (representative h J k)) j : ℤ) := by
      intro k hk j hj
      have hp := Nat.mul_le_mul_right J (show k+1 ≤ LightBlockSourceCatalog.count h J by omega)
      exact (kept _ (by nlinarith)).trans (hoccRead k hk j hj)
    have hrun := C.step.meets (d := d+1) (μ := ν) (base := baseAt base h J cut i)
      H' hw (by omega) hg hi hcut (hpair.trans hiBase) (hocc.trans hiBase)
      (hmaps.trans hiBase) (hcandidates.trans hiBase) (hleft.trans hiBase) (hright.trans hiBase)
      hiSpace hword hrows hcover'
    light_call hrun using baseAt with s ν' ⟨stored,kept'⟩
    refine ⟨by simp,s,ν',by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (written j hj).of_kept kept' (baseAt_mono base h J cut (by omega))
      · exact stored
    · intro a ha
      exact (kept' a (by omega)).trans (kept a ha)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    simp

end ThreeSum.LightSourceBandBankBatch
