import Submission.ThreeSum.LightLocalCoverMetadata
import Submission.ThreeSum.LightLocalParameters

/-!
# The complete local cover initialized from h and the original free pointer

The first eight header cells are the original local graph counts, prime,
and bucket cap. The next twelve contain computed dimensions and packed
pointers. The cover tables begin immediately after this fixed header.
-/

namespace ThreeSum.LightLocalCoverInit

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables
open LightLocalCoverLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def base (free : ℕ) : ℕ := free+20

def values (free h : ℕ) : List ℤ :=
  LightLocalParameters.values h++LightLocalCoverMetadata.values (base free) h

def body (pParameters pMetadata pSetup : ℕ) : Stmt :=
  .set 2 (v 1 +' k 20) ;;
  .call pParameters [v 0,v 1,v 2] 3 ;;
  .set 4 (M (v 1 +' k 1)) ;;
  .set 5 (M (v 1 +' k 7)) ;;
  .set 6 (v 1 +' k 8) ;;
  .call pMetadata [v 0,v 3,v 4,v 2,v 6] 7 ;;
  .call pSetup [v 0,v 3,v 4,v 5,v 2] 8 ;;
  .set 0 (v 7)

def time (h : ℕ) : ℕ := LightLocalParameters.time h+
  LightLocalCoverMetadata.time h+LightLocalCoverSetup.time h+100

def word (h : ℕ) : ℕ := LightLocalParameters.word h+LightLocalCoverSetup.word h

def space (free h : ℕ) : ℕ :=
  max (LightLocalParameters.space (base free) h) (LightLocalCoverLayout.space (base free) h)

structure Procs (P : Program) (pMain : ℕ) where
  pParameters : ℕ
  pMetadata : ℕ
  pSetup : ℕ
  parameters : LightLocalParameters.Procs P pParameters
  metadata : LightLocalCoverMetadata.Procs P pMetadata
  setup : LightLocalCoverSetup.Procs P pSetup
  main : P[pMain]? = some (body pParameters pMetadata pSetup)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {free h : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+9 ≤ lim.depth)
    (hspace : space free h ≤ lim.space) (hword : (word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,free] μ (time h)
      (fun r ν => r = (LightLocalCoverMetadata.nextFree (base free) h : ℤ) ∧
        Seg ν free (values free h) ∧
        Data ν h (maps (base free) h) (hist0 (base free) h)
          (hist1 (base free) h) (matrixPtr (base free) h) ∧
        ScheduleRows ν h (scheduleMaps (base free) h) ∧
        (∀ s : Occurrence h, ν (candidates (base free) h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν free) := by
  have hpspace : LightLocalParameters.space (base free) h ≤ lim.space :=
    (le_max_left _ _).trans hspace
  have hcspace : LightLocalCoverLayout.space (base free) h ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hpword : (LightLocalParameters.word h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_add_right ..)).trans hword
  have hcword : (LightLocalCoverSetup.word h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.le_add_left ..)).trans hword
  have hwork : work (base free) h ≤ lim.space := (work_le_space _ _).trans hcspace
  have hbase : base free ≤ lim.space := by
    unfold work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr at hwork
    omega
  have hheaderSpace : free+20 ≤ lim.space := hbase
  have hbaseWord : (base free : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hbase).trans hw
  have hbaseWordZ : (free : ℤ)+20 ≤ lim.word := by simpa only [base,Nat.cast_add,Nat.cast_ofNat] using hbaseWord
  have hnext : LightLocalCoverMetadata.nextFree (base free) h ≤ lim.space :=
    (schedule_end_le_space _ _).trans hcspace
  have hnextWord : (LightLocalCoverMetadata.nextFree (base free) h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hnext).trans hw
  apply Meets.of_body S.main
  unfold body time
  light_set (base free : ℕ) using time,base
  light_call (S.parameters.meets (d := d+1) (μ := μ) (h := h) (dst := free) (work := base free)
    hw (by omega) (by unfold base; omega) hpspace hpword)
    using time with prime μ₁ ⟨hprime,hparams,hkeep₁⟩
  have hn : μ₁ (free+1) = (vertices h : ℤ) := by
    simpa [LightLocalParameters.values,LightLocalCounts.values,vertices,LocalMaskGraph.vertexCount,
      LocalCoverBounds.vertexCount] using hparams 1 (by simp [LightLocalParameters.values,LightLocalCounts.values])
  have hcap : μ₁ (free+7) = (localBucketCap h : ℤ) := by
    simpa [LightLocalParameters.values,LightLocalCounts.values] using
      hparams 7 (by simp [LightLocalParameters.values,LightLocalCounts.values])
  have hcapRead : μ₁ (((free : ℤ)+7).toNat) = (localBucketCap h : ℤ) := by
    have he : ((free : ℤ)+7).toNat = free+7 := by omega
    rw [he]
    exact hcap
  light_set (vertices h : ℕ) using time,hn,base
  light_set (localBucketCap h : ℕ) using time,hcap,hcapRead,base
  light_set (free+8 : ℕ) using time,base
  light_call (S.metadata.meets (d := d+1) (μ := μ₁) (base := base free) (h := h) (dst := free+8)
    hw (by omega) (by unfold base; omega) hcspace hcword)
    using time,hprime with next μ₂ ⟨hnextVal,hmeta,hkeep₂⟩
  have hparams₂ : Seg μ₂ free (LightLocalParameters.values h) :=
    hparams.of_sameOutside hkeep₂ (Or.inl (by simp [LightLocalParameters.values,LightLocalCounts.values]))
  light_call (S.setup.meets (d := d+1) (μ := μ₂) (base := base free) (h := h)
    hw (by omega) hcspace hcword)
    using time,hprime with schedule μ₃ ⟨hschedule,hdata,hrows,hcandidates,hkeep₃⟩
  have hparams₃ : Seg μ₃ free (LightLocalParameters.values h) := by
    apply hparams₂.congr
    intro i hi
    have hi' : i < 8 := by simpa [LightLocalParameters.values,LightLocalCounts.values] using hi
    exact hkeep₃ _ (by unfold base; omega)
  have hmeta₃ : Seg μ₃ (free+8) (LightLocalCoverMetadata.values (base free) h) := by
    apply hmeta.congr
    intro i hi
    have hi' : i < 12 := by simpa [LightLocalCoverMetadata.values] using hi
    exact hkeep₃ _ (by unfold base; omega)
  light_set (LightLocalCoverMetadata.nextFree (base free) h : ℕ) using time,hnextVal
  refine ⟨rfl,?_,hdata,hrows,hcandidates,?_⟩
  · apply seg_append.mpr
    exact ⟨hparams₃,by simpa [LightLocalParameters.values,LightLocalCounts.values] using hmeta₃⟩
  · intro a ha
    change μ₃ a=μ a
    rw [hkeep₃ _ (by unfold base; omega),hkeep₂ _ (by omega),
      hkeep₁ _ ⟨by unfold base; omega,Or.inl ha⟩]

/-- Keep the original 36-procedure cover table at indices 0 through 35. -/
def program : Program := LightLocalCoverSetup.program++
  [LightLocalParameters.body 37 45 50,LightLocalCounts.body 38,LightSubsetSetup.body 39 43 44,
    LightPascal.buildBody 40 41,fillBody,LightPascal.rowBody 42,LightArray.linearBody,
    powTableBody,LightSubsetAddress.rankBody 44,LightSelectedPrime.body 46 47,sqrtBody,
    LightPrimePool.body 48,LightPrimality.body 49,emodBody,LightSmallDivide.body,
    LightLocalCoverMetadata.body 1 2,body 36 51 0]

def setupProcs : LightLocalCoverSetup.Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨31,8,32,33,34,35,4,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨5,24,29,⟨6,⟨7,12,19,⟨8,9,10,11,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,8,14,15,16,17,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨20,11,21,22,23,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨18,25,28,rfl,⟨26,21,27,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨30,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩

def programProcs : Procs program 52 :=
  ⟨36,51,0,⟨37,45,50,⟨38,39,40,41,42,43,44,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    ⟨46,47,rfl,⟨48,⟨49,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨1,2,rfl,rfl,rfl⟩,setupProcs,rfl⟩

end ThreeSum.LightLocalCoverInit
