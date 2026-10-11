import Submission.ThreeSum.LightLocalCoverRetention
import Submission.ThreeSum.LightGlobalKeys

/-!
# From h to the original local cover and all global output keys

The fixed host obtains every key-constructor parameter from the header
written by the actual local-cover initializer. The original schedule,
candidate histograms, metadata, and input prefix remain available afterwards.
-/

namespace ThreeSum.LightCoverKeys

open Light GlobalEncoding GlobalKeyEnumeration LocalCoverBounds
open LightLocalCoverTables LightLocalCoverLayout LightLocalCoverSchedule

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

/-- h, global block count, and first free address. -/
def body (pCover pKeys : ℕ) : Stmt :=
  .call pCover [v 0,v 2] 3 ;;
  .call pKeys [M (v 2 +' k 8),M (v 2 +' k 9),M (v 2 +' k 10),
    M (v 2 +' k 6),v 1,M (v 2 +' k 12),M (v 2),v 3] 0

def afterCover (free h : ℕ) : ℕ :=
  LightLocalCoverMetadata.nextFree (LightLocalCoverInit.base free) h

def keyHeader (free h J : ℕ) : ℕ :=
  LightGlobalKeys.scratch (afterCover free h) h+LightRadixKeys.offset (LightGlobalKeys.localCount h) J

def time (h J : ℕ) : ℕ := LightLocalCoverInit.time h+LightGlobalKeys.time h J+200
def space (free h J : ℕ) : ℕ :=
  max (LightLocalCoverInit.space free h) (LightGlobalKeys.space (afterCover free h) h J)
def word (h J : ℕ) : ℕ := max (LightLocalCoverInit.word h) (LightGlobalKeys.word h J)

structure Procs (P : Program) (pMain : ℕ) where
  pCover : ℕ
  pKeys : ℕ
  cover : LightLocalCoverInit.Procs P pCover
  keys : LightGlobalKeys.Procs P pKeys
  main : P[pMain]? = some (body pCover pKeys)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets_with_masks {pMain h J free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,J,free] μ (time h J)
      (fun r ν => r=(keyHeader free h J : ℤ) ∧
        ν (keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        Seg ν (keyHeader free h J+1) (globalKeys h J) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps (LightLocalCoverInit.base free) h)
          (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
          (matrixPtr (LightLocalCoverInit.base free) h) ∧
        ScheduleRows ν h (scheduleMaps (LightLocalCoverInit.base free) h) ∧
        (∀ s : Occurrence h, ν (candidates (LightLocalCoverInit.base free) h+s.val)=
          (candidateAt h s : ℤ)) ∧
        (∀ i < outputCount (512*h) h, ν (afterCover free h+i)=
          (LocalMaskGraph.maskAt (512*h) (2*h) i : ℤ)) ∧ Kept μ ν free) := by
  have hcspace : LightLocalCoverInit.space free h ≤ lim.space := (le_max_left _ _).trans hspace
  have hkspace : LightGlobalKeys.space (afterCover free h) h J ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hcword : (LightLocalCoverInit.word h : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hkword : (LightGlobalKeys.word h J : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hbaseNext : free+20 ≤ afterCover free h :=
    LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base free) h
  have hnextSpace : afterCover free h ≤ lim.space := by
    have hs : LightLocalKeyRow.space (LightGlobalKeys.scratch (afterCover free h) h)
        (512*h) (outputCount (512*h) h) ≤ lim.space :=
      (le_max_left _ _).trans hkspace
    unfold LightLocalKeyRow.space LightGlobalKeys.scratch at hs
    omega
  apply Meets.of_body S.main
  unfold body time
  light_call (S.cover.meets (d := d+1) hw (by omega) hcspace hcword)
    with next μ₁ ⟨hnext,hheader,hdata,hrows,hindices,hkeep₁⟩
  have h0 : μ₁ free=(outputCount (512*h) h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 0 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h6 : μ₁ (free+6)=(localPrime h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 6 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h8 : μ₁ (free+8)=(512*h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 8 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h9 : μ₁ (free+9)=(2*h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 9 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h10 : μ₁ (free+10)=(scheduleSize h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 10 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have h12 : μ₁ (free+12)=(scheduleMaps (LightLocalCoverInit.base free) h : ℤ) := by
    simpa [LightLocalCoverInit.values,LightLocalParameters.values,LightLocalCounts.values,
      LightLocalCoverMetadata.values] using hheader 12 (by simp [LightLocalCoverInit.values,
      LightLocalParameters.values,LightLocalCounts.values,LightLocalCoverMetadata.values])
  have hk := S.keys.meets_with_masks (d := d+1) (h := h) (J := J)
    (maps := scheduleMaps (LightLocalCoverInit.base free) h) (free := afterCover free h)
    hw (by omega) hkspace hkword le_rfl
    (fun j hj i hi => (hrows j hj i hi).1) (fun j hj i hi => (hrows j hj i hi).2)
  have haddress (i : ℕ) : ((free : ℤ)+(i : ℤ)).toNat=free+i := by omega
  have h6Read : μ₁ (((free : ℤ)+6).toNat)=(localPrime h : ℤ) := by
    rw [show ((free : ℤ)+6).toNat=free+6 by omega]
    exact h6
  have h8Read : μ₁ (((free : ℤ)+8).toNat)=(512*h : ℤ) := by
    rw [show ((free : ℤ)+8).toNat=free+8 by omega]
    exact h8
  have h9Read : μ₁ (((free : ℤ)+9).toNat)=(2*h : ℤ) := by
    rw [show ((free : ℤ)+9).toNat=free+9 by omega]
    exact h9
  have h10Read : μ₁ (((free : ℤ)+10).toNat)=(scheduleSize h : ℤ) := by
    rw [show ((free : ℤ)+10).toNat=free+10 by omega]
    exact h10
  have h12Read : μ₁ (((free : ℤ)+12).toNat)=(scheduleMaps (LightLocalCoverInit.base free) h : ℤ) := by
    rw [show ((free : ℤ)+12).toNat=free+12 by omega]
    exact h12
  light_call hk using h0,h6Read,h8Read,h9Read,h10Read,h12Read,hnext,afterCover
    with result μ₂ ⟨hr,hcount,hkeys,hmasks,hkeep₂⟩
  refine ⟨hr,hcount,hkeys,LightLocalCoverRetention.header_of_kept hheader hkeep₂,
    LightLocalCoverRetention.data_of_kept hdata hkeep₂,
    LightLocalCoverRetention.rows_of_kept hrows hkeep₂,
    LightLocalCoverRetention.indices_of_kept hindices hkeep₂,hmasks,?_⟩
  intro a ha
  exact (hkeep₂ a (by omega)).trans (hkeep₁ a ha)

/-- Preserve the original host contract while exposing a stronger reusable API above. -/
theorem Procs.meets {pMain h J free : ℕ} {μ : ℕ → ℤ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+J+11 ≤ lim.depth)
    (hspace : space free h J ≤ lim.space) (hword : (word h J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [h,J,free] μ (time h J)
      (fun r ν => r=(keyHeader free h J : ℤ) ∧
        ν (keyHeader free h J)=((LightGlobalKeys.localCount h^J : ℕ) : ℤ) ∧
        Seg ν (keyHeader free h J+1) (globalKeys h J) ∧
        Seg ν free (LightLocalCoverInit.values free h) ∧
        Data ν h (maps (LightLocalCoverInit.base free) h)
          (hist0 (LightLocalCoverInit.base free) h) (hist1 (LightLocalCoverInit.base free) h)
          (matrixPtr (LightLocalCoverInit.base free) h) ∧
        ScheduleRows ν h (scheduleMaps (LightLocalCoverInit.base free) h) ∧
        (∀ s : Occurrence h, ν (candidates (LightLocalCoverInit.base free) h+s.val)=
          (candidateAt h s : ℤ)) ∧ Kept μ ν free) := by
  exact (S.meets_with_masks hw hd hspace hword).mono le_rfl
    (fun _ _ ⟨hr,hc,hkeys,hheader,hdata,hrows,hindices,_,hkeep⟩ =>
      ⟨hr,hc,hkeys,hheader,hdata,hrows,hindices,hkeep⟩)

/-- Preserve the original initializer's procedure indices, then append
the key constructor and this two-call host. -/
def program : Program := LightLocalCoverInit.program++
  [LightGlobalKeys.body 54 57 64,LightSubsetEnumerationSetup.body 55 56,powTableBody,
    LightSubsetEnumeration.body 56,LightLocalKeys.body 58 63,LightLocalKeyRow.body 59 60 62,
    fillBody,LightMaskHashes.body 55 61,LightOneHot.body 61,LightArray.linearBody,copyBody,
    LightRadixKeys.body 64 65,LightRadixRows.body 66,LightReportingAffine.body,body 52 53]

def keyProcs : LightGlobalKeys.Procs program 53 :=
  ⟨54,55,56,57,64,65,66,rfl,rfl,rfl,rfl,
    ⟨58,63,rfl,⟨59,60,55,61,62,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl,rfl,rfl⟩

def coverSetupProcs : LightLocalCoverSetup.Procs program 0 :=
  ⟨1,2,3,rfl,rfl,⟨31,8,32,33,34,35,4,rfl,rfl,rfl,rfl,rfl,rfl,
    ⟨5,24,29,⟨6,⟨7,12,19,⟨8,9,10,11,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨13,8,14,15,16,17,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
      ⟨20,11,21,22,23,18,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,
      ⟨18,25,28,rfl,⟨26,21,27,rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,⟨30,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩

def coverProcs : LightLocalCoverInit.Procs program 52 :=
  ⟨36,51,0,⟨37,45,50,⟨38,39,40,41,42,43,44,⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩,
    ⟨46,47,rfl,⟨48,⟨49,rfl,rfl⟩,rfl⟩,rfl⟩,rfl,rfl⟩,
    ⟨1,2,rfl,rfl,rfl⟩,coverSetupProcs,rfl⟩

def programProcs : Procs program 67 := ⟨52,53,coverProcs,keyProcs,rfl⟩

theorem program_length : program.length=68 := rfl

end ThreeSum.LightCoverKeys
