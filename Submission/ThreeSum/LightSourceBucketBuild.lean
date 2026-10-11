import Submission.ThreeSum.LightSourceBucketFromHistogram

/-!
# Actual contiguous buckets from a generic residue-code array

This fixed program constructs its own count histogram, then exact prefix
offsets and an index scatter. No caller-supplied bucket lengths or lists are
assumed. It is shared by source extraction and output-sensitive residue joins.
-/

namespace ThreeSum.LightSourceBucketBuild

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def body (pHistogram pBuckets : ℕ) : Stmt :=
  .call pHistogram [v 0,v 1,v 5,v 6] 7 ;;
  .call pBuckets [v 0,v 1,v 2,v 3,v 4,v 5,v 6] 7

def time (N M : ℕ) : ℕ := histogramTime N M+LightSourceBucketFromHistogram.time N M+50

structure Procs (P : Program) (pMain : ℕ) where
  pHistogram : ℕ
  pFill : ℕ
  pBuckets : ℕ
  histogram : P[pHistogram]? = some (histogramBody pFill)
  fill : P[pFill]? = some fillBody
  buckets : LightSourceBucketFromHistogram.Procs P pBuckets
  main : P[pMain]? = some (body pHistogram pBuckets)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {keys hist offsets cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hkeys : keys+N ≤ offsets) (hhist : hist+M ≤ offsets)
    (hsep : Apart keys N hist M)
    (hoffsets : offsets+M+1 ≤ cursor) (hcursor : cursor+M ≤ flat)
    (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ)) :
    Meets lim P pMain d [keys,hist,offsets,cursor,flat,N,M] μ (time N M)
      (fun _ ν => Stored ν key N M offsets flat ∧
        (∀ r < M, ν (hist+r) = (count key r N : ℤ)) ∧
        Kept μ ν hist ∧ SameOutside μ ν hist (flat+N-hist)) := by
  apply Meets.of_body C.main
  unfold body time
  have hh := histogram_meets (d := d+1) C.histogram C.fill (μ := μ)
    (src := keys) (dst := hist) (n := N) (p := M) key
    hw (by omega) (by omega) (by omega) hsep hread hkey
  light_call hh using histogramTime,countTime,LightSourceBucketFromHistogram.time,
    LightSourceBucketOffsets.time,LightSourceBucketScatter.time with r ν₁ ⟨counts,kept₁⟩
  have hr : ∀ i < N, ν₁ (keys+i) = (key i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hread i hi)
  have hb := C.buckets.meets (d := d+1) (μ := ν₁) (keys := keys) (hist := hist)
    (offsets := offsets) (cursor := cursor) (flat := flat) (N := N) (M := M)
    key hw (by omega) hkeys hhist hoffsets hcursor hspace hkey hr counts
  light_call hb using histogramTime,countTime,LightSourceBucketFromHistogram.time,
    LightSourceBucketOffsets.time,LightSourceBucketScatter.time with r ν₂ ⟨stored,kept₂,same₂⟩
  refine ⟨stored,?_,?_,?_⟩
  · intro r hr
    exact (kept₂ _ (by omega)).trans (counts r hr)
  · intro a ha
    exact (kept₂ a (by omega)).trans (kept₁ a (Or.inl ha))
  · intro a ha
    exact (same₂ a (by omega)).trans (kept₁ a (by omega))

def program : Program :=
  [body 1 3,histogramBody 2,fillBody,LightSourceBucketFromHistogram.body 4 5,
    LightSourceBucketOffsets.body,LightSourceBucketScatter.body]

def programProcs : Procs program 0 := ⟨1,2,3,rfl,rfl,⟨4,5,rfl,rfl,rfl⟩,rfl⟩

theorem program_length : program.length = 6 := rfl

theorem time_bound (N M : ℕ) : time N M ≤ 300*(N+M+1) := by
  unfold time histogramTime countTime fillTime LightSourceBucketFromHistogram.time
    LightSourceBucketOffsets.time LightSourceBucketScatter.time
  omega

end ThreeSum.LightSourceBucketBuild
