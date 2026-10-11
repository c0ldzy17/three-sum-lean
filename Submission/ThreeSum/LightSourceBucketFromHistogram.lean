import Submission.ThreeSum.LightSourceBucketOffsets
import Submission.ThreeSum.LightSourceBucketScatter

/-!
# Retained code/count arrays to exact contiguous original-index buckets

This actual three-procedure program is generic in the residue code function.
It constructs prefix offsets and scatters every physical index exactly once.
The code and count arrays are retained for source stages and later joins.
-/

namespace ThreeSum.LightSourceBucketFromHistogram

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: code array, histogram, offsets, cursor scratch, flat index
output, input count, residue count. -/
def body (pOffsets pScatter : ℕ) : Stmt :=
  .call pOffsets [v 1,v 2,v 3,v 6,v 5] 7 ;;
  .call pScatter [v 0,v 3,v 4,v 5,v 6] 7

def time (N M : ℕ) : ℕ :=
  LightSourceBucketOffsets.time M+LightSourceBucketScatter.time N+80

structure Procs (P : Program) (pMain : ℕ) where
  pOffsets : ℕ
  pScatter : ℕ
  offsets : P[pOffsets]? = some LightSourceBucketOffsets.body
  scatter : P[pScatter]? = some LightSourceBucketScatter.body
  main : P[pMain]? = some (body pOffsets pScatter)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {keys hist offsets cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hkeys : keys+N ≤ offsets) (hhist : hist+M ≤ offsets)
    (hoffsets : offsets+M+1 ≤ cursor) (hcursor : cursor+M ≤ flat)
    (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ))
    (hhistRead : ∀ r < M, μ (hist+r) = (count key r N : ℤ)) :
    Meets lim P pMain d [keys,hist,offsets,cursor,flat,N,M] μ (time N M)
      (fun _ ν => Stored ν key N M offsets flat ∧ Kept μ ν offsets ∧
        SameOutside μ ν offsets (flat+N-offsets)) := by
  have hN : (N : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show N ≤ lim.space by omega)).trans hw
  apply Meets.of_body C.main
  unfold body time
  have ho := LightSourceBucketOffsets.meets (d := d+1) C.offsets (μ := μ)
    (hist := hist) (offsets := offsets) (cursor := cursor) (M := M) (N := N)
    key hw hN hhist hoffsets (by omega) hkey hhistRead
  light_call ho using LightSourceBucketOffsets.time,LightSourceBucketScatter.time
    with r ν₁ ⟨offRead,curRead,kept₁⟩
  have hr : ∀ i < N, ν₁ (keys+i) = (key i : ℤ) := by
    intro i hi
    exact (kept₁ _ (Or.inl (by omega))).trans (hread i hi)
  have hs := LightSourceBucketScatter.meets (d := d+1) C.scatter (μ := ν₁)
    (keys := keys) (cursor := cursor) (flat := flat) (N := N) (M := M)
    key hw (by omega) hcursor hspace hkey hr curRead
  light_call hs using LightSourceBucketOffsets.time,LightSourceBucketScatter.time
    with r ν₂ ⟨indices,_,kept₂⟩
  refine ⟨⟨?_,indices⟩,?_,?_⟩
  · intro r hr
    exact (kept₂ _ (Or.inl (by omega))).trans (offRead r hr)
  · intro a ha
    exact (kept₂ a (Or.inl (by omega))).trans (kept₁ a (Or.inl ha))
  · intro a ha
    exact (kept₂ a (by omega)).trans (kept₁ a (by omega))

def program : Program :=
  [body 1 2,LightSourceBucketOffsets.body,LightSourceBucketScatter.body]

def programProcs : Procs program 0 := ⟨1,2,rfl,rfl,rfl⟩

theorem time_bound (N M : ℕ) : time N M ≤ 220*(N+M+1) := by
  unfold time LightSourceBucketOffsets.time LightSourceBucketScatter.time
  omega

end ThreeSum.LightSourceBucketFromHistogram
