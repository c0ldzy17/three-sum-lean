import Submission.ThreeSum.LightSourceBucketBuild
import Submission.ThreeSum.SourceBucketView

/-!
# Packed generic residue buckets from four scalar arguments

Only the code-array base, item count, positive residue count, and free pointer are
supplied. The program computes every histogram/offset/cursor/index address
and returns the next free address. Its exact fibers serve both source
reporting and the wanted-record residue join.
-/

namespace ThreeSum.LightSourceBucketSetup

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def hist (base : ℕ) : ℕ := base
def offsets (base M : ℕ) : ℕ := base+M
def cursor (base M : ℕ) : ℕ := base+2*M+1
def flat (base M : ℕ) : ℕ := base+3*M+1
def next (base N M : ℕ) : ℕ := base+3*M+1+N

def body (pBuild : ℕ) : Stmt :=
  .set 4 (v 3 +' v 2) ;;
  .set 5 (v 3 +' k 2 *' v 2 +' k 1) ;;
  .set 6 (v 3 +' k 3 *' v 2 +' k 1) ;;
  .set 7 (v 6 +' v 1) ;;
  .call pBuild [v 0,v 3,v 4,v 5,v 6,v 1,v 2] 8 ;;
  .set 0 (v 7)

def time (N M : ℕ) : ℕ := LightSourceBucketBuild.time N M+200

structure Procs (P : Program) (pMain : ℕ) where
  pBuild : ℕ
  build : LightSourceBucketBuild.Procs P pBuild
  main : P[pMain]? = some (body pBuild)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {keys N M base : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hM : 0 < M)
    (hkeys : keys+N ≤ base) (hspace : next base N M ≤ lim.space)
    (hkey : ∀ i < N, key i < M) (hread : ∀ i < N, μ (keys+i) = (key i : ℤ)) :
    Meets lim P pMain d [keys,N,M,base] μ (time N M)
      (fun r ν => r = (next base N M : ℤ) ∧
        Stored ν key N M (offsets base M) (flat base M) ∧
        (∀ j < M, ν (hist base+j) = (count key j N : ℤ)) ∧ Kept μ ν base) := by
  have hspace' : base+3*M+1+N ≤ lim.space := hspace
  have htwo : (2*(M : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 2*M ≤ lim.space by omega) : (2*(M : ℤ)) ≤ lim.space).trans hw
  have hthree : (3*(M : ℤ)) ≤ lim.word :=
    (by exact_mod_cast (show 3*M ≤ lim.space by omega) : (3*(M : ℤ)) ≤ lim.space).trans hw
  apply Meets.of_body C.main
  unfold body time
  light_set (offsets base M : ℕ) using offsets
  light_set (cursor base M : ℕ) using cursor
  light_set (flat base M : ℕ) using flat
  light_set (next base N M : ℕ) using next,flat
  have hb := C.build.meets (d := d+1) (μ := μ) (keys := keys) (hist := hist base)
    (offsets := offsets base M) (cursor := cursor base M) (flat := flat base M)
    (N := N) (M := M) key hw (by omega) (by unfold offsets; omega)
    (by unfold hist offsets; omega) (Or.inl hkeys) (by unfold offsets cursor; omega)
    (by unfold cursor flat; omega) hspace hkey hread
  light_call hb using LightSourceBucketBuild.time,hist,offsets,cursor,flat,next
    with r ν ⟨stored,counts,kept,_⟩
  light_set (next base N M : ℕ) using next
  exact ⟨rfl,stored,counts,kept⟩

def program : Program :=
  [body 1,LightSourceBucketBuild.body 2 4,histogramBody 3,fillBody,
    LightSourceBucketFromHistogram.body 5 6,LightSourceBucketOffsets.body,LightSourceBucketScatter.body]

def programProcs : Procs program 0 :=
  ⟨1,⟨2,3,4,rfl,rfl,⟨5,6,rfl,rfl,rfl⟩,rfl⟩,rfl⟩

theorem program_length : program.length = 7 := rfl

theorem time_bound (N M : ℕ) : time N M ≤ 500*(N+M+1) := by
  have hb := LightSourceBucketBuild.time_bound N M
  unfold time
  omega

end ThreeSum.LightSourceBucketSetup
