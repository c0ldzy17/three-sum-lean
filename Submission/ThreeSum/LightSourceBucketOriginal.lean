import Submission.ThreeSum.LightSourceBucketFromHistogram
import Submission.ThreeSum.LightSourceHistogram

/-!
# Original signed inputs to retained histograms and exact index buckets

The actual code/histogram constructor runs once, followed by linear prefix
and scatter passes. Both source transforms and terminal Cartesian reporting
reuse these same counts and original-index fibers.
-/

namespace ThreeSum.LightSourceBucketOriginal

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pSource pBuckets : ℕ) : Stmt :=
  .call pSource [v 0,v 5,v 1,v 2,v 3,v 6,v 10,v 4] 11 ;;
  .call pBuckets [v 6,v 5,v 7,v 8,v 9,v 1,v 3] 11

def time (N p m U D : ℕ) : ℕ :=
  LightSourceHistogram.time N p m U D+LightSourceBucketFromHistogram.time N m+50

structure Procs (P : Program) (pMain : ℕ) where
  pSource : ℕ
  pBuckets : ℕ
  sourceProcs : LightSourceHistogram.Procs P pSource
  buckets : LightSourceBucketFromHistogram.Procs P pBuckets
  main : P[pMain]? = some (body pSource pBuckets)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {src N p m hist codes offsets cursor flat work U D : ℕ} {shift : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hp : 0 < p) (hm : 0 < m)
    (hsrc : src+N ≤ hist) (hhist : hist+m ≤ codes) (hcodes : codes+N ≤ offsets)
    (hoffsets : offsets+m+1 ≤ cursor) (hcursor : cursor+m ≤ flat) (hflat : flat+N ≤ work)
    (hspace : LightSourceResidues.space work p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceResidues.word p m U D : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [(src : ℤ),(N : ℤ),(p : ℤ),(m : ℤ),shift,(hist : ℤ),(codes : ℤ),
        (offsets : ℤ),(cursor : ℤ),(flat : ℤ),(work : ℤ)]
      μ (time N p m U D) (fun _ ν =>
        Stored ν (fun i => LightSourceResidues.key p m shift (μ (src+i))) N m offsets flat ∧
        (∀ r < m, ν (hist+r) = (count
          (fun i => LightSourceResidues.key p m shift (μ (src+i))) r N : ℤ)) ∧
        (∀ i < N, ν (codes+i) = (LightSourceResidues.key p m shift (μ (src+i)) : ℤ)) ∧
        Kept μ ν hist) := by
  have hwork : work ≤ lim.space := by
    unfold LightSourceResidues.space at hspace
    omega
  apply Meets.of_body C.main
  unfold body time
  have hs := C.sourceProcs.meets (d := d+1) (μ := μ) (src := src) (hist := hist)
    (n := N) (p := p) (m := m) (codes := codes) (work := work) (U := U) (D := D)
    (shift := shift) hw (by omega) hp hm (by omega) hhist (by omega) hspace hshift hword hvalues
  light_call hs using LightSourceHistogram.time,LightSourceResidues.time,
    LightSourceBucketFromHistogram.time,LightSourceBucketOffsets.time,LightSourceBucketScatter.time
    with r ν₁ ⟨keys,counts,kept₁⟩
  have hb := C.buckets.meets (d := d+1) (μ := ν₁) (keys := codes) (hist := hist)
    (offsets := offsets) (cursor := cursor) (flat := flat) (N := N) (M := m)
    (fun i => LightSourceResidues.key p m shift (μ (src+i))) hw (by omega) hcodes (by omega)
    hoffsets hcursor (by omega) (fun i _ => LightSourceResidues.key_lt hm shift (μ (src+i)))
    keys counts
  light_call hb using LightSourceHistogram.time,LightSourceResidues.time,
    LightSourceBucketFromHistogram.time,LightSourceBucketOffsets.time,LightSourceBucketScatter.time
    with r ν₂ ⟨stored,kept₂,_⟩
  refine ⟨stored,?_,?_,?_⟩
  · intro r hr
    exact (kept₂ _ (by omega)).trans (counts r hr)
  · intro i hi
    exact (kept₂ _ (by omega)).trans (keys i hi)
  · intro a ha
    exact (kept₂ a (by omega)).trans (kept₁ a ⟨by omega,Or.inl ha⟩)

def program : Program :=
  [body 1 6,LightSourceHistogram.body 2 4,LightSourceResidues.body 3,emodBody,
    histogramBody 5,fillBody,LightSourceBucketFromHistogram.body 7 8,
    LightSourceBucketOffsets.body,LightSourceBucketScatter.body]

def programProcs : Procs program 0 :=
  ⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,⟨7,8,rfl,rfl,rfl⟩,rfl⟩

theorem program_length : program.length = 9 := rfl

theorem time_bound (N p m U D : ℕ) :
    time N p m U D ≤ 498*N*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+233*m+333 := by
  have hh := LightSourceHistogram.time_bound N p m U D
  have hb := LightSourceBucketFromHistogram.time_bound N m
  unfold time
  nlinarith

end ThreeSum.LightSourceBucketOriginal
