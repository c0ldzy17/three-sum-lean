import Submission.ThreeSum.LightLocalCoverBuild

/-! # A packed layout for the complete local-cover constructor -/

namespace ThreeSum.LightLocalCoverLayout

open Light LocalCoverBounds GlobalEncoding LightLocalCoverSchedule LightLocalCoverTables

def vertices (h : ℕ) : ℕ := LocalMaskGraph.vertexCount (512*h) h
def bitPtr (base h : ℕ) : ℕ := base+vertices h
def maps (base h : ℕ) : ℕ := bitPtr base h+vertices h*(512*h)
def raw0 (base h : ℕ) : ℕ := maps base h+rows h*(2*(512*h))
def raw1 (base h : ℕ) : ℕ := raw0 base h+2*vertices h
def hist0 (base h : ℕ) : ℕ := raw1 base h+2*vertices h
def hist1 (base h : ℕ) : ℕ := hist0 base h+rows h*localPrime h
def matrixPtr (base h : ℕ) : ℕ := hist1 base h+rows h*localPrime h
def work (base h : ℕ) : ℕ := matrixPtr base h+rows h*cols h
def scheduleMaps (base h : ℕ) : ℕ :=
  work base h+LightCoverGreedy.total (rows h) (cols h) (scheduleSize h)
def candidates (base h : ℕ) : ℕ := LightCoverGreedy.out (work base h) (rows h) (cols h)

def space (base h : ℕ) : ℕ :=
  max (LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h))
    (scheduleMaps base h+scheduleSize h*(2*(512*h)))

theorem space_shift (base h : ℕ) : space base h = base+space 0 h := by
  unfold space scheduleMaps work matrixPtr hist1 hist0 raw1 raw0 maps bitPtr LightLocalCoverCandidate.space
  omega

theorem work_le_space (base h : ℕ) : work base h ≤ space base h := by
  have hm := Nat.le_max_left
    (LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h))
    (scheduleMaps base h+scheduleSize h*(2*(512*h)))
  change LightLocalCoverCandidate.space (work base h) (512*h) (vertices h) (localPrime h) ≤ space base h at hm
  unfold LightLocalCoverCandidate.space at hm
  omega

theorem schedule_end_le_space (base h : ℕ) :
    scheduleMaps base h+scheduleSize h*(2*(512*h)) ≤ space base h := Nat.le_max_right ..

theorem build_meets {lim : Limits} {P : Program} {d pMain : ℕ}
    (S : LightLocalCoverBuild.Procs P pMain) {μ : ℕ → ℤ} {base h : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+512*h+7 ≤ lim.depth)
    (hspace : space base h ≤ lim.space) (hword : (LightLocalCoverBuild.word h : ℤ) ≤ lim.word) :
    Meets lim P pMain d
      [512*h,h,localPrime h,rows h,vertices h,localBucketCap h,base,bitPtr base h,maps base h,
        raw0 base h,raw1 base h,hist0 base h,hist1 base h,matrixPtr base h,work base h,
        scheduleSize h,scheduleMaps base h]
      μ (LightLocalCoverBuild.time h)
      (fun r ν => r = (scheduleMaps base h : ℤ) ∧
        Data ν h (maps base h) (hist0 base h) (hist1 base h) (matrixPtr base h) ∧
        ScheduleRows ν h (scheduleMaps base h) ∧
        (∀ s : Occurrence h, ν (candidates base h+s.val) = (candidateAt h s : ℤ)) ∧
        Kept μ ν base) := by
  exact S.meets hw hd ((Nat.le_max_left ..).trans hspace) le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl ((Nat.le_max_right ..).trans hspace) hword

end ThreeSum.LightLocalCoverLayout
