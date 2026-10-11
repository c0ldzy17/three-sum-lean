import Submission.ThreeSum.LightReportingBucketPairs
import Submission.ThreeSum.LightSourceBucketSelect
import Submission.ThreeSum.BlockSourceBuckets

/-!
# Physical bucket-test semantics and original-index completeness

The selected offset segment contains exactly the original physical indices
in one residue fiber, with an independent endpoint flag. The literal pair
tester therefore recognizes exactly the compatible original value pairs.
-/

namespace ThreeSum.ReportingHostBucketTest

open Light SourceBuckets LightHistogram LightSourceBucketSelect

set_option maxHeartbeats 1400000
set_option maxRecDepth 7000

def index (μ : ℕ → ℤ) (flat : ℕ) (key : ℕ → ℕ) (N r j : ℕ) : ℕ :=
  (μ (flat+offset key N r+j)).toNat

theorem selected_le (key : ℕ → ℕ) (N r flag : ℕ) :
    countSelected key N r flag ≤ count key r N := by
  unfold countSelected
  split <;> omega

theorem selected_end {key : ℕ → ℕ} {N M r flag : ℕ}
    (hkey : ∀ i < N, key i<M) (hr : r<M) :
    offset key N r+countSelected key N r flag ≤ N := by
  have hend := offset_le hkey (show r+1 ≤ M by omega)
  rw [offset_succ] at hend
  exact (Nat.add_le_add_left (selected_le key N r flag) _).trans hend

theorem selected_read {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag j : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i<M)
    (hr : r<M) (hj : j<countSelected key N r flag) :
    index μ flat key N r j<N ∧
      μ (flat+offset key N r+j)=(index μ flat key N r j : ℤ) := by
  obtain ⟨i,hi,_,_,hread⟩ := H.read_bucket hkey hr (hj.trans_le (selected_le key N r flag))
  simp only [index,hread,Int.toNat_natCast]
  exact ⟨hi,trivial⟩

theorem exists_index_iff {μ : ℕ → ℤ} {key : ℕ → ℕ} {N M offsets flat r flag i : ℕ}
    (H : Stored μ key N M offsets flat) (hkey : ∀ i < N, key i<M) (hr : r<M) :
    (∃ j<countSelected key N r flag, index μ flat key N r j=i) ↔
      flag=1 ∧ i<N ∧ key i=r := by
  by_cases hf : flag=1
  · simp only [countSelected,hf,ite_true,true_and]
    rw [← H.mem_bucketList hkey hr]
    simp only [bucketList,List.mem_ofFn]
    constructor
    · rintro ⟨j,hj,he⟩
      exact ⟨⟨j,hj⟩,he⟩
    · rintro ⟨j,he⟩
      exact ⟨j.val,j.isLt,he⟩
  · simp [countSelected,hf]

def testCount (μ : ℕ → ℤ) (a : ℤ) (left right : ℕ → ℤ)
    (keyL keyR : ℕ → ℕ) (NL NR flatL flatR rL rR flagL flagR : ℕ) : ℕ :=
  LightReportingBucketPairs.count a left right
    (index μ flatL keyL NL rL) (index μ flatR keyR NR rR)
    (countSelected keyR NR rR flagR) (countSelected keyL NL rL flagL)

theorem testCount_le (μ : ℕ → ℤ) (a : ℤ) (left right : ℕ → ℤ)
    (keyL keyR : ℕ → ℕ) (NL NR flatL flatR rL rR flagL flagR : ℕ) :
    testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR ≤
      countSelected keyL NL rL flagL*countSelected keyR NR rR flagR :=
  LightReportingBucketPairs.count_le _ _ _ _ _ _ _

theorem testCount_pos_iff {μ : ℕ → ℤ} {keyL keyR : ℕ → ℕ}
    {NL NR M offsetsL offsetsR flatL flatR rL rR flagL flagR : ℕ}
    (HL : Stored μ keyL NL M offsetsL flatL) (HR : Stored μ keyR NR M offsetsR flatR)
    (hkeyL : ∀ i < NL, keyL i<M) (hkeyR : ∀ j < NR, keyR j<M)
    (hrL : rL<M) (hrR : rR<M) (a : ℤ) (left right : ℕ → ℤ) :
    0<testCount μ a left right keyL keyR NL NR flatL flatR rL rR flagL flagR ↔
      flagL=1 ∧ flagR=1 ∧
        ∃ i<NL, ∃ j<NR, keyL i=rL ∧ keyR j=rR ∧ right j-left i-a=0 := by
  rw [testCount,LightReportingBucketPairs.count_pos_iff]
  constructor
  · rintro ⟨i,hi,j,hj,he⟩
    obtain ⟨hfL,hiL,hki⟩ := (exists_index_iff HL hkeyL hrL).mp ⟨i,hi,rfl⟩
    obtain ⟨hfR,hjR,hkj⟩ := (exists_index_iff HR hkeyR hrR).mp ⟨j,hj,rfl⟩
    exact ⟨hfL,hfR,_,hiL,_,hjR,hki,hkj,he⟩
  · rintro ⟨hfL,hfR,i,hi,j,hj,hki,hkj,he⟩
    obtain ⟨s,hs,hes⟩ := (exists_index_iff HL hkeyL hrL).mpr ⟨hfL,hi,hki⟩
    obtain ⟨t,ht,het⟩ := (exists_index_iff HR hkeyR hrR).mpr ⟨hfR,hj,hkj⟩
    exact ⟨s,hs,t,ht,by simpa only [hes,het] using he⟩

end ThreeSum.ReportingHostBucketTest
