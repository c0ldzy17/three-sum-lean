import Submission.ThreeSum.LightLocalCoverMatrix
import Submission.ThreeSum.LightLocalCoverSchedule
import Submission.ThreeSum.BlockCoefficientRows

/-!
# Exact semantic interfaces for constructed local-cover tables

The concrete matrix constructor uses the unchanged radix enumeration of
the original local maps. Its retained histograms and gathered coefficient
rows are identified with the original occurrence-indexed encoding.
-/

namespace ThreeSum.LightLocalCoverTables

open Light LocalHashMoments LocalCoverBounds GlobalEncoding LightLocalCoverSchedule

def Data (μ : ℕ → ℤ) (h maps hist0 hist1 matrixPtr : ℕ) : Prop :=
  LightLocalCoverMatrix.Tables μ (512*h) (LocalMaskGraph.vertexCount (512*h) h)
    (localPrime h) (localBucketCap h) maps hist0 hist1 matrixPtr
    (LocalMaskGraph.maskAt (512*h) h) (LocalCoverMatrix.bits (512*h) h)
    (fun j => LocalMaskHashes.coeff false (candidate h j))
    (fun j => LocalMaskHashes.coeff true (candidate h j)) (rows h)

def ScheduleRows (μ : ℕ → ℤ) (h dst : ℕ) : Prop :=
  ∀ s < scheduleSize h, ∀ i < 512*h,
    μ (dst+s*(2*(512*h))+i) = (BlockCoefficientRows.mapRow h false s i : ℤ) ∧
    μ (dst+s*(2*(512*h))+512*h+i) = (BlockCoefficientRows.mapRow h true s i : ℤ)

theorem coeff_digit (h j : ℕ) (b : Bool) (i : Fin (512*h)) :
    LocalMaskHashes.coeff b (candidate h j) i.val =
      WeightEnumeration.digit (localPrime h) (2*(512*h)) j (2*i.val+(if b then 1 else 0)) := by
  simp only [LocalMaskHashes.coeff,OneHotMask.extend_fin,candidate,
    WeightEnumeration.decodedWeight_val,WeightEnumeration.coordinateIndex]

theorem entry_eq (h j r : ℕ) :
    LightLocalCoverCandidate.entry (512*h) (LocalMaskGraph.vertexCount (512*h) h)
      (localPrime h) (localBucketCap h) (LocalMaskGraph.maskAt (512*h) h)
      (LocalCoverMatrix.bits (512*h) h)
      (LocalMaskHashes.coeff false (candidate h j))
      (LocalMaskHashes.coeff true (candidate h j)) r = matrix h j r := rfl

theorem Data.matrix_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < cols h) :
    μ (matrixPtr+j*cols h+r) = (matrix h j r : ℤ) := (H j hj).2.2 r hr

theorem Data.counts_read {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) {j r : ℕ} (hj : j < rows h) (hr : r < localPrime h) :
    μ (hist0+j*localPrime h+r) = (LocalCoverMatrix.leftCount (candidate h j) h r : ℤ) ∧
    μ (hist1+j*localPrime h+r) = (LocalCoverMatrix.rightCount (candidate h j) h r : ℤ) :=
  (H j hj).2.1 r hr

theorem Data.selected_counts {μ : ℕ → ℤ} {h maps hist0 hist1 matrixPtr : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) (s : Occurrence h) {r : ℕ} (hr : r < localPrime h) :
    μ (hist0+candidateAt h s*localPrime h+r) =
      (HashFamily.bucketSize (LocalGraph.leftVertices (512*h) h) (mapAt h s) (r : LocalField h) : ℤ) ∧
    μ (hist1+candidateAt h s*localPrime h+r) =
      (HashFamily.bucketSize (LocalGraph.rightVertices (512*h) h) (mapAt h s) (r : LocalField h) : ℤ) := by
  have hc := H.counts_read (candidateAt_lt h s) hr
  rw [leftCount_candidateAt h s hr,rightCount_candidateAt h s hr] at hc
  exact hc

theorem Data.of_kept {μ ν : ℕ → ℤ} {h maps hist0 hist1 matrixPtr cut : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr) (K : Kept μ ν cut)
    (hmaps : maps+rows h*(2*(512*h)) ≤ cut)
    (hhist0 : hist0+rows h*localPrime h ≤ cut)
    (hhist1 : hist1+rows h*localPrime h ≤ cut)
    (hmatrix : matrixPtr+rows h*cols h ≤ cut) : Data ν h maps hist0 hist1 matrixPtr := by
  intro j hj
  obtain ⟨hc,hh,he⟩ := H j hj
  have hm := Nat.mul_le_mul_right (2*(512*h)) (show j+1 ≤ rows h by omega)
  have hp := Nat.mul_le_mul_right (localPrime h) (show j+1 ≤ rows h by omega)
  have hx := Nat.mul_le_mul_right (cols h) (show j+1 ≤ rows h by omega)
  simp only [Nat.add_mul,one_mul] at hm hp hx
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [K _ (by omega),K _ (by omega)]
    exact hc i hi
  · intro r hr
    rw [K _ (by omega),K _ (by omega)]
    exact hh r hr
  · intro r hr
    change ν (matrixPtr+j*cols h+r) = _
    rw [K _ (by change r < cols h at hr; omega)]
    exact he r hr

theorem Data.gathered_schedule {μ ν : ℕ → ℤ} {h maps hist0 hist1 matrixPtr dst : ℕ}
    (H : Data μ h maps hist0 hist1 matrixPtr)
    (hcopy : ∀ s < scheduleSize h, ∀ a < 2*(512*h),
      ν (dst+s*(2*(512*h))+a) = μ (maps+(indices h).getD s 0*(2*(512*h))+a)) :
    ScheduleRows ν h dst := by
  intro s hs i hi
  let o : Occurrence h := ⟨s,hs⟩
  have hc := ((H (candidateAt h o) (candidateAt_lt h o)).1).decodedWeight ⟨i,hi⟩
  change
    μ (maps+candidateAt h o*(2*(512*h))+i) = ((candidate h (candidateAt h o) (⟨i,hi⟩,false)).val : ℤ) ∧
    μ (maps+candidateAt h o*(2*(512*h))+512*h+i) = ((candidate h (candidateAt h o) (⟨i,hi⟩,true)).val : ℤ) at hc
  rw [candidateAt_mapAt h o] at hc
  rw [BlockCoefficientRows.mapRow_fin false o ⟨i,hi⟩,
    BlockCoefficientRows.mapRow_fin true o ⟨i,hi⟩]
  constructor
  · rw [hcopy s hs i (by omega)]
    exact hc.1
  · have he := hcopy s hs (512*h+i) (by omega)
    rw [← Nat.add_assoc,← Nat.add_assoc] at he
    rw [he]
    exact hc.2

end ThreeSum.LightLocalCoverTables
