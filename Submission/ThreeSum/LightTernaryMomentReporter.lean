import Submission.ThreeSum.TernaryMomentDriverResources
import Submission.ThreeSum.LightTernaryPhysicalMomentBatch

/-! The actual reporting program builds every signed moment channel from the
original surviving source arrays and runs the physical-support zero detector. -/
noncomputable section
namespace ThreeSum.LightTernaryMomentReporter
open Light TernaryMomentSchedule
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 100000

def driver {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  LightTernaryCertifiedMomentDriver.program S (2*H+1)

def body (pDriver pDetector : ℕ) : Stmt :=
  .call pDriver (LightTernarySourceCountHost.callArgs 6 115) 121 ;;
  .call pDetector [v 3,v 5,v 0,v 1,v 4,v 2] 0

def libraries {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  ReportingHostRelocation.program (driver S H) (LightTernaryMomentBatch.program H)

def program {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  libraries S H++[body (127*(channels (2*H+1)).length+1) (driver S H).length]

@[simp] theorem driver_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    (driver S H).length=127*(channels (2*H+1)).length+2 := by
  exact LightTernaryCertifiedMomentDriver.program_length S (2*H+1)

@[simp] theorem program_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    (program S H).length=127*(channels (2*H+1)).length+7 := by
  simp [program,libraries,ReportingHostRelocation.program,LightTernaryMomentBatch.program]

def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  let base := LightTernaryMomentDriver.program xl yl zl xr yr zr
    (channels (2*H+1)) (2*H+1) 115
  ReportingHostRelocation.program base (LightTernaryMomentBatch.program H)++
    [body (127*(channels (2*H+1)).length+1) (127*(channels (2*H+1)).length+2)]

/-- Compact source lengths, scalar/hash pointers, native dimensions and all
workspace parameters are runtime arguments. The program text is fixed by
the six literal local tables and the fixed physical support order. -/
theorem program_eq_closed {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H=closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by
  unfold program
  rw [driver_length]
  simp only [libraries,driver,LightTernaryCertifiedMomentDriver.program,
    LightTernaryMomentChannelFactory.backend_length,Nat.reduceAdd,closedProgram]

def args {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (originalA originalCount scratch originalB originalC matrix : ℕ) : List ℤ :=
  [(originalA : ℤ),originalCount,scratch,S.front.records,matrix,S.front.count]++
    LightTernaryMomentChannelFactory.args S originalB originalC matrix

def time {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : ℕ :=
  LightTernaryCertifiedMomentDriver.time S (2*H+1)+LightTernaryMomentBatch.time H S.front.count+200

theorem meets {lim : Limits} {N H d originalA originalCount scratch originalB originalC matrix
      a b U W detectorU : ℕ}
    (S : TernarySourceCountExecutionFactory.Setup N) (μ : ℕ→ℤ) (A B C : ℕ→ℤ) (position : ℕ→ℕ)
    (R : LightTernaryCertifiedMomentDriver.Resources S lim (d+1) originalB originalC matrix
      (2*H+1) a b U W μ B C)
    (hAarray : originalA+originalCount≤matrix)
    (hmatrix : matrix+(2*H+1)*S.front.count≤scratch)
    (hspace : scratch+(2*H+1)≤lim.space)
    (hpositions : ∀ i<S.front.count, position i<originalCount)
    (hpositionRead : ∀ i<S.front.count, μ (S.front.records+3*i)=(position i : ℤ))
    (hAread : ∀ i<originalCount, μ (originalA+i)=A i)
    (hAabs : ∀ i<originalCount, |A i|≤(detectorU : ℤ))
    (hword : max (detectorU : ℤ) (LightMomentDeterminant.wordBound detectorU H)≤lim.word)
    (hsupport : ∀ i<S.front.count,
      (TernaryPairedSupport.physicalSupport (TernaryNativePairMoments.mode (S := S) (i := i) B C)).card≤H)
    (hmabs : ∀ i<S.front.count, ∀ k≤2*H,
      |∑ p : TernaryNativePairMoments.Pair S i,
        TernaryNativePairMoments.mass S i p*TernaryNativePairMoments.mode B C p^k|≤(detectorU : ℤ)) :
    Meets lim (program S H) ((driver S H).length+4) d
      (args S originalA originalCount scratch originalB originalC matrix) μ (time S H)
      (fun r ν => r=(if ∃ i<S.front.count, ∃ p : TernaryNativePairMoments.Pair S i,
          TernaryNativePairMoments.mode B C p=A (position i) then 1 else 0 : ℤ) ∧
        Kept μ ν matrix) := by
  have hdriver : Meets lim (program S H) (127*(channels (2*H+1)).length+1) (d+1)
      (LightTernaryMomentChannelFactory.args S originalB originalC matrix) μ
      (LightTernaryCertifiedMomentDriver.time S (2*H+1))
      (fun _ ν => (∀ k<2*H+1, ∀ i<S.front.count,
        ν (matrix+k*S.front.count+i)=∑ p : TernaryNativePairMoments.Pair S i,
          TernaryNativePairMoments.mass S i p*TernaryNativePairMoments.mode B C p^k) ∧ Kept μ ν matrix) := by
    have hr := R.run.append ((LightTernaryMomentBatch.program H).map
      (ReportingHostRelocation.relocate (driver S H).length)++
        [body (127*(channels (2*H+1)).length+1) (driver S H).length])
    simpa only [program,libraries,ReportingHostRelocation.program,List.append_assoc,driver] using hr
  have hmain : (program S H)[(driver S H).length+4]?=
      some (body (127*(channels (2*H+1)).length+1) (driver S H).length) := by
    unfold program libraries ReportingHostRelocation.program
    rw [List.getElem?_append_right (by simp [LightTernaryMomentBatch.program])]
    simp [LightTernaryMomentBatch.program]
  have hargv : (LightTernaryMomentChannelFactory.args S originalB originalC matrix).length=115 := by
    simp [LightTernaryMomentChannelFactory.args,LightTernaryMomentChannelStep.args,
      LightTernaryMomentChannelFactory.backend_length]
  have hreads : LightTernarySourceCountHost.Reads
      (frame (args S originalA originalCount scratch originalB originalC matrix)) 6
      (LightTernaryMomentChannelFactory.args S originalB originalC matrix) := by
    intro i hi
    unfold args frame
    rw [List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_sub_cancel_left]
  apply Meets.of_body hmain
  unfold body time
  refine Ends.callThen hdriver ?_
    (ha := ⟨LightTernarySourceCountHost.callArgs_safe _ _ _ _,
      LightTernarySourceCountHost.callArgs_values _ _ _ _ _ hargv hreads⟩)
    (hd := by have := R.hd; omega) (hT := by rw [LightTernarySourceCountHost.callArgs_cost]; omega)
  intro result ν ⟨hm,hkeep⟩
  have hrecords : S.front.records+3*S.front.count≤matrix := R.himmutable.frontRecords
  have hpositionν : ∀ i<S.front.count, ν (S.front.records+3*i)=(position i : ℤ) := by
    intro i hi
    have hh := Nat.mul_le_mul_left 3 (show i+1≤S.front.count by omega)
    simp only [Nat.mul_add,Nat.mul_one] at hh
    exact (hkeep _ (by omega)).trans (hpositionRead i hi)
  have hAν : ∀ i<originalCount, ν (originalA+i)=A i := by
    intro i hi
    exact (hkeep _ (by omega)).trans (hAread i hi)
  have hs : ∀ i<S.front.count,
      (TernaryPhysicalMomentSupport.support
        (TernaryNativePairMoments.mode (S := S) (i := i) B C)).card≤H := by
    intro i hi
    rw [TernaryNativePairMoments.support_eq]
    exact hsupport i hi
  have hd : d+1+1<lim.depth := by have := R.hd; omega
  have hb := LightTernaryPhysicalMomentBatch.meets (d := d+1)
    (records := S.front.records) (count := S.front.count) (originalA := originalA)
    (originalCount := originalCount) (matrix := matrix) (scratch := scratch) (U := detectorU)
    (LightTernaryMomentBatch.procs H)
    (TernaryNativePairMoments.Pair S)
    (fun i => TernaryNativePairMoments.mode (S := S) (i := i) B C)
    (TernaryNativePairMoments.mass S) position A ν R.hw hd (by omega) (by omega) hmatrix hspace
    hpositions hpositionν hAν hAabs hword (fun i hi => TernaryNativePairMoments.mass_positive S i)
    hs hmabs (by intro i hi k hk; exact hm k (by omega) i hi)
  have hr := (ReportingHostRelocation.meets hb (driver S H)).append
    [body (127*(channels (2*H+1)).length+1) (driver S H).length]
  have hr' : Meets lim (program S H) (driver S H).length (d+1)
      [S.front.records,S.front.count,originalA,originalCount,matrix,scratch] ν
      (LightTernaryMomentBatch.time H S.front.count)
      (fun r ξ => r=(if ∃ i<S.front.count, ∃ p : TernaryNativePairMoments.Pair S i,
        TernaryNativePairMoments.mode B C p=A (position i) then 1 else 0 : ℤ) ∧ Kept ν ξ scratch) := by
    simpa only [Nat.add_zero,program,libraries] using hr
  refine Ends.callLast hr' ?_ (ha := by light_side [args])
    (hd := by have := R.hd; omega)
    (hT := by rw [LightTernarySourceCountHost.callArgs_cost]; light_time)
  intro r ξ ⟨hflag,hkeepDetector⟩
  refine ⟨hflag,?_⟩
  intro x hx
  exact (hkeepDetector x (by omega)).trans (hkeep x hx)

end ThreeSum.LightTernaryMomentReporter
