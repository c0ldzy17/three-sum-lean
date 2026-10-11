import Submission.ThreeSum.LightSourceRetainedStages
import Submission.ThreeSum.LightBlockSourceStages

/-!
# Exact block source stages using the shared original-input histograms

The histogram read condition is the ordinary output of the already costed
`LightSourceHistogram` program. The physical array-index equivalence supplies
its semantic connection to the finite original input set. Once retained, this
same histogram supports every occurrence vector of the corresponding band.
-/

namespace ThreeSum.LightBlockSourceRetainedStages

open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild

set_option maxHeartbeats 1800000

def histogram (p m : ℕ) (shift : ℤ) (v : ℕ → ℤ) (N r : ℕ) : ℕ :=
  LightHistogram.count (fun j => LightSourceResidues.key p m shift (v j)) r N

theorem histogram_le (p m : ℕ) (shift : ℤ) (v : ℕ → ℤ) (N r : ℕ) :
    histogram p m shift v N r ≤ N := LightHistogram.count_le ..

theorem source_eq_left {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    LightSourceRetainedStages.source (modulus h J)
      (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
      (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
      (histogram p (modulus h J) 0 v N) = BlockIndexedQuery.leftSource (p : ℤ) B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (left_value (outputOccurrences q) p B b (fun _ => unindexSet S) v e hinput 0)

theorem source_eq_right {β : Type*} [Fintype β] [DecidableEq β]
    {h J N : ℕ} (p : ℕ) (shift : ℤ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, v i.val = b (e i)) :
    LightSourceRetainedStages.source (modulus h J)
      (fun S => endpointRight (outputOccurrences q) (unindexSet S))
      (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
      (histogram p (modulus h J) shift v N) =
      BlockIndexedQuery.rightSource (p : ℤ) shift B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (right_value (outputOccurrences q) p shift B b (fun _ => unindexSet S) v e hinput 0)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_left {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J N raw flags p table base work cut maskBase : ℕ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hraw : raw+downsetCap (J*(512*h)) cut ≤ base)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ base)
    (htable : table+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ work)
    (hspace : LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) N : ℤ) ≤ lim.word)
    (hinput : ∀ i : Fin N, v i.val = b (e i))
    (hhistRead : ∀ r < modulus h J, μ (table+r) = (histogram p (modulus h J) 0 v N r : ℤ))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointLeft (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if LeftAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [raw,flags,table,base,modulus h J,work,J*(512*h),cut,maskBase,downsetCap (J*(512*h)) cut]
      μ (LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(512*h)) ∧ Kept μ ν base) := by
  have run := C.meets (d := d) (μ := μ) (raw := raw) (flags := flags)
    (table := table) (base := base) (m := modulus h J) (work := work)
    (L := J*(512*h)) (cut := cut) (maskBase := maskBase) (E := endpointBound h J) (B := N)
    (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
    (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
    (histogram p (modulus h J) 0 v N)
    hw hd (modulus_pos h J) hcut hraw hflags htable hdata hmasks hspace hword hrawRead
    (fun S _ => endpointLeft_abs_le (outputOccurrences q) (unindexSet S)) hflagRead
    (fun S _ => by split <;> omega) hhistRead (fun r _ => histogram_le ..)
  rw [source_eq_left p B b q v e hinput] at run
  exact run

theorem meets_right {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceRetainedStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J N raw flags p table base work cut maskBase : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (v : ℕ → ℤ) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h))
    (hraw : raw+downsetCap (J*(512*h)) cut ≤ base)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ base)
    (htable : table+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ work)
    (hspace : LightSourceRetainedStages.space work (J*(512*h)) (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceRetainedStages.word (J*(512*h)) (modulus h J) (endpointBound h J) N : ℤ) ≤ lim.word)
    (hinput : ∀ i : Fin N, v i.val = b (e i))
    (hhistRead : ∀ r < modulus h J, μ (table+r) = (histogram p (modulus h J) shift v N r : ℤ))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [raw,flags,table,base,modulus h J,work,J*(512*h),cut,maskBase,downsetCap (J*(512*h)) cut]
      μ (LightSourceRetainedStages.time (J*(512*h)) cut (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(512*h)) ∧ Kept μ ν base) := by
  have run := C.meets (d := d) (μ := μ) (raw := raw) (flags := flags)
    (table := table) (base := base) (m := modulus h J) (work := work)
    (L := J*(512*h)) (cut := cut) (maskBase := maskBase) (E := endpointBound h J) (B := N)
    (fun S => endpointRight (outputOccurrences q) (unindexSet S))
    (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
    (histogram p (modulus h J) shift v N)
    hw hd (modulus_pos h J) hcut hraw hflags htable hdata hmasks hspace hword hrawRead
    (fun S _ => endpointRight_abs_le (outputOccurrences q) (unindexSet S)) hflagRead
    (fun S _ => by split <;> omega) hhistRead (fun r _ => histogram_le ..)
  rw [source_eq_right p shift B b q v e hinput] at run
  exact run

end ThreeSum.LightBlockSourceRetainedStages
