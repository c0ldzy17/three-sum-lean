import Submission.ThreeSum.LightThreeSumColorDriverBounded

/-!
# Initialize parameters once and execute the complete color family

The public arguments are [source,n,free]. The nineteen-cell parameter
record starts at free; the reusable six-cell color row starts at free+19;
the concrete selected-color program receives free+25 as its work boundary.
-/

namespace ThreeSum.LightThreeSumFastDriver

open Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 18000

def row (free : ℕ) : ℕ := free+19
def normalizedFree (free : ℕ) : ℕ := free+25

def body (pScan : ℕ) : Stmt :=
  .set 3 (v 2 +' k 19) ;;
  .call 0 [v 1,v 2,v 3] 4 ;;
  .call pScan [v 0,v 1,v 2,v 3] 0

def libraries (colorProgram : Program) (pColor : ℕ) : Program :=
  ReportingHostRelocation.program LightParameterInit.program
    (LightThreeSumColorDriver.program colorProgram pColor)

def program (colorProgram : Program) (pColor : ℕ) : Program :=
  libraries colorProgram pColor++[body (colorProgram.length+25)]

def time (colorTime n : ℕ) : ℕ :=
  LightParameterInit.time n+LightColorScanHost.time colorTime n+500

theorem libraries_length (colorProgram : Program) (pColor : ℕ) :
    (libraries colorProgram pColor).length=colorProgram.length+26 := by
  simp only [libraries,ReportingHostRelocation.program,List.length_append,List.length_map,
    LightThreeSumColorDriver.program_length]
  change 22+(colorProgram.length+4)=colorProgram.length+26
  omega

theorem program_length (colorProgram : Program) (pColor : ℕ) :
    (program colorProgram pColor).length=colorProgram.length+27 := by
  simp only [program,List.length_append,List.length_cons,List.length_nil,libraries_length]

theorem main_lookup (colorProgram : Program) (pColor : ℕ) :
    (program colorProgram pColor)[colorProgram.length+26]?=some (body (colorProgram.length+25)) := by
  have hh : (libraries colorProgram pColor++[body (colorProgram.length+25)])[(libraries colorProgram pColor).length+0]?=
      some (body (colorProgram.length+25)) := by
    apply getElem?_append_length_add
    rfl
  simpa only [program,libraries_length,Nat.add_zero] using hh

theorem normalizedFree_eq (free : ℕ) : row free+6=normalizedFree free := by
  unfold row normalizedFree
  omega

theorem program_meets {lim : Limits} {colorProgram : Program} {pColor : ℕ}
    {colorNeed : ℕ→ℕ→Need} {src n free U colorTime d : ℕ}
    (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (H : (ThreeSumColorDriverResources.fullNeed colorNeed n U).Ok lim free d)
    (hsrc : src+n≤free) (hinput : Seg μ src (List.ofFn x))
    (hcolor : LightThreeSumColorDriver.ColorLaw lim colorProgram pColor colorNeed
      src n free (row free) U colorTime x) :
    Meets lim (program colorProgram pColor) (colorProgram.length+26) d [src,n,free] μ (time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) := by
  have hinitOk := ThreeSumColorDriverResources.parameters_of_full_ok H
  have hscanOk := ThreeSumColorDriverResources.scan_of_full_ok H
  have hspace := (ThreeSumColorDriverResources.scan_bounds_of_ok hscanOk).1
  have hw := H.space
  have hd := (ThreeSumParameterResources.resources_of_ok hinitOk).2.2
  apply Meets.of_body (main_lookup colorProgram pColor)
  unfold body time
  light_set (row free : ℕ) using row
  have hinit := (ThreeSumParameterResources.program_meets (μ := μ) hinitOk).append
    ((LightThreeSumColorDriver.program colorProgram pColor).map
      (ReportingHostRelocation.relocate LightParameterInit.program.length)++[body (colorProgram.length+25)])
  change Meets lim (program colorProgram pColor) 0 (d+1) _ μ _ _ at hinit
  light_call hinit using ThreeSumParameterResources.work,row with modulus ν ⟨_,hparams,hkeptInit⟩
  have hkeep := ThreeSumParameterResources.kept_of_post hkeptInit
  have hread := hinput.of_kept hkeep (by simpa only [List.length_ofFn] using hsrc)
  have hscan := LightThreeSumColorDriver.program_meets_bounded x ν hscanOk
    (by omega) (by omega) hread hparams hcolor
  have hscanRun := (ReportingHostRelocation.meets hscan LightParameterInit.program).append
    [body (colorProgram.length+25)]
  have hentry : LightParameterInit.program.length+(colorProgram.length+3)=colorProgram.length+25 := by
    change 22+(colorProgram.length+3)=colorProgram.length+25
    omega
  rw [hentry] at hscanRun
  change Meets lim (program colorProgram pColor) (colorProgram.length+25) (d+1) _ ν _ _ at hscanRun
  light_call hscanRun using row with result ξ ⟨hbool,hresult,hkeptScan⟩
  exact ⟨hbool,hresult,fun a ha => (hkeptScan a (by omega)).trans (hkeep a ha)⟩

end ThreeSum.LightThreeSumFastDriver
