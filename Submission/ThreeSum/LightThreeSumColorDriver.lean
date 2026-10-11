import Submission.ThreeSum.LightColorScanHost
import Submission.ThreeSum.ReportingHostRelocation

/-!
# Close the actual color decoder and scan around a concrete color program

The supplied program stays at its original indices. Four actual procedures
are appended: the six-cell decoder, scalar division, recursive short-circuit
scan, and parameter-header reader. The resulting program can then be
relocated by the already verified general relocation theorem.
-/

namespace ThreeSum.LightThreeSumColorDriver

open Light ColorParameters LightColorParametersCosts

set_option maxHeartbeats 2000000
set_option maxRecDepth 14000

def extra (colorProgram : Program) (pColor : ℕ) : Program :=
  [LightColorParameters.body (colorProgram.length+1),LightSmallDivide.body,
    LightColorScan.body (colorProgram.length+2) colorProgram.length pColor,
    LightColorScanHost.body (colorProgram.length+2)]

def program (colorProgram : Program) (pColor : ℕ) : Program := colorProgram++extra colorProgram pColor

theorem program_length (colorProgram : Program) (pColor : ℕ) :
    (program colorProgram pColor).length=colorProgram.length+4 := by simp [program,extra]

def procs (colorProgram : Program) (pColor : ℕ) :
    LightColorScanHost.Procs (program colorProgram pColor) (colorProgram.length+3) where
  pScan := colorProgram.length+2
  scan := {
    pParameters := colorProgram.length
    pDivide := colorProgram.length+1
    pColor := pColor
    main := by apply getElem?_append_length_add; rfl
    parameters := by
      change (colorProgram++extra colorProgram pColor)[colorProgram.length+0]?=_
      apply getElem?_append_length_add
      rfl
    divide := by apply getElem?_append_length_add; rfl }
  main := by apply getElem?_append_length_add; rfl

theorem program_meets {lim : Limits} {colorProgram : Program} {pColor : ℕ}
    {src n params row colorTime colorDepth d : ℕ} (x : Fin n→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : row+6≤lim.space)
    (hsrc : src≤row) (hparams : params<row)
    (hword : (LightColorScanHost.word n : ℤ)≤lim.word)
    (hd : d+count (width n)+colorDepth+4≤lim.depth)
    (hread : μ params=(Scales.inputBits n : ℤ))
    (hcolor : ∀ (i : ℕ) (hi : i<count (width n)) (ν : ℕ→ℤ),
      Kept μ ν row → Seg ν row (fields (parameter hi)) →
      ∀ dd : ℕ, dd+colorDepth≤lim.depth →
      Meets lim colorProgram pColor dd [src,n,params,row,row+6] ν colorTime
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ ColorClassLists.witness (parameter hi) x) ∧ Kept ν ξ row)) :
    Meets lim (program colorProgram pColor) (colorProgram.length+3) d
      [src,n,params,row] μ (LightColorScanHost.time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧ (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ row) := by
  apply (procs colorProgram pColor).meets x μ hw hspace hsrc hparams hword hd hread
  intro i hi ν hkeep hrow dd hdepth
  exact (hcolor i hi ν hkeep hrow dd hdepth).append (extra colorProgram pColor)

end ThreeSum.LightThreeSumColorDriver
