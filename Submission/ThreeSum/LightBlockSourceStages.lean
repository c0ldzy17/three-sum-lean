import Submission.ThreeSum.LightSourceStages
import Submission.ThreeSum.LightBlockSourceBuild
import Submission.ThreeSum.BlockSourceTableLayout

/-!
# Stored suffix stages of the original block source functions

The physical original-input array is related to its finite input set by an
explicit array-index equivalence. The program builds its histogram, gathers
the exact endpoint multiplicities, and constructs every retained suffix stage
of the unchanged `BlockIndexedQuery.leftSource` or `rightSource` function.
-/

namespace ThreeSum.LightBlockSourceStages

open Light BlockEncoding BlockIndex BlockSourceEncoding GlobalEncoding
open SubsetAddress LightBlockSourceBuild

set_option maxHeartbeats 1800000

theorem source_eq_left {β : Type*} [Fintype β] [DecidableEq β]
    {h J N src : ℕ} (μ : ℕ → ℤ) (p : ℕ) (B : Finset β) (b : β → ℤ)
    (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i)) :
    LightSourceStages.source μ src N p (modulus h J) 0
      (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
      (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0) =
      BlockIndexedQuery.leftSource (p : ℤ) B b q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (left_value (outputOccurrences q) p B b (fun _ => unindexSet S)
      (fun i => μ (src+i)) e hinput 0)

theorem source_eq_right {β : Type*} [Fintype β] [DecidableEq β]
    {h J N src : ℕ} (μ : ℕ → ℤ) (p : ℕ) (shift : ℤ) (C : Finset β) (c : β → ℤ)
    (q : GlobalOutput h J) (e : Fin N ≃ C)
    (hinput : ∀ i : Fin N, μ (src+i.val) = c (e i)) :
    LightSourceStages.source μ src N p (modulus h J) shift
      (fun S => endpointRight (outputOccurrences q) (unindexSet S))
      (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0) =
      BlockIndexedQuery.rightSource (p : ℤ) shift C c q := by
  funext S
  exact congrArg (fun n : ℕ => (n : ℤ))
    (right_value (outputOccurrences q) p shift C c (fun _ => unindexSet S)
      (fun i => μ (src+i)) e hinput 0)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets_left {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags p hist base codes work cut maskBase U : ℕ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hsrc : src+N ≤ hist) (hraw : raw+downsetCap (J*(512*h)) cut ≤ hist)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ hist)
    (hhist : hist+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceStages.space work (J*(512*h)) p U 0 (endpointBound h J) ≤ lim.space)
    (hword : (LightSourceStages.word N (J*(512*h)) p (modulus h J) U 0 (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointLeft (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if LeftAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [src,N,raw,flags,p,modulus h J,hist,base,codes,work,0,J*(512*h),cut,maskBase,
        downsetCap (J*(512*h)) cut]
      μ (LightSourceStages.time N (J*(512*h)) cut p (modulus h J) U 0 (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.leftSource (p : ℤ) B b q) (J*(512*h)) ∧ Kept μ ν hist) := by
  have run := C.meets (d := d) (μ := μ) (src := src) (N := N) (raw := raw) (flags := flags)
    (p := p) (m := modulus h J) (hist := hist) (base := base) (codes := codes) (work := work)
    (L := J*(512*h)) (cut := cut) (maskBase := maskBase) (U := U) (D := 0)
    (E := endpointBound h J) (shift := 0)
    (fun S => endpointLeft (outputOccurrences q) (unindexSet S))
    (fun S => if LeftAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
    hw hd hp (modulus_pos h J) hcut hsrc hraw hflags hhist hdata hmasks hcodes
    hspace (by simp) hword hvalues hrawRead
    (fun S _ => endpointLeft_abs_le (outputOccurrences q) (unindexSet S)) hflagRead
    (fun S _ => by split <;> omega)
  rw [source_eq_left μ p B b q e hinput] at run
  exact run.mono le_rfl (fun _ _ h => ⟨h.1,h.2.2⟩)

theorem meets_right {β : Type*} [Fintype β] [DecidableEq β] {pMain : ℕ}
    (C : LightSourceStages.Procs P pMain)
    {μ : ℕ → ℤ} {h J src N raw flags p hist base codes work cut maskBase U D : ℕ} {shift : ℤ}
    (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) (e : Fin N ≃ B)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+8 ≤ lim.depth)
    (hp : 0 < p) (hcut : cut ≤ J*(512*h))
    (hsrc : src+N ≤ hist) (hraw : raw+downsetCap (J*(512*h)) cut ≤ hist)
    (hflags : flags+downsetCap (J*(512*h)) cut ≤ hist)
    (hhist : hist+modulus h J ≤ base)
    (hdata : base+(J*(512*h)+1)*downsetCap (J*(512*h)) cut ≤ maskBase)
    (hmasks : maskBase+downsetCap (J*(512*h)) cut ≤ codes) (hcodes : codes+N ≤ work)
    (hspace : LightSourceStages.space work (J*(512*h)) p U D (endpointBound h J) ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ))
    (hword : (LightSourceStages.word N (J*(512*h)) p (modulus h J) U D (endpointBound h J) : ℤ) ≤ lim.word)
    (hvalues : ∀ i < N, |μ (src+i)| ≤ (U : ℤ))
    (hinput : ∀ i : Fin N, μ (src+i.val) = b (e i))
    (hrawRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (raw+i) = endpointRight (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i))
    (hflagRead : ∀ i < downsetCap (J*(512*h)) cut,
      μ (flags+i) = (if RightAllowed (outputOccurrences q) (BlockSourceTableLayout.sets h J cut i)
        then 1 else 0 : ℕ)) :
    Meets lim P pMain d
      [src,N,raw,flags,p,modulus h J,hist,base,codes,work,shift,J*(512*h),cut,maskBase,
        downsetCap (J*(512*h)) cut]
      μ (LightSourceStages.time N (J*(512*h)) cut p (modulus h J) U D (endpointBound h J))
      (fun _ ν => LightZetaStages.StoredThrough ν base cut
        (BlockIndexedQuery.rightSource (p : ℤ) shift B b q) (J*(512*h)) ∧ Kept μ ν hist) := by
  have run := C.meets (d := d) (μ := μ) (src := src) (N := N) (raw := raw) (flags := flags)
    (p := p) (m := modulus h J) (hist := hist) (base := base) (codes := codes) (work := work)
    (L := J*(512*h)) (cut := cut) (maskBase := maskBase) (U := U) (D := D)
    (E := endpointBound h J) (shift := shift)
    (fun S => endpointRight (outputOccurrences q) (unindexSet S))
    (fun S => if RightAllowed (outputOccurrences q) (unindexSet S) then 1 else 0)
    hw hd hp (modulus_pos h J) hcut hsrc hraw hflags hhist hdata hmasks hcodes
    hspace hshift hword hvalues hrawRead
    (fun S _ => endpointRight_abs_le (outputOccurrences q) (unindexSet S)) hflagRead
    (fun S _ => by split <;> omega)
  rw [source_eq_right μ p shift B b q e hinput] at run
  exact run.mono le_rfl (fun _ _ h => ⟨h.1,h.2.2⟩)

end ThreeSum.LightBlockSourceStages
