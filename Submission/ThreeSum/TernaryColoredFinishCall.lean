import Submission.ThreeSum.TernaryColoredConcreteFinalCall
import Submission.ThreeSum.TernaryColoredLookupDepth

noncomputable section
namespace ThreeSum.TernaryColoredFinishCall
open Light TernaryConcreteProfile TernaryColoredLoopSetup TernaryArenaLayout
open TernaryLocalParameters TernaryArenaSourceSetup TernaryColoredTerminalReceipt
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

private theorem reassoc {lim : Limits} {P : Program} {d T : ℕ} {s t u : Stmt}
    {σ : State} {Q : State→Prop} (H : Ends lim P d ((s;;t);;u) σ T Q) :
    Ends lim P d (s;;t;;u) σ T Q := by
  obtain ⟨σ',_,he,hc,hq⟩:=H
  cases he with
  | seq hst hu =>
    cases hst with
    | seq hs ht => exact ⟨σ',_,.seq hs (.seq ht hu),by omega,hq⟩

theorem lookup_word {lim : Limits} {d : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hcutoff : P.cutoff≤n)
    (hok : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free d) :
    ((fixedLength P.m+2*fixedLength P.m*(rounds P n)+16:ℕ):ℤ)≤lim.word := by
  have hinputs:=P.inputGuards n hcutoff
  have hr : 0<rounds P n :=
    Nat.clog_pos P.M_gt_one (by have:=hinputs.1;nlinarith)
  have hlen : fixedLength P.m≤fixedLength P.m*(rounds P n) :=
    Nat.le_mul_of_pos_right _ hr
  have hp := (P.allocation.fits n (n^κ) (rounds P n) le_rfl).prefixCells
  have hw := (TernaryArenaAllocationResources.ok P.allocation hok).2.1
  have hbound : fixedLength P.m+2*fixedLength P.m*(rounds P n)+16≤cells P n := by
    dsimp only [TernaryArenaPrefixFootprints.numbers] at hp
    change _≤cells P n at hp
    simp only [Nat.mul_assoc]
    omega
  exact (Int.ofNat_le.mpr hbound).trans hw

/-- The last two assignments and final reporter call consume only the
executed loop's invariant and the actual original preprocessing records. -/
theorem finish {lim : Limits} {d header : ℕ} (P : Profile κ)
    (n free menu c : ℕ) (A B C oldA oldB oldC : List ℤ) (initial ν loc : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]
    (NA : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.av free n) n oldA A)
    (NB : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.bv free n) n oldB B)
    (NC : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.cv free n) n oldC C)
    (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hcutoff : P.cutoff≤n)
    (hok : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free (d+3))
    (Hloop : TernaryArenaLoop.Invariant (TernaryColoredLoopSetup.setup P n free menu c A B C initial)
      (rounds P n) ν)
    (hheader : Seg initial header (LightTernaryColorPreparationProof.header free n (n^κ)
      (rounds P n) (J P n) (q P n) menu A B C))
    (hheaderEnd : header+19≤(input P n free A B C).free)
    (h5 : loc 5=(header:ℤ)) (h6 : loc 6=((input P n free A B C).free:ℤ))
    (h7 : loc 7=(cells P n:ℤ))
    (h10 : loc 10=(addr (input P n free A B C).free (cells P n) 1:ℤ))
    (h12 : loc 12=((P.p^(rounds P n):ℕ):ℤ)) :
    Ends lim P.color d
      (.set 13 (k (fixedLength P.m) *' LightTernaryColoredSolver.H 15) ;;
        .set 14 (k 2 *' v 13) ;;
        .call (240+TernaryExecutable.reportingMain (p:=P.p) P.K) LightTernaryColoredSolver.postArgs 0)
      ⟨loc,ν⟩
      (1000+LightTernaryPreparedPostSelection.time
        (TernaryArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
          (TernaryColoredFinalReady.selected P n free menu c A B C initial)) P.H
        (TernaryColoredFinalReady.cleanup P n free A B C)
        (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial))
      (fun σ=>σ.loc 0=(if ∃i<A.length,∃j<B.length,∃k<C.length,
          C.getD k 0=A.getD i 0+B.getD j 0 then 1 else 0:ℤ) ∧
        Kept initial σ.mem (input P n free A B C).free) := by
  have hinputs:=P.inputGuards n hcutoff
  have T:=TernaryColoredTerminalReceipt.from_invariant P n free menu c A B C initial ν
    hmeta hinputs Hloop
  have R:=TernaryColoredFinalReady.ready P n free menu c A B C initial initial ν
    oldA oldB oldC NA NB NC hmeta hcutoff hok SameOn.refl T
  have hν : Seg ν header (LightTernaryColorPreparationProof.header free n (n^κ)
      (rounds P n) (J P n) (q P n) menu A B C) :=
    hheader.of_kept T.immutable (by simpa only [LightTernaryColorPreparationProof.header,
      List.length_cons,List.length_nil] using hheaderEnd)
  have hfree : (input P n free A B C).free≤lim.space := by have hh:=hok.cells;omega
  have hsix : Seg ν header [(LightTernaryColorPrelude.av free n:ℤ),A.length,
      LightTernaryColorPrelude.bv free n,B.length,LightTernaryColorPrelude.cv free n,C.length] := by
    intro i hi
    have hii : i<6 := by simpa using hi
    interval_cases i <;> exact hν _ (by simp [LightTernaryColorPreparationProof.header])
  have hread : ν (header+15)=(rounds P n:ℤ) := by
    simpa only [LightTernaryColorPreparationProof.header,List.getElem_cons_succ,List.getElem_cons_zero] using
      hν 15 (by simp [LightTernaryColorPreparationProof.header])
  have hlook := TernaryColoredLookupDepth.compute (P:=P.color) (d:=d)
    (len:=fixedLength P.m) loc ν h5 hread (by omega) hok.space
    (lookup_word P n free A B C hcutoff hok)
  apply reassoc
  apply Ends.pieceThen hlook
  intro σ hσ
  rcases hσ with ⟨h13,h14,hkeep,hmem⟩
  rcases σ with ⟨loc',mem'⟩
  dsimp only at hmem
  subst mem'
  have h14' : loc' 14=((2*N P.m (rounds P n):ℕ):ℤ) := by
    simpa only [N,mul_comm] using h14
  have hc:=TernaryColoredConcreteFinalCall.call P n free menu c A B C initial ν loc' header
    hmeta hinputs R T
    ((hkeep 5 (by decide) (by decide)).trans h5)
    ((hkeep 6 (by decide) (by decide)).trans h6)
    ((hkeep 7 (by decide) (by decide)).trans h7)
    ((hkeep 10 (by decide) (by decide)).trans h10)
    ((hkeep 12 (by decide) (by decide)).trans h12) h14' hsix (by omega)
  apply hc.mono (by omega)
  intro σ hσ
  refine ⟨hσ.1,?_⟩
  intro x hx
  exact (hσ.2 x (by unfold addr;omega)).trans (T.immutable x hx)

end ThreeSum.TernaryColoredFinishCall
