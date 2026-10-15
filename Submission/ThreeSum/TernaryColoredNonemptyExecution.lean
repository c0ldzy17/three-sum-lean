import Submission.ThreeSum.TernaryColoredLoopCall
import Submission.ThreeSum.TernaryColoredFinishCall
import Submission.ThreeSum.TernaryColoredPreparationFields
import Submission.ThreeSum.TernaryColoredInitializationResources
import Submission.ThreeSum.TernaryColoredProgramIdentity

noncomputable section
namespace ThreeSum.TernaryColoredNonemptyExecution
open Light TernaryConcreteProfile TernaryColoredLoopSetup TernaryArenaLayout TernaryLocalParameters
open LightTernaryColoredSolver LightTernaryColoredInitializationProof
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def tail (P : Profile κ) : Stmt :=
  .call 237 (loopArgs P.m P.F P.p (fixedAlpha P.m 2) (TernaryArenaSourceSetup.alphaRank P.m)
    (TernaryCodeSemantics.address P.output.val) (4^fixedLength P.m) (P.p^(2*P.K)) P.drift P.scale) 12 ;;
  .set 13 (k (fixedLength P.m) *' H 15) ;; .set 14 (k 2 *' v 13) ;;
  .call (240+TernaryExecutable.reportingMain (p:=P.p) P.K) postArgs 0

def postTime (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))] :=
  LightTernaryPreparedPostSelection.time
    (TernaryArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
      (TernaryColoredFinalReady.selected P n free menu c A B C initial)) P.H
    (TernaryColoredFinalReady.cleanup P n free A B C)
    (TernaryColoredTerminalReceipt.keysB P n free menu c A B C initial)
    (TernaryColoredTerminalReceipt.keysC P n free menu c A B C initial)

theorem ends {lim : Limits} {d : ℕ} (P : Profile κ) (n free menu c : ℕ)
    (A B C oldA oldB oldC : List ℤ) (initial : ℕ→ℤ) (locals : List ℤ)
    [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]
    (hcutoff : P.cutoff≤n) (hneed : (P.colorNeed n (n^κ)).Ok lim free d)
    (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (NA : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.av free n) n oldA A)
    (NB : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.bv free n) n oldB B)
    (NC : LightTernaryColorPrelude.Normalized initial (LightTernaryColorPrelude.cv free n) n oldC C)
    (hheader : Seg initial (LightTernaryColorPreparation.headerAt free n (LightColorParametersCosts.width n))
      (LightTernaryColorPreparationProof.header free n (n^κ) (rounds P n) (J P n) (q P n) menu A B C))
    (hOriginals : TernaryArenaPrefixInputs.Originals (input P n free A B C) (arrays P n free menu A B C)
      (q P n*q P n) P.radix P.radix n
      (TernaryComputedExtensionMenu.functional (p:=P.p) (c:=c) (dim_pos P n))
      (TernaryArenaFamilyBudget.seedAt (TernaryComputedExtensionMenu.seeds (p:=P.p) (d:=dim P n) (c:=c)))
      (TernaryArenaSelectedSigned.left (n^κ) P.radix (J P n) (fun i=>B.getD i 0))
      (TernaryArenaSelectedSigned.right (n^κ) P.radix (J P n) (fun i=>C.getD i 0))
      (TernaryArenaSelectedSigned.requester (n^κ) P.radix (J P n) (fun i=>A.getD i 0)) initial)
    (h1 : frame locals 1=(n:ℤ))
    (h5 : frame locals 5=(LightTernaryColorPreparation.headerAt free n (LightColorParametersCosts.width n):ℤ)) :
    let S:=setup P n free menu c A B C initial
    Ends lim P.color d (initChunk P.p (4^fixedLength P.m) P.F (tail P)) ⟨frame locals,initial⟩
      (LightTernaryArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+
        S.initTime+postTime P n free menu c A B C initial+8000)
      (fun σ=>σ.loc 0=(if ∃i<A.length,∃j<B.length,∃k<C.length,
          C.getD k 0=A.getD i 0+B.getD j 0 then 1 else 0:ℤ) ∧
        Kept initial σ.mem (input P n free A B C).free) := by
  let S:=setup P n free menu c A B C initial
  let header:=LightTernaryColorPreparation.headerAt free n (LightColorParametersCosts.width n)
  let fn:=TernaryColoredPreparationFields.field P n free menu A B C
  let PT:=postTime P n free menu c A B C initial
  let Q:=fun σ : State=>σ.loc 0=(if ∃i<A.length,∃j<B.length,∃k<C.length,
      C.getD k 0=A.getD i 0+B.getD j 0 then 1 else 0:ℤ) ∧ Kept initial σ.mem S.input.free
  have Bnd:=TernaryColoredInitializationResources.bounds P n free A B C hneed hmeta
  have hinputs:=P.inputGuards n hcutoff
  have HR:=ready (depth:=d+2) P n free menu c A B C initial Bnd.hardware hmeta hinputs hOriginals
  have hEnd:=TernaryColoredPreparationFields.header_before P n free A B C
  change header+19≤(input P n free A B C).free at hEnd
  have hspace : (input P n free A B C).free≤lim.space := by have:=Bnd.hardware.cells;omega
  have hread:=TernaryColoredPreparationFields.reads hheader
  have next : ∀σ, Initialized P.allocation.D P.allocation.E P.K P.radix (P.p^(2*P.K)) P.drift P.scale
      n (n^κ) S.input.free (q P n) (J P n) (A.length*2^(J P n))
      (TernaryColoredLoopCall.initValues P n free menu A B C) (frame locals) σ.loc initial σ.mem →
      Ends lim P.color d (tail P) σ (S.initTime+PT+2000) Q := by
    intro σ HI
    have hloc5 : σ.loc 5=(header:ℤ) := HI.header.trans h5
    have hR : σ.mem (header+15)=(rounds P n:ℤ) :=
      (HI.kept _ (by change header+15<(input P n free A B C).free;omega)).trans (hread 15 (by decide))
    have hJ : σ.mem (header+16)=(J P n:ℤ) :=
      (HI.kept _ (by change header+16<(input P n free A B C).free;omega)).trans (hread 16 (by decide))
    have hc:=TernaryColoredLoopCall.call (d:=d) P n free menu c A B C initial (frame locals) σ.loc σ.mem
      HI HR hloc5 hR hJ (by omega)
    unfold tail
    apply Ends.pieceThen hc (hT:=by change 25+S.initTime≤S.initTime+PT+2000;omega)
    intro ω hw
    rcases hw with ⟨h12,hInv,hkeep⟩
    have hf:=TernaryColoredFinishCall.finish (d:=d) P n free menu c A B C oldA oldB oldC initial ω.mem ω.loc
      NA NB NC hmeta hcutoff (Bnd.hardware.mono le_rfl le_rfl (by omega)) hInv hheader hEnd
      ((hkeep 5 (by decide)).trans hloc5) ((hkeep 6 (by decide)).trans HI.arena)
      ((hkeep 7 (by decide)).trans HI.capacity) ((hkeep 10 (by decide)).trans HI.liveHost) h12
    exact hf.mono (by change 1000+PT≤S.initTime+PT+2000-(25+S.initTime);omega) (fun _ h=>h)
  have hi:=LightTernaryColoredInitializationProof.ends_then
    (radix:=P.radix) (D:=P.allocation.D) (E:=P.allocation.E) (K:=P.K) (bDigit:=P.radix)
    (a:=P.p^(2*P.K)) (b:=P.drift) (scaleBase:=P.scale) (p:=P.p) (R:=4^fixedLength P.m) (F:=P.F)
    S.raws S.words S.mapCodes
    ((TernaryExecutable.leftRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native false P.maps))
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native true P.maps))
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    (TernaryColoredProgramIdentity.suffix P) locals initial fn h1 h5 hread hEnd
    (by have:=hinputs.1;omega) P.radix_gt_one.le hneed.space Bnd.finish Bnd.inputWord Bnd.exponentWord
    Bnd.menu Bnd.constants Bnd.budgetWord Bnd.depthBound (tail P) Q
    (fun σ h=>by
      change Ends lim (TernaryColoredProgramIdentity.libraries P++TernaryColoredProgramIdentity.suffix P)
        d (tail P) σ (S.initTime+PT+2000) Q
      rw [←TernaryColoredProgramIdentity.color_eq]
      exact next σ h)
  change Ends lim (TernaryColoredProgramIdentity.libraries P++TernaryColoredProgramIdentity.suffix P) _ _ _ _ _ at hi
  rw [←TernaryColoredProgramIdentity.color_eq] at hi
  exact hi.mono (by
    change LightTernaryColoredInitializationProof.time P.allocation.E P.K+(S.initTime+PT+2000)≤
      LightTernaryArenaTemplate.time P.allocation.E+LightTernaryInitialBudgets.time P.K+S.initTime+PT+8000
    unfold LightTernaryColoredInitializationProof.time
    omega) (fun _ h=>h)

end ThreeSum.TernaryColoredNonemptyExecution
