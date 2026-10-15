import Submission.ThreeSum.TernaryColoredFinalCall
import Submission.ThreeSum.TernaryColoredFinalReady

noncomputable section
namespace ThreeSum.TernaryColoredConcreteFinalCall
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open TernaryConcreteProfile TernaryLocalParameters TernaryColoredLoopSetup
open TernaryColoredTerminalReceipt TernaryColoredFinalReady
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000
variable {κ : ℕ}

def pre (P : Profile κ) : Program :=
  LightTernaryColoredSolver.libraries P.radix P.allocation.D P.allocation.E P.K P.radix
    (P.p^(2*P.K)) P.drift P.scale P.p (4^fixedLength P.m) P.F
    (TernaryGoodOutputCatalog.raws P.maps P.threshold)
    (TernaryGoodOutputCatalog.wordCodes P.maps P.threshold)
    (TernaryGoodOutputCatalog.mapCodes P.maps P.threshold)
    ((TernaryExecutable.leftRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native false P.maps))
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.leftRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map (TernaryCanonicalDictionaries.native true P.maps))
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.wordCode)
    ((TernaryExecutable.rightRecords P.maps P.cap).map TernaryCanonicalDictionaries.mapCode)

def suffix (P : Profile κ) : Program :=
  [LightTernaryColoredSolver.body ((pre P).length+TernaryExecutable.reportingMain (p:=P.p) P.K)
    P.m P.F P.p (fixedAlpha P.m 2) (alphaRank P.m) (TernaryCodeSemantics.address P.output.val)
    (4^fixedLength P.m) (P.p^(2*P.K)) P.drift P.scale (fixedLength P.m)]

theorem pre_length (P : Profile κ) : (pre P).length=240 :=
  LightTernaryColoredSolver.libraries_length _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

theorem program_eq (P : Profile κ) : P.color=
    ReportingHostRelocation.program (pre P) (TernaryExecutable.reporting P.maps P.cap P.K)++suffix P :=rfl

variable (P : Profile κ) (n free menu c : ℕ) (A B C : List ℤ) (initial : ℕ→ℤ)
variable [Fact (Irreducible (TernaryComputedExtensionMenu.modulus P.p (dim P n) c))]

theorem reporter_eq :
    let S:=TernaryArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
      (selected P n free menu c A B C initial)
    LightTernaryPreparedPostSelection.closedProgram
      S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs P.H=
        TernaryExecutable.reporting P.maps P.cap P.K :=rfl

/-- Literal procedure240+reportingMain runs the complete final reporter.
All semantic inputs are the actual terminal loop receipt. -/
theorem call {lim : Limits} {d : ℕ} (ν : ℕ→ℤ) (loc : ℕ→ℤ) (header : ℕ)
    (hmeta : TernaryPreparedOriginals.Metadata n (n^κ) A B C)
    (hinputs : TernaryArenaFixedParameters.InputGuards P.K P.m P.radix κ n)
    (H : Ready P n free menu c A B C initial lim d ν)
    (T : Receipt P n free menu c A B C initial ν)
    (hloc5 : loc 5=(header:ℤ))
    (hloc6 : loc 6=((input P n free A B C).free:ℤ))
    (hloc7 : loc 7=(cells P n:ℤ))
    (hloc10 : loc 10=(addr (input P n free A B C).free (cells P n) 1:ℤ))
    (hloc12 : loc 12=((P.p^(rounds P n):ℕ):ℤ))
    (hloc14 : loc 14=((2*N P.m (rounds P n):ℕ):ℤ))
    (hheader : Seg ν header [(LightTernaryColorPrelude.av free n:ℤ),A.length,
      LightTernaryColorPrelude.bv free n,B.length,LightTernaryColorPrelude.cv free n,C.length])
    (hheaderSpace : header+6≤lim.space) :
    Ends lim P.color d
      (.call (240+TernaryExecutable.reportingMain (p:=P.p) P.K) LightTernaryColoredSolver.postArgs 0)
      ⟨loc,ν⟩
      (673+LightTernaryPreparedPostSelection.time
        (TernaryArenaSourceSetup.setup (r:=rounds P n) P.maps P.threshold P.cap P.output
          (selected P n free menu c A B C initial)) P.H (cleanup P n free A B C)
        (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial))
      (fun σ=>σ.loc 0=(if ∃i<A.length,∃j<B.length,∃k<C.length,
          C.getD k 0=A.getD i 0+B.getD j 0 then 1 else 0:ℤ) ∧
        Kept ν σ.mem (addr (input P n free A B C).free (cells P n) 6)) :=by
  have hcapacity : 106≤cells P n:=by
    have hh:=capacity_pos P.allocation.D P.allocation.E (n+n^κ)
    change 106≤capacity P.allocation.D P.allocation.E (n+n^κ)
    omega
  have hhostSpace : addr (input P n free A B C).free (cells P n) 1+106≤lim.space :=
    region_space (by decide : 1<slots) hcapacity H.guards.hend
  have hh:=TernaryColoredFinalCall.final_call (J:=J P n) (r:=rounds P n) (K:=P.K)
    P.maps P.threshold P.cap P.output (input P n free A B C) (n^κ) P.radix A.length
    (LightTernaryColorPrelude.av free n) (LightTernaryColorPrelude.bv free n) (LightTernaryColorPrelude.cv free n)
    (P.p^(rounds P n)) (2*N P.m (rounds P n)) (hash P n free menu c A B C initial)
    (fun i=>A.getD i 0) (fun i=>B.getD i 0) (fun i=>C.getD i 0)
    (keysB P n free menu c A B C initial) (keysC P n free menu c A B C initial) ν
    H.guards H.cleanup H.metadata P.cover hmeta.boundA hmeta.boundB hmeta.boundC
    P.radix_gt_one P.basePrime hinputs.2.2.1 (fun _ _=>rfl) (fun _ _=>rfl) le_rfl T.zero
    (pre P) (suffix P) loc header (addr (input P n free A B C).free (cells P n) 1)
    hloc5 hloc6 hloc7 hloc10 hloc12 hloc14 hheader hheaderSpace hhostSpace hcapacity H.host
  dsimp only at hh
  have hreport:=reporter_eq P n free menu c A B C initial
  dsimp only [selected] at hreport
  erw [hreport,←program_eq P,pre_length] at hh
  have hB : (input P n free A B C).nB=B.length:=rfl
  have hC : (input P n free A B C).nC=C.length:=rfl
  have hCap : (input P n free A B C).capacity=cells P n:=rfl
  set_option backward.isDefEq.respectTransparency false in
    simpa only [TernaryColoredPostABI.post_cost,TernaryExecutable.reportingMain,Profile.H,
      selected,cleanup,hB,hC,hCap,show (671:ℕ)+2=673 by decide] using hh

end ThreeSum.TernaryColoredConcreteFinalCall
