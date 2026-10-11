import Submission.ThreeSum.LightReportingWantedRecordCall

/-!
# Execute one physical wanted slot from the reusable retained controls

The actual pointer constructor runs first. Its returned work pointer feeds
the actual wanted decoder and owner/source/catalog selector. The concrete
two-record loader then invokes the guarded original-value reporter.
-/

namespace ThreeSum.LightReportingWantedDispatch

open Light ReportingHostWantedLayout ReportingHostWantedControls

set_option maxHeartbeats 2600000
set_option maxRecDepth 22000

structure Config where
  layoutHeader : ℕ
  J : ℕ
  h : ℕ
  K : ℕ
  N : ℕ
  NB : ℕ
  NC : ℕ
  cover : ℕ
  counter : ℕ
  pairs : ℕ
  layerCount : ℕ
  scheduleSize : ℕ
  masks : ℕ
  vals : ℕ
  owners : ℕ
  records : ℕ
  pair : ℕ
  bank : ℕ
  srcB : ℕ
  srcC : ℕ
  report : ℕ
  modulus : ℕ

def arguments (C : Config) (slot : ℕ) : List ℤ :=
  [slot,C.layoutHeader,C.J,C.h,C.K,C.N,C.NB,C.NC,C.cover,C.counter,C.pairs,
    C.layerCount,C.scheduleSize,C.masks,C.vals,C.owners,C.records,C.pair,C.bank,
    C.srcB,C.srcC,C.report,C.modulus]

def layoutArguments (C : Config) : List ℤ :=
  [C.J,C.h,C.K,C.cover,C.counter,C.N,C.NB,C.NC,C.layoutHeader]

def decodeArguments (C : Config) (slot work : ℕ) : List ℤ :=
  [C.pairs,slot,C.N,C.J,C.scheduleSize,C.layerCount,C.masks,decoded C.layoutHeader,work,
    C.vals,C.owners,C.records,C.pair,C.bank,C.cover,C.srcB,C.srcC,C.report,access C.layoutHeader C.J]

def recordArguments (C : Config) : List ℤ :=
  [access C.layoutHeader C.J,C.layoutHeader,C.h,C.J,C.K,C.modulus,C.cover,C.counter]

def body (pLayout pDecode pRecord : ℕ) : Stmt :=
  .call pLayout [v 2,v 3,v 4,v 8,v 9,v 5,v 6,v 7,v 1] 23 ;;
  .set 24 (v 1 +' k 14) ;;
  .set 25 (v 1 +' k 18 +' k 2 *' v 2) ;;
  .call pDecode [v 10,v 0,v 5,v 2,v 12,v 11,v 13,v 24,v 23,
    v 14,v 15,v 16,v 17,v 18,v 8,v 19,v 20,v 21,v 25] 26 ;;
  .call pRecord [v 25,v 1,v 3,v 2,v 4,v 22,v 8,v 9] 0

def baseLibraries : Program := ReportingHostRelocation.program
  LightReportingWantedLayout.program LightReportingWantedDecodeAccess.program

def libraries : Program := ReportingHostRelocation.program
  baseLibraries LightReportingWantedRecordCall.program

def program : Program := libraries++[body 1 11 150]

def time (C : Config) (V reportTime : ℕ) : ℕ :=
  LightReportingWantedLayout.time C.h C.J+
    LightReportingWantedDecodeAccess.time C.J V+reportTime+4500

/-- A direct composition law for the three concrete, fixed executables.
The continuation contracts allow retained physical semantics to be supplied
without replacing any machine call by an assumed query operation. -/
theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {C : Config} {L : Layout}
    {slot V reportTime d : ℕ} {A B : (ℕ→ℤ)→Prop} {Q : ℤ→(ℕ→ℤ)→Prop}
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hs : C.layoutHeader+38+2*C.J≤lim.space)
    (hlayout : Meets lim LightReportingWantedLayout.program 1 (d+1) (layoutArguments C) μ
      (LightReportingWantedLayout.time C.h C.J) (fun r ν => r=(L.work : ℤ) ∧ A ν))
    (hdecode : ∀ ν, A ν → Meets lim LightReportingWantedDecodeAccess.program 9 (d+1)
      (decodeArguments C slot L.work) ν (LightReportingWantedDecodeAccess.time C.J V)
      (fun _ ξ => B ξ))
    (hrecord : ∀ ν, B ν → Meets lim LightReportingWantedRecordCall.program 138 (d+1)
      (recordArguments C) ν (reportTime+4000) Q) :
    Meets lim program 151 d (arguments C slot) μ (time C V reportTime) Q := by
  have hdecoded : (C.layoutHeader : ℤ)+14=(decoded C.layoutHeader : ℤ) := by simp [decoded]
  have haccess : (C.layoutHeader : ℤ)+18+2*(C.J : ℤ)=(access C.layoutHeader C.J : ℤ) := by
    simp [access,decoded]
    ring
  apply Meets.of_body (p := 151) (by rfl : program[151]?=some (body 1 11 150))
  unfold body time arguments
  have hlayoutRun := hlayout.append
    (LightReportingWantedDecodeAccess.program.map (ReportingHostRelocation.relocate 2)++
      LightReportingWantedRecordCall.program.map (ReportingHostRelocation.relocate 12)++[body 1 11 150])
  change Meets lim program 1 (d+1) _ μ _ _ at hlayoutRun
  light_call hlayoutRun using layoutArguments with work ν ⟨hwork,hA⟩
  light_set (decoded C.layoutHeader : ℕ) using decoded
  light_set (access C.layoutHeader C.J : ℕ) using access,decoded
  have hdecodeRun := (ReportingHostRelocation.meets (hdecode ν hA) LightReportingWantedLayout.program).append
    (LightReportingWantedRecordCall.program.map (ReportingHostRelocation.relocate 12)++[body 1 11 150])
  change Meets lim program 11 (d+1) _ ν _ _ at hdecodeRun
  light_call hdecodeRun using decodeArguments,hwork with selection ξ hB
  have hrecordRun := (ReportingHostRelocation.meets (hrecord ξ hB) baseLibraries).append [body 1 11 150]
  change Meets lim program 150 (d+1) _ ξ _ Q at hrecordRun
  light_call hrecordRun using recordArguments with result τ hQ
  exact hQ

end ThreeSum.LightReportingWantedDispatch
