import Submission.ThreeSum.TernaryArenaQueryTime
import Submission.ThreeSum.TernaryArenaPostSelection

noncomputable section
namespace ThreeSum.TernaryArenaQueryTimeMonotone
open TernaryArenaSourceSetup TernaryCoverGoodMaps TernaryLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

/-- Physical source keys, addresses and requester values do not enter the
query runtime; only the common coefficient magnitude can increase it. -/
theorem prepared {V W : ℕ} (I I' : Input) (hV : V≤W) (Q : TritWord (N m r)) :
    LightTernaryPreparedWanted.time
      (nearConfig (m:=m) (r:=r) I false V) (nearConfig (m:=m) (r:=r) I true V) Q≤
    LightTernaryPreparedWanted.time
      (nearConfig (m:=m) (r:=r) I' false W) (nearConfig (m:=m) (r:=r) I' true W) Q := by
  have hE : TernaryFrontendResources.eulerBound (N m r) V≤
      TernaryFrontendResources.eulerBound (N m r) W := by
    unfold TernaryFrontendResources.eulerBound TernaryFrontendResources.sourceZeta
    gcongr
  have hl := Nat.log_mono_right (b:=2) (Nat.add_le_add_right hE 1)
  unfold LightTernaryPreparedWanted.time LightTernaryWantedQuery.time
    LightTernaryNearPair.pairTime LightTernaryNearPair.time LightTernaryNearSource.time
    LightTernaryEulerMemo.time LightTernaryEulerScan.time LightTernaryEulerRow.fillTime
    LightTernaryEulerRow.time LightTernaryDivide.time LightOutputDecodeDivide.budget
  dsimp only [nearConfig,TernaryArenaFrontendResources.config]
  gcongr

theorem query {V W : ℕ} (I I' : Input) (hV : V≤W) :
    TernaryArenaCountReady.queryTime (m:=m) (r:=r) I V≤
      TernaryArenaCountReady.queryTime (m:=m) (r:=r) I' W := by
  classical
  unfold TernaryArenaCountReady.queryTime
  apply Finset.sup_le
  intro Q hQ
  exact (prepared I I' hV Q).trans (Finset.le_sup (f:=fun Q =>
    LightTernaryPreparedWanted.time (nearConfig (m:=m) (r:=r) I' false W)
      (nearConfig (m:=m) (r:=r) I' true W) Q) hQ)

theorem value (maps : Fin F→Weight m p) (cap : ℕ) (I I' : Input)
    (hB : I.nB≤I'.nB) (hC : I.nC≤I'.nC) (hw : I.weightCap≤I'.weightCap) :
    valueCap (r:=r) maps cap I≤valueCap (r:=r) maps cap I' := by
  unfold valueCap
  gcongr

theorem counts (maps : Fin F→Weight m p) (cap : ℕ) (I I' : Input)
    (hB : I.nB≤I'.nB) (hC : I.nC≤I'.nC) (hw : I.weightCap≤I'.weightCap) :
    TernaryArenaCountReady.queryTime (m:=m) (r:=r) I (valueCap (r:=r) maps cap I)≤
      TernaryArenaCountReady.queryTime (m:=m) (r:=r) I' (valueCap (r:=r) maps cap I') :=
  query I I' (value maps cap I I' hB hC hw)

/-- Singleton compaction lowers the actual native query coefficient bound;
the target hash and compact source values may vary freely. -/
theorem selected {J : ℕ} (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (U radix nA : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    let I' := TernaryArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC
    TernaryArenaCountReady.queryTime (m:=m) (r:=r) I' (valueCap (r:=r) maps cap I')≤
      TernaryArenaCountReady.queryTime (m:=m) (r:=r) I (valueCap (r:=r) maps cap I) := by
  apply counts
  · exact LightOriginalSurvivors.length_le keysB I.nB
  · exact LightOriginalSurvivors.length_le keysC I.nC
  · exact le_rfl

end ThreeSum.TernaryArenaQueryTimeMonotone
