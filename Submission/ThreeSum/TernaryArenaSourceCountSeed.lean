import Submission.ThreeSum.TernaryArenaSourceSeed
import Submission.ThreeSum.TernaryArenaCountReady
import Submission.ThreeSum.TernarySourceCountWeightSeed

noncomputable section
namespace ThreeSum.TernaryArenaSourceCountSeed
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

/-- Literal immutable inputs retained across all actual signed channel calls. -/
structure Reads (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (μ : ℕ→ℤ) : Prop where
  left : ∀i<I.nB, μ (addr I.free I.capacity 16+i)=I.leftInput i
  right : ∀i<I.nC, μ (addr I.free I.capacity 17+i)=I.rightInput i
  leftBound : ∀i<I.nB, |I.leftInput i|≤(p*(p+1)^r : ℕ)
  rightBound : ∀i<I.nC, |I.rightInput i|≤(p*(p+1)^r : ℕ)
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
  wanted : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I))

theorem seed {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ)
    (localQ : TernaryGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (hF : 1<F) (hN : 0<N m r)
    (hw : (lim.space : ℤ)≤lim.word)
    (C : TernaryArenaCountReady.Capacity (lim := lim) (d := d+1) (r := r) maps τ cap I)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hprefix : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 28)
    (hlocal : ∀right, 0<(localRecords maps cap right).length)
    (G : ∀right, TernaryArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space)
    (W : ∀right, TernaryArenaSourceControls.Controls (r := r) maps cap I right lim (d+1))
    (M : Reads (r := r) maps τ I μ)
    (hleft : ∀i<I.nB, |leftWeight i|≤(I.weightCap : ℤ))
    (hright : ∀i<I.nC, |rightWeight i|≤(I.weightCap : ℤ)) :
    TernarySourceCountExecutionFactory.Seed (setup (r := r) maps τ cap localQ I) lim d
      (addr I.free I.capacity 28) μ leftWeight rightWeight := by
  have hnb := TernaryArenaCountReady.bank_size hN
  have hfour : 4^(N m r)=2^(2*N m r) := by rw [Nat.pow_mul]
  have hbank : I.prefixFree+nb m r≤addr I.free I.capacity 28 := by omega
  have h28_30 : addr I.free I.capacity 28≤addr I.free I.capacity 30 := before (by decide) (by omega : 0≤I.capacity)
  have hgroup : F^r*nb m r+1≤lim.space := by
    have hp := C.powers
    have hs := C.endSpace
    have hg := C.bankValues
    unfold finish addr slots at hs
    omega
  have mem (right : Bool) : TernaryArenaSourceSeed.Memory (r := r) maps cap I right lim μ
      (if right then rightWeight else leftWeight) := by
    refine {
      nonempty:=hlocal right
      sourceBefore:=?_
      weightsBefore:=?_
      bankBefore:=?_
      powersBefore:=?_
      groupSpace:=hgroup
      bankSize:=hnb
      input:=?_
      inputBound:=?_
      weights:=?_
      codes:=M.codes
      powers:=M.powers }
    · cases right
      · exact before (by decide) hnB
      · exact before (by decide) hnC
    · cases right
      · exact before (by decide) hnB
      · exact before (by decide) hnC
    · cases right
      · exact hbank.trans (before (by decide) (by omega : 0≤I.capacity))
      · exact hbank.trans (before (by decide) (by omega : 0≤I.capacity))
    · cases right
      · exact hprefix.trans (before (by decide) (by omega : 0≤I.capacity))
      · exact hprefix.trans (before (by decide) (by omega : 0≤I.capacity))
    · cases right
      · exact M.left
      · exact M.right
    · cases right
      · exact M.leftBound
      · exact M.rightBound
    · cases right
      · exact hleft
      · exact hright
  refine {
    layout:=?_
    left:=TernaryArenaSourceSeed.seed maps cap I false hF hw (G false) (W false) (mem false)
    right:=TernaryArenaSourceSeed.seed maps cap I true hF hw (G true) (W true) (mem true)
    front:=TernaryArenaCountReady.ready maps τ cap localQ I μ leftWeight rightWeight hF hN hw C M.codes M.wanted hleft hright
    leftInputBefore:=before (by decide) hnB
    leftCodesBefore:=hbank
    leftPowersBefore:=hprefix
    rightInputBefore:=before (by decide) hnC
    rightCodesBefore:=hbank
    rightPowersBefore:=hprefix
    frontCodesBefore:=hbank
    frontRecordsBefore:=before (by decide) C.records
    boundaryBefore:=h28_30
    depth:=by have := C.depth; omega }
  refine {
    leftBank:=rfl
    rightBank:=rfl
    leftGroups:=rfl
    rightGroups:=rfl
    leftValues:=rfl
    rightValues:=rfl
    leftBeforeRight:=before (by decide) (by omega : 0≤I.capacity)
    leftBeforeFront:=before (by decide) (by omega : 0≤I.capacity)
    leftValuesEnd:=before (by decide) C.bankValues
    rightInputBefore:=before (by decide) hnC
    rightWeightsBefore:=before (by decide) hnC
    rightCodesBefore:=hbank.trans h28_30
    rightPowersBefore:=hprefix.trans h28_30
    frontCodesBefore:=hbank.trans h28_30
    frontRecordsBefore:=before (by decide) C.records }

end ThreeSum.TernaryArenaSourceCountSeed
