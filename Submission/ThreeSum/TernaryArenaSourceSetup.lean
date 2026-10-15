import Submission.ThreeSum.TernaryNativeCompleteFrontend
import Submission.ThreeSum.TernaryArenaFrontendResources
import Submission.ThreeSum.TernaryAddressDecode
import Submission.ThreeSum.TernaryBankCanonical
import Submission.ThreeSum.LightTernaryPrefixSetup

noncomputable section
namespace ThreeSum.TernaryArenaSourceSetup
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaLayout
open TernaryCanonicalDictionaries LightTernarySourceHost TernaryNativeCompleteFrontend
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]

structure Input where
  free : ℕ
  capacity : ℕ
  prefixFree : ℕ
  nB : ℕ
  nC : ℕ
  leftInput : ℕ→ℤ
  rightInput : ℕ→ℤ
  targets : ℕ→ℤ
  positions : ℕ→ℕ
  requesterCount : ℕ
  weightCap : ℕ
  queryTime : ℕ

def N (m r : ℕ) : ℕ := r*fixedLength m
def cut (m r : ℕ) : ℕ := LightTernaryPrefixSetup.T m r
def bankCodes (m r : ℕ) := TernaryAddresses.codes (N m r) (cut m r)
def nb (m r : ℕ) := (bankCodes m r).length
def alphaRank (m : ℕ) : ℕ := fixedAlpha m 1+2*fixedAlpha m 2

def source (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) :
    TernarySourceExecutionFactory.Setup :=
  let slot := if right then 39 else 30
  let recs := localRecords maps cap right
  let words := recs.map wordCode
  let groups := recs.map mapCode
  { xs := recs.map (native right maps)
    ys := words
    zs := groups
    base0 := addr I.free I.capacity slot
    dst0 := addr I.free I.capacity (slot+1)
    base1 := addr I.free I.capacity (slot+2)
    dst1 := addr I.free I.capacity (slot+3)
    base2 := addr I.free I.capacity (slot+4)
    dst2 := addr I.free I.capacity (slot+5)
    p0 := p
    p1 := 4^(fixedLength m)
    p2 := F
    U0 := p
    U1 := 4^(fixedLength m)
    U2 := F
    J := r
    src := addr I.free I.capacity (if right then 17 else 16)
    NL := if right then I.nC else I.nB
    M := p^r
    free := addr I.free I.capacity (slot+6)
    a := I.prefixFree
    bank := nb m r
    powers := I.prefixFree+4^(N m r)
    W := 2*N m r
    L := 2*N m r
    keyBase := addr I.free I.capacity (slot+7)
    valueBase := addr I.free I.capacity (slot+8)
    weightBase := addr I.free I.capacity (if right then 29 else 28)
    weightU := I.weightCap
    factor := 2^(r*fixedAlpha m 2)
    groups := F^r
    U := p*(p+1)^r
    input := if right then I.rightInput else I.leftInput
    codes := fun i => (bankCodes m r).getD i 0
    key := fun i => (bankCodes m r).idxOf (dictionary words (4^(fixedLength m)) r i).toNat
    group := fun i => (dictionary groups F r i).toNat }

def entries (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) :=
  TernaryWantedBatchIndex.entries p (4^(fixedLength m)) F r
    (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
    (TernaryGoodOutputCatalog.mapCodes maps τ) I.targets I.positions I.requesterCount

def nearConfig (I : Input) (right : Bool) (V : ℕ) : LightTernaryNearPair.Config :=
  TernaryArenaFrontendResources.config I.free I.capacity (N m r) V I.prefixFree (nb m r)
    (addr I.free I.capacity (if right then 51 else 50)+N m r*nb m r)
    (cut m r) (r*alphaRank m) (if right then 62 else 58)

def valueCap (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) : ℕ :=
  2^(r*fixedAlpha m 2)*I.weightCap*
    (I.nB*(localRecords maps cap false).length^r+I.nC*(localRecords maps cap true).length^r+1)

def front (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : TernaryGoodOutputCatalog.Output m)
    (I : Input) : TernaryCountExecutionFactory.Setup (N m r) :=
  { f := nearConfig (m := m) (r := r) I false (valueCap (r := r) maps cap I)
    g := nearConfig (m := m) (r := r) I true (valueCap (r := r) maps cap I)
    Qstar := TernaryRepeatedWords.canonical (fun _ : Fin r => localQ.val)
    Q := fun i => TernaryAddressDecode.word (N m r) (TernaryWantedBatchIndex.get (entries (r := r) maps τ I) i).2.1
    group := fun i => (TernaryWantedBatchIndex.get (entries (r := r) maps τ I) i).2.2
    E := TernaryBankCanonical.enumeration (N m r) (cut m r)
    bankPowers := addr I.free I.capacity 49
    keyBase := addr I.free I.capacity 48
    groups := F^r
    fsource := addr I.free I.capacity 38
    gsource := addr I.free I.capacity 47
    fbase := addr I.free I.capacity 50
    gbase := addr I.free I.capacity 51
    hbase := addr I.free I.capacity 52
    out := addr I.free I.capacity 66
    caps := addr I.free I.capacity 55
    records := addr I.free I.capacity 19
    count := (entries (r := r) maps τ I).length
    dst := addr I.free I.capacity 53
    V := valueCap (r := r) maps cap I
    t := I.queryTime }

def setup (maps : Fin F→Weight m p) (τ cap : ℕ) (localQ : TernaryGoodOutputCatalog.Output m)
    (I : Input) : TernarySourceCountExecutionFactory.Setup (N m r) :=
  { left := source (r := r) maps cap I false
    right := source (r := r) maps cap I true
    front := front (r := r) maps τ cap localQ I }

@[simp] theorem setup_left_input (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) :
    (setup (r := r) maps τ cap Q I).left.input=I.leftInput := rfl
@[simp] theorem setup_right_input (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) :
    (setup (r := r) maps τ cap Q I).right.input=I.rightInput := rfl

end ThreeSum.TernaryArenaSourceSetup
