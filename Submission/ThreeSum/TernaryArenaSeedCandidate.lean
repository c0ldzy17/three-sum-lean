import Submission.ThreeSum.LightTernaryControllerFactory
import Submission.ThreeSum.TernaryArenaSourceCertificate
import Submission.ThreeSum.TernaryArenaQueryModel

noncomputable section
namespace ThreeSum.TernaryArenaSeedCandidate
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
open LightTernarySeedScoreFactory LightTernaryControllerFactory
variable {p m F r : ℕ} [Fact p.Prime]

/-- The physical arrays preceding the mutable prefix arena. -/
structure Inputs where
  menu : ℕ
  J : ℕ
  Bmatrix : ℕ
  Cmatrix : ℕ
  Omatrix : ℕ
  positions : ℕ
  leftTagged : ℕ
  rightTagged : ℕ

def config (p r : ℕ) (I : Input) (A : Inputs) (seed : ℕ) : Config where
  menu:=A.menu
  seed:=seed
  J:=A.J
  catalog:=addr I.free I.capacity 7
  catalogRows:=p^(r-1)
  p:=p
  power:=p^(r-1)
  Bmatrix:=A.Bmatrix
  Bold:=addr I.free I.capacity 4
  Bnew:=addr I.free I.capacity 16
  nB:=I.nB
  Cmatrix:=A.Cmatrix
  Cold:=addr I.free I.capacity 5
  Cnew:=addr I.free I.capacity 17
  nC:=I.nC
  Omatrix:=A.Omatrix
  Oold:=addr I.free I.capacity 6
  Onew:=addr I.free I.capacity 18
  nO:=I.requesterCount
  positions:=A.positions
  wanted:=addr I.free I.capacity 19
  work:=addr I.free I.capacity 20
  hashWork:=addr I.free I.capacity 21
  hist:=addr I.free I.capacity 22
  header:=addr I.free I.capacity 1
  leftTagged:=A.leftTagged
  rightTagged:=A.rightTagged
  leftWeights:=addr I.free I.capacity 28
  rightWeights:=addr I.free I.capacity 29
  tensor:=addr I.free I.capacity 23
  countOutput:=addr I.free I.capacity 53
  quadScratch:=addr I.free I.capacity 24
  quadPowers:=addr I.free I.capacity 25
  potentialColumns:=addr I.free I.capacity 26
  potentialPowers:=addr I.free I.capacity 27
  flags:=addr I.free I.capacity 9
  scoreB:=addr I.free I.capacity 10
  scoreC:=addr I.free I.capacity 11
  scorePaired:=addr I.free I.capacity 12
  prefixLength:=r

instance (I : Input) (A : Inputs) (seed : ℕ) : Fact (config p r I A seed).p.Prime :=
  inferInstanceAs (Fact p.Prime)

/-- Actual append outputs, rather than ideal row hashes, determine every
source join and literal wanted record of this candidate. -/
def sourceInput (I : Input) (A : Inputs) (seed : ℕ) (D : Data (config p r I A seed)) : Input :=
  {I with
    leftInput:=fun i => D.newB i
    rightInput:=fun i => D.newC i
    targets:=D.targets
    positions:=D.position}

def candidate (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs)
    (seed : ℕ) (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ) :
    Candidate (config p r I A seed) where
  N:=N m r
  data:=D
  host:=setup (r := r) maps τ cap Q (sourceInput I A seed D)
  L:=L
  Rvalues:=R
  cap:=F*TernaryGoodOutputCatalog.cap m p τ
  V:=V
  U:=U
  scoreBound:=scoreBound
  leftRank:=r*alphaRank m
  rightRank:=r*alphaRank m
  twos:=r*fixedPi m 2
  leftHom:=by
    intro x hx
    exact TernaryArenaSourceCertificate.source_rank maps cap (sourceInput I A seed D) false x.2
      ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hx).2.1
  rightHom:=by
    intro x hx
    exact TernaryArenaSourceCertificate.source_rank maps cap (sourceInput I A seed D) true x.2
      ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hx).2.1
  queryRank:=by
    intro j hj
    exact TernaryArenaQueryModel.setup_rank hj
  queryTwos:=by
    intro j hj
    exact TernaryArenaQueryModel.setup_countTwo hj

/-- Every candidate executes the same six fixed local dictionaries. Only
runtime source keys, wanted rows, and the literal menu ordinal change. -/
def family (maps : Fin F→Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs)
    (D : (seed : ℕ)→Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ) :
    Family (config p r I A 0) where
  candidate:=fun seed => candidate maps τ cap U V scoreBound Q I A seed (D seed) L R
  xl:=(localRecords maps cap false).map (TernaryCanonicalDictionaries.native false maps)
  yl:=(localRecords maps cap false).map TernaryCanonicalDictionaries.wordCode
  zl:=(localRecords maps cap false).map TernaryCanonicalDictionaries.mapCode
  xr:=(localRecords maps cap true).map (TernaryCanonicalDictionaries.native true maps)
  yr:=(localRecords maps cap true).map TernaryCanonicalDictionaries.wordCode
  zr:=(localRecords maps cap true).map TernaryCanonicalDictionaries.mapCode
  leftX:=fun _ => rfl
  leftY:=fun _ => rfl
  leftZ:=fun _ => rfl
  rightX:=fun _ => rfl
  rightY:=fun _ => rfl
  rightZ:=fun _ => rfl

end ThreeSum.TernaryArenaSeedCandidate
