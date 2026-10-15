import Submission.ThreeSum.LightTernarySeedScoreFactory
import Submission.ThreeSum.TernaryNativeTensorScore
import Submission.ThreeSum.LightTernarySeedController

noncomputable section
namespace ThreeSum.LightTernaryControllerFactory
open Light LightTernarySeedScoreFactory
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

/-- A menu ordinal changes only the runtime seed field. -/
def withSeed (C : Config) (i : ℕ) : Config :={C with seed:=i}
instance {C : Config} [Fact C.p.Prime] (i : ℕ) : Fact (withSeed C i).p.Prime :=inferInstanceAs (Fact C.p.Prime)

structure Candidate (C : Config) [Fact C.p.Prime] where
  N : ℕ
  data : Data C
  host : TernarySourceCountExecutionFactory.Setup N
  L : ℕ→ℕ→ℤ
  Rvalues : ℕ→ℕ→ℤ
  cap : ℕ
  V : ℕ
  U : ℕ
  scoreBound : ℤ
  leftRank : ℕ
  rightRank : ℕ
  twos : ℕ
  leftHom : ∀pair∈host.left.records, TernaryBank.rank (host.front.E.word (host.left.key pair.2))=leftRank
  rightHom : ∀pair∈host.right.records, TernaryBank.rank (host.front.E.word (host.right.key pair.2))=rightRank
  queryRank : ∀i<host.front.count, TernaryBank.rank (host.front.Q i)=leftRank+rightRank
  queryTwos : ∀i<host.front.count, TernaryJointType.digitCount (host.front.Q i) 2=twos

def Candidate.score {C : Config} [Fact C.p.Prime] (D : Candidate C) (K : ℕ) : ℤ :=
  ((2:ℤ)^D.twos)^K*(TernaryNativeTensorScore.pairedPotential D.host K C.J D.L D.Rvalues:ℤ)

def Candidate.runtime {C : Config} [Fact C.p.Prime] (D : Candidate C) (K R S : ℕ)
    (raws : List ℤ) (words maps : List ℕ) : ℕ :=
  LightTernarySeedScoreFactory.runtime D.data D.host K R S D.cap D.V raws words maps

def Candidate.Guard {C : Config} [Fact C.p.Prime] (D : Candidate C) (lim : Limits)
    (depth K R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ) : Prop :=
  Ready C D.data lim depth R S D.cap D.V K D.N D.U D.host D.L D.Rvalues D.scoreBound raws words maps μ ∧
    |D.score K|≤lim.word

def Candidate.Done {C : Config} [Fact C.p.Prime] (D : Candidate C) (K : ℕ) (μ ν : ℕ→ℤ) : Prop :=
  ∃ξ, KeptInput C μ ξ ∧ ν=
    Function.update (Function.update (Function.update (Function.update ξ
      (C.flags+C.seed) D.data.flag) (C.scoreB+C.seed) D.data.collisionB)
      (C.scoreC+C.seed) D.data.collisionC) (C.scorePaired+C.seed) (D.score K)

theorem Candidate.run {C : Config} [Fact C.p.Prime] {D : Candidate C} {lim : Limits}
    {depth K R S : ℕ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ→ℤ}
    (G : D.Guard lim depth K R S raws words maps μ) :
    Meets lim (LightTernarySeedScore.program C.p R S K raws words maps
      D.host.left.xs D.host.left.ys D.host.left.zs D.host.right.xs D.host.right.ys D.host.right.zs)
      164 depth C.argv μ (D.runtime K R S raws words maps)
      (fun r ν=>r=D.data.flag ∧ D.Done K μ ν) :=by
  have hh:=G.1.run D.leftHom D.rightHom D.queryRank
    (fun i : Fin D.host.front.count=>TernaryNativePairMoments.Pair D.host i.val)
    (fun i=>TernaryNativeTensorScore.originalLeft D.host C.J D.L i.val)
    (fun i=>TernaryNativeTensorScore.originalRight D.host C.J D.Rvalues i.val)
    ((2:ℤ)^D.twos)
    (by
      intro i a b c e
      rw [TernaryNativeTensorScore.score_eq_original_tensor,
        TernaryConvolution.factorial_eq_power_two,D.queryTwos i.val i.isLt])
    (by simpa only [Candidate.score,TernaryNativeTensorScore.pairedPotential,Nat.cast_sum] using G.2)
  simpa only [Candidate.runtime,Candidate.Done,Candidate.score,
    TernaryNativeTensorScore.pairedPotential,Nat.cast_sum] using hh

structure Family (C : Config) [Fact C.p.Prime] where
  candidate : (i : ℕ)→Candidate (withSeed C i)
  xl : List ℤ
  yl : List ℤ
  zl : List ℤ
  xr : List ℤ
  yr : List ℤ
  zr : List ℤ
  leftX : ∀i, (candidate i).host.left.xs=xl
  leftY : ∀i, (candidate i).host.left.ys=yl
  leftZ : ∀i, (candidate i).host.left.zs=zl
  rightX : ∀i, (candidate i).host.right.xs=xr
  rightY : ∀i, (candidate i).host.right.ys=yr
  rightZ : ∀i, (candidate i).host.right.zs=zr

def Family.flag {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : ℤ :=(D.candidate i).data.flag
def Family.scoreB {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : ℤ :=(D.candidate i).data.collisionB
def Family.scoreC {C : Config} [Fact C.p.Prime] (D : Family C) (i : ℕ) : ℤ :=(D.candidate i).data.collisionC
def Family.scoreP {C : Config} [Fact C.p.Prime] (D : Family C) (K i : ℕ) : ℤ :=(D.candidate i).score K

def Family.pick {C : Config} [Fact C.p.Prime] (D : Family C) (K n dB dC dP tB tC tP : ℕ) :=
  LightTernaryRowSelector.pick (LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
    dB dC dP tB tC tP) n

structure SpanGuard (C : Config) [Fact C.p.Prime] (D : Data C) (lim : Limits)
    (depth newSpan : ℕ) (μ : ℕ→ℤ) : Prop where
  represents : TernaryStoredSpan.Represents D.catalog C.catalogRows
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J))
  rowsPos : 0<C.catalogRows
  spaceWord : (lim.space:ℤ)≤lim.word
  source : C.catalog+C.J*C.catalogRows≤newSpan
  row : C.row+C.J≤newSpan
  output : newSpan+C.J*C.catalogRows*C.p≤lim.space
  word : (LightPrimeCoefficient.word C.p:ℤ)≤lim.word
  controls : ((C.catalogRows+C.J+16:ℕ):ℤ)≤lim.word
  bounded : ∀k<C.catalogRows, ∀i<C.J, D.catalog k i<C.p
  read : ∀k<C.catalogRows, ∀i<C.J, μ (C.catalog+C.J*k+i)=(D.catalog k i:ℤ)
  rowRead : ∀i<C.J, μ (C.row+i)=
    (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i:ℤ)
  depth : depth+4≤lim.depth

def SpanDone (C : Config) [Fact C.p.Prime] (D : Data C) (newSpan : ℕ) (μ ν : ℕ→ℤ) : Prop :=
  (∀q<C.p*C.catalogRows, ∀i<C.J, ν (newSpan+C.J*q+i)=
    (TernaryStoredSpan.next D.catalog
      (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow))
      C.p C.catalogRows q i:ℤ)) ∧
  TernaryStoredSpan.Represents
    (TernaryStoredSpan.next D.catalog
      (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)) C.p C.catalogRows)
    (C.p*C.catalogRows)
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow::D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J)) ∧
  (∀q<C.p*C.catalogRows, ∀i<C.J, TernaryStoredSpan.next D.catalog
    (LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)) C.p C.catalogRows q i<C.p) ∧
  SameOutside μ ν newSpan (C.J*C.catalogRows*C.p)

theorem SpanGuard.run {C : Config} [Fact C.p.Prime] {D : Data C} {lim : Limits}
    {depth newSpan : ℕ} {μ : ℕ→ℤ} (G : SpanGuard C D lim depth newSpan μ) :
    Meets lim LightStoredSpan.program 1 depth [C.catalog,C.catalogRows,C.row,newSpan,C.J,C.p]
      μ (LightSpanCatalogStep.time C.J C.p C.catalogRows) (fun _ ν=>SpanDone C D newSpan μ ν) :=by
  exact LightStoredSpan.program_step_meets μ D.catalog
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J)) G.represents G.rowsPos
    G.spaceWord G.source G.row G.output G.word G.controls G.bounded G.read G.rowRead G.depth

/-- A pure state invariant, concrete candidate guards, and the actual span
layout derive all operational premises of the finite menu controller. -/
theorem run {C : Config} [Fact C.p.Prime] (D : Family C) {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ→ℤ)
    (I : ℕ→(ℕ→ℤ)→Prop) (Replay Final : (ℕ→ℤ)→Prop)
    (hw : (lim.space:ℤ)≤lim.word)
    (hFlags : C.flags+n≤lim.space) (hBs : C.scoreB+n≤lim.space)
    (hCs : C.scoreC+n≤lim.space) (hPs : C.scorePaired+n≤lim.space)
    (hWord : (LightTernaryRowSelector.word n U dB dC dP tB tC tP:ℤ)≤lim.word)
    (hLen : C.J+2≤lim.space)
    (hRow : C.menu+(D.pick K n dB dC dP tB tC tP-1)*(C.J+2)≤lim.space)
    (hd : depth<lim.depth) (hstart : I 0 μ)
    (hguard : ∀i<n, ∀ν, I i ν→(D.candidate i).Guard lim (depth+1) K R S raws words maps ν)
    (htime : ∀i<n, (D.candidate i).runtime K R S raws words maps≤seedTime)
    (hnext : ∀i<n, ∀ν ξ, I i ν→(D.candidate i).Done K ν ξ→I (i+1) ξ)
    (hread : ∀ν, I n ν→
      (∀i<n, ν (C.flags+i)=D.flag i ∧ |D.flag i|≤1) ∧
      (∀i<n, ν (C.scoreB+i)=D.scoreB i ∧ |D.scoreB i|≤U) ∧
      (∀i<n, ν (C.scoreC+i)=D.scoreC i ∧ |D.scoreC i|≤U) ∧
      (∀i<n, ν (C.scorePaired+i)=D.scoreP K i ∧ |D.scoreP K i|≤U))
    (hexist : ∃i<n, LightTernaryRowSelector.Good D.flag D.scoreB D.scoreC (D.scoreP K)
      dB dC dP tB tC tP i)
    (hreplayGuard : ∀ν, I n ν→
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).Guard lim (depth+1) K R S raws words maps ν)
    (hreplay : ∀ν ξ, I n ν→(D.candidate (D.pick K n dB dC dP tB tC tP-1)).Done K ν ξ→Replay ξ)
    (hspan : ∀ν, Replay ν→SpanGuard (withSeed C (D.pick K n dB dC dP tB tC tP-1))
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data lim (depth+1) newSpan ν)
    (hfinal : ∀ν ξ, Replay ν→SpanDone (withSeed C (D.pick K n dB dC dP tB tC tP-1))
      (D.candidate (D.pick K n dB dC dP tB tC tP-1)).data newSpan ν ξ→Final ξ) :
    Meets lim (LightTernarySeedController.program C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr)
      166 depth (LightTernarySeedController.args (withSeed C 0).argv n dB dC dP tB tC tP newSpan)
      μ (LightTernarySeedController.time n seedTime (LightSpanCatalogStep.time C.J C.p C.catalogRows))
      (fun r ν=>r=(D.pick K n dB dC dP tB tC tP:ℤ) ∧ Final ν) :=by
  have hpos : 0<D.pick K n dB dC dP tB tC tP :=
    (LightTernaryRowSelector.pick_pos_iff _ _).mpr hexist
  have hle : D.pick K n dB dC dP tB tC tP≤n :=LightTernaryRowSelector.pick_le _ _
  have hi : D.pick K n dB dC dP tB tC tP-1<n :=by omega
  apply LightTernarySeedController.program_meets raws words maps D.xl D.yl D.zl D.xr D.yr D.zr
    μ D.flag D.scoreB D.scoreC (D.scoreP K) I Replay Final hw hFlags hBs hCs hPs hWord hLen hRow hd hstart
  · intro i hi ν hI
    have hh:=Candidate.run (hguard i hi ν hI)
    rw [D.leftX i,D.leftY i,D.leftZ i,D.rightX i,D.rightY i,D.rightZ i] at hh
    apply hh.mono (htime i hi)
    intro r ξ hξ
    exact hnext i hi ν ξ hI hξ.2
  · exact hread
  · exact hexist
  · intro ν hI
    have hh:=Candidate.run (hreplayGuard ν hI)
    rw [D.leftX _,D.leftY _,D.leftZ _,D.rightX _,D.rightY _,D.rightZ _] at hh
    apply hh.mono (htime _ hi)
    intro r ξ hξ
    exact hreplay ν ξ hI hξ.2
  · intro ν hν
    have hcast : ((D.pick K n dB dC dP tB tC tP-1:ℕ):ℤ)=
        (D.pick K n dB dC dP tB tC tP:ℤ)-1 :=by omega
    dsimp only [Family.pick] at hcast
    simpa only [withSeed,Config.row,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,hcast,Family.pick] using
      (hspan ν hν).run.mono le_rfl (fun _ ξ hξ=>hfinal ν ξ hν hξ)

end ThreeSum.LightTernaryControllerFactory
