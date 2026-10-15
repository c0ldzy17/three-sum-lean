import Submission.ThreeSum.TernaryArenaSeedScoreReady

noncomputable section
namespace ThreeSum.TernaryArenaSeedPrimitiveGuards
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
open LightTernarySeedScoreFactory TernaryArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000

def rawCap (m p r : ℕ) : ℕ :=p*(p+1)^r

def word (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (A : Inputs) (seed positionCap : ℕ)
    (D : Data (config p r I A seed)) : ℕ :=
  LightTernaryAppendKeys.word (A.J+2) p D.bB (p^(r-1))+
  LightTernaryAppendKeys.word (A.J+2) p D.bC (p^(r-1))+
  LightTernaryAppendKeys.word (A.J+2) p D.bO (p^(r-1))+
  p^(r-1)+A.J+16+p+(4^fixedLength m)+F+(TernaryGoodOutputCatalog.raws maps τ).length+
  (8*rawCap m p r+4*p+16)+(2*(4^fixedLength m))^r+(2*F)^r+positionCap+r+
  (I.nB*I.nB+I.nB+p^(r-1)*p+16)+(I.nC*I.nC+I.nC+p^(r-1)*p+16)

/-- These are exact original-array, menu, old-key and prefix-catalog
invariants furnished by the corresponding actual initialization kernels. -/
structure Reads (I : Input) (A : Inputs) (seed : ℕ) (D : Data (config p r I A seed))
    (μ : ℕ→ℤ) (positionCap : ℕ) : Prop where
  matrixB : A.Bmatrix+I.nB*(A.J+2)≤I.free
  matrixC : A.Cmatrix+I.nC*(A.J+2)≤I.free
  matrixO : A.Omatrix+I.requesterCount*(A.J+2)≤I.free
  menu : (config p r I A seed).row+(A.J+2)≤I.free
  positions : A.positions+I.requesterCount≤I.free
  bB : D.bB<p
  bC : D.bC<p
  bO : D.bO<p
  Bbound : ∀i<I.nB,∀k<A.J+2, |D.B i k|≤(D.bB : ℤ)
  Cbound : ∀i<I.nC,∀k<A.J+2, |D.Cvalues i k|≤(D.bC : ℤ)
  Obound : ∀i<I.requesterCount,∀k<A.J+2, |D.O i k|≤(D.bO : ℤ)
  coeffBound : ∀k<A.J+2, D.coeff k≤p
  oldB : ∀i<I.nB, D.oldB i<p^(r-1)
  oldC : ∀i<I.nC, D.oldC i<p^(r-1)
  oldO : ∀i<I.requesterCount, D.oldO i<p^(r-1)
  BRead : ∀i<I.nB,∀k<A.J+2, μ (A.Bmatrix+i*(A.J+2)+k)=D.B i k
  CRead : ∀i<I.nC,∀k<A.J+2, μ (A.Cmatrix+i*(A.J+2)+k)=D.Cvalues i k
  ORead : ∀i<I.requesterCount,∀k<A.J+2, μ (A.Omatrix+i*(A.J+2)+k)=D.O i k
  coeffRead : ∀k<A.J+2, μ ((config p r I A seed).row+k)=(D.coeff k : ℤ)
  oldBRead : LightTernarySeedScoreFactory.Reads μ (addr I.free I.capacity 4) I.nB D.oldB
  oldCRead : LightTernarySeedScoreFactory.Reads μ (addr I.free I.capacity 5) I.nC D.oldC
  oldORead : LightTernarySeedScoreFactory.Reads μ (addr I.free I.capacity 6) I.requesterCount D.oldO
  represents : TernaryStoredSpan.Represents D.catalog (p^(r-1))
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal A.J))
  catalogBound : ∀k<p^(r-1),∀i<A.J, D.catalog k i<p
  catalogRead : ∀k<p^(r-1),∀i<A.J, μ (addr I.free I.capacity 7+A.J*k+i)=(D.catalog k i : ℤ)
  digits : ∀i<A.J, D.coeff i=LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i
  positionRead : ∀i<I.requesterCount, μ (A.positions+i)=(D.position i : ℤ)
  positionBound : ∀i<I.requesterCount, D.position i≤positionCap

theorem guards {lim : Limits} {depth seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (A : Inputs)
    (D : Data (config p r I A seed)) (μ : ℕ→ℤ)
    (M : Reads I A seed D μ positionCap) (hw : (lim.space : ℤ)≤lim.word)
    (hend : finish I.free I.capacity≤lim.space)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity) (hnO : I.requesterCount≤I.capacity)
    (hJ : A.J+2≤I.capacity) (hspan : A.J*p^(r-1)≤I.capacity)
    (hhist : p^(r-1)*p≤I.capacity)
    (hwanted : 3*I.requesterCount*(F*TernaryGoodOutputCatalog.cap m p τ)^r≤I.capacity)
    (hdiv : Nat.log 2 (2*rawCap m p r+1)+2≤I.capacity)
    (hword : (word maps τ I A seed positionCap D : ℤ)≤lim.word)
    (hd : depth+r+6<lim.depth) (hF : 1<F) (hτ : 0<τ)
    (hraw : 1≤(TernaryGoodOutputCatalog.raws maps τ).length) :
    AppendGuard (config p r I A seed) D lim depth μ ∧
    SpanGuard (config p r I A seed) D lim μ ∧
    WantedGuard (config p r I A seed) D lim depth (4^fixedLength m) F
      (F*TernaryGoodOutputCatalog.cap m p τ) (rawCap m p r)
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ ∧
    CollisionGuard (config p r I A seed) D lim (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) := by
  have before16 : I.free≤addr I.free I.capacity 16 := by unfold addr; omega
  have numWord (v : ℕ) (hv : v≤word maps τ I A seed positionCap D) : (v : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hv).trans hword
  have controls : p^(r-1)+A.J+16≤word maps τ I A seed positionCap D := by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega
  have wp : p≤word maps τ I A seed positionCap D := by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega
  have wB : LightTernaryAppendKeys.word (A.J+2) p D.bB (p^(r-1))≤word maps τ I A seed positionCap D := by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega
  have wC : LightTernaryAppendKeys.word (A.J+2) p D.bC (p^(r-1))≤word maps τ I A seed positionCap D := by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega
  have wO : LightTernaryAppendKeys.word (A.J+2) p D.bO (p^(r-1))≤word maps τ I A seed positionCap D := by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega
  have app : AppendGuard (config p r I A seed) D lim depth μ := {
    spaceWord:=hw
    depth:=by omega
    matrixB:=M.matrixB.trans before16
    matrixC:=M.matrixC.trans before16
    matrixO:=M.matrixO.trans before16
    rowBefore:=M.menu.trans before16
    oldB:=before (by decide) hnB
    oldC:=before (by decide) hnC
    oldO:=before (by decide) hnO
    BC:=before (by decide) hnB
    CO:=before (by decide) hnC
    outScratch:=before (by decide) hnO
    scratchSpace:=region_space (by decide) hJ hend
    bB:=M.bB
    bC:=M.bC
    bO:=M.bO
    Bword:=numWord _ wB
    Cword:=numWord _ wC
    Oword:=numWord _ wO
    Bbound:=M.Bbound
    Cbound:=M.Cbound
    Obound:=M.Obound
    coeffBound:=M.coeffBound
    oldBBound:=M.oldB
    oldCBound:=M.oldC
    oldOBound:=M.oldO
    BRead:=M.BRead
    CRead:=M.CRead
    ORead:=M.ORead
    coeffRead:=M.coeffRead
    oldBRead:=M.oldBRead
    oldCRead:=M.oldCRead
    oldORead:=M.oldORead }
  have span : SpanGuard (config p r I A seed) D lim μ := {
    represents:=M.represents
    catalogSpace:=region_space (by decide) hspan hend
    controls:=numWord _ controls
    pword:=numWord _ wp
    bounded:=M.catalogBound
    read:=M.catalogRead
    digits:=M.digits }
  have capPos : 1≤F*TernaryGoodOutputCatalog.cap m p τ := by
    have hp := TernaryGoodOutputCatalog.cap_pos (m := m) (p := p) hτ
    nlinarith
  have rawBound : ∀i<(TernaryGoodOutputCatalog.raws maps τ).length,
      |(TernaryGoodOutputCatalog.raws maps τ).getD i 0|≤(rawCap m p r : ℤ) := by
    intro i hi
    have him : i<(TernaryGoodOutputCatalog.records maps τ).length := by simpa using hi
    rw [List.getD_eq_getElem _ _ hi]
    simp only [TernaryGoodOutputCatalog.raws,List.getElem_map]
    have hb := TernaryGoodOutputCatalog.key_bounds maps (TernaryGoodOutputCatalog.records maps τ)[i]
    rw [abs_of_nonneg hb.1]
    apply hb.2.le.trans
    exact_mod_cast (show p≤rawCap m p r by unfold rawCap; exact Nat.le_mul_of_pos_right _ (by positivity))
  have wanted : WantedGuard (config p r I A seed) D lim depth (4^fixedLength m) F
      (F*TernaryGoodOutputCatalog.cap m p τ) (rawCap m p r)
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ := {
    prime:=(Fact.out : p.Prime).two_le
    nonempty:=hraw
    Rpos:=Nat.succ_le_of_lt (by positivity)
    Spos:=by omega
    capPos:=capPos
    capBound:=by simpa only [config,Fintype.card_fin] using TernaryGoodOutputCatalog.localBucket_cap maps τ
    rawBound:=rawBound
    wordBound:=TernaryGoodOutputCatalog.wordCodes_bound maps τ
    mapBound:=TernaryGoodOutputCatalog.mapCodes_bound maps τ
    Rword:=numWord _ (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
    Sword:=numWord _ (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
    Nword:=numWord _ (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
    division:={
      mod_pos:=by
        change 1≤p
        have := (Fact.out : p.Prime).two_le
        omega
      space:=hw
      word:=by
        change 4*(2*(rawCap m p r : ℤ))+4*(p : ℤ)+16≤_
        have hh := numWord (8*rawCap m p r+4*p+16) (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
        push_cast at hh
        nlinarith
      free:=region_space (by decide) hdiv hend}
    targetEnd:=before (by decide) hnO
    positionsEnd:=M.positions.trans before16
    positionsRead:=M.positionRead
    targetBound:=by
      intro i hi
      change |(D.newO i : ℤ)|≤_
      rw [Int.abs_natCast]
      have hh := LightTernaryAppendKeys.key_lt p (p^(r-1)) (A.J+2) D.oldO D.O D.coeff i
        (Fact.out : p.Prime).pos (M.oldO i hi)
      apply (Int.ofNat_le.mpr hh.le).trans
      have hp1 := Nat.pow_le_pow_left (show p≤p+1 by omega) (r-1)
      have hp2 := Nat.pow_le_pow_right (show 1≤p+1 by omega) (show r-1≤r by omega)
      exact_mod_cast (show p^(r-1)*p≤rawCap m p r by unfold rawCap; nlinarith)
    codesWord:=numWord ((2*(4^fixedLength m))^r) (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
    mapsWord:=numWord ((2*F)^r) (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
    positionsWord:=fun i hi => (Int.ofNat_le.mpr (M.positionBound i hi)).trans (numWord _ (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega))
    prefixWord:=numWord r (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
    outputSpace:=before (by decide) hwanted
    depth:=by change depth+r+5≤lim.depth; omega }
  refine ⟨app,span,wanted,?_⟩
  refine {
    histogramAfter:=?_
    histogramSpace:=region_space (by decide) hhist hend
    Bword:=numWord (I.nB*I.nB+I.nB+p^(r-1)*p+16) (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega)
    Cword:=numWord (I.nC*I.nC+I.nC+p^(r-1)*p+16) (by unfold word; generalize p^(r-1)=pp; generalize 4^fixedLength m=rr; generalize (2*rr)^r=rpow; generalize (2*F)^r=fpow; omega) }
  have hlen := LightTernaryWantedBatch.rows_length_le p (4^fixedLength m) F r
    (F*TernaryGoodOutputCatalog.cap m p τ) (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ)
    D.targets D.position wanted.capBound I.requesterCount
  exact before (by decide) (hlen.trans hwanted)

end ThreeSum.TernaryArenaSeedPrimitiveGuards
