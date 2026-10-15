import Submission.ThreeSum.LightTernarySeedScore
import Submission.ThreeSum.TernaryPhysicalDigitSpan
import Submission.ThreeSum.TernaryWantedBatchCount
import Submission.ThreeSum.LightTernaryTensorFactoryScaled
import Submission.ThreeSum.TernaryNativeTensorScore

/-! A candidate execution is derived from pure finite data, actual array
reads, scalar resources, and the concrete tensor readiness certificate.
No component execution receipt is a field of the factory guard. -/
noncomputable section
namespace ThreeSum.LightTernarySeedScoreFactory
open Light
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

structure Config where
  menu : ℕ
  seed : ℕ
  J : ℕ
  catalog : ℕ
  catalogRows : ℕ
  p : ℕ
  power : ℕ
  Bmatrix : ℕ
  Bold : ℕ
  Bnew : ℕ
  nB : ℕ
  Cmatrix : ℕ
  Cold : ℕ
  Cnew : ℕ
  nC : ℕ
  Omatrix : ℕ
  Oold : ℕ
  Onew : ℕ
  nO : ℕ
  positions : ℕ
  wanted : ℕ
  work : ℕ
  hashWork : ℕ
  hist : ℕ
  header : ℕ
  leftTagged : ℕ
  rightTagged : ℕ
  leftWeights : ℕ
  rightWeights : ℕ
  tensor : ℕ
  countOutput : ℕ
  quadScratch : ℕ
  quadPowers : ℕ
  potentialColumns : ℕ
  potentialPowers : ℕ
  flags : ℕ
  scoreB : ℕ
  scoreC : ℕ
  scorePaired : ℕ
  prefixLength : ℕ

def Config.argv (C : Config) : List ℤ :=
  LightTernarySeedScore.args C.menu C.seed C.J C.catalog C.catalogRows C.p C.power
    C.Bmatrix C.Bold C.Bnew C.nB C.Cmatrix C.Cold C.Cnew C.nC C.Omatrix C.Oold C.Onew C.nO
    C.positions C.wanted C.work C.hashWork C.hist C.header C.leftTagged C.rightTagged
    C.leftWeights C.rightWeights C.tensor C.countOutput C.quadScratch C.quadPowers
    C.potentialColumns C.potentialPowers C.flags C.scoreB C.scoreC C.scorePaired C.prefixLength

def Config.row (C : Config) := C.menu+C.seed*(C.J+2)

structure Data (C : Config) where
  oldB : ℕ → ℕ
  oldC : ℕ → ℕ
  oldO : ℕ → ℕ
  B : ℕ → ℕ → ℤ
  Cvalues : ℕ → ℕ → ℤ
  O : ℕ → ℕ → ℤ
  coeff : ℕ → ℕ
  position : ℕ → ℕ
  catalog : ℕ → ℕ → ℕ
  logicalRows : List (Fin C.J → ZMod C.p)
  logicalRow : Fin (C.J+2) → ZMod C.p
  bB : ℕ
  bC : ℕ
  bO : ℕ

def Data.newB {C : Config} (D : Data C) :=
  LightTernaryAppendKeys.key C.p C.power (C.J+2) D.oldB D.B D.coeff

def Data.newC {C : Config} (D : Data C) :=
  LightTernaryAppendKeys.key C.p C.power (C.J+2) D.oldC D.Cvalues D.coeff

def Data.newO {C : Config} (D : Data C) :=
  LightTernaryAppendKeys.key C.p C.power (C.J+2) D.oldO D.O D.coeff

def Data.targets {C : Config} (D : Data C) (i : ℕ) : ℤ := D.newO i

def Data.flag {C : Config} [Fact C.p.Prime] (D : Data C) : ℤ :=
  LightStoredSpan.admissibleFlag (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J))
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)

def Data.collisionB {C : Config} (D : Data C) : ℤ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin C.nB => D.newB i.val)).card

def Data.collisionC {C : Config} (D : Data C) : ℤ :=
  (TernaryOriginalCollisions.collisionPairs (fun i : Fin C.nC => D.newC i.val)).card

def Data.wantedRows {C : Config} (D : Data C) (R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :=
  LightTernaryWantedBatch.rows C.p R S C.prefixLength raws words maps D.targets D.position C.nO

def Data.H {C : Config} (D : Data C) (R S : ℕ) (raws : List ℤ) (words maps : List ℕ) :=
  TernaryWantedBatchCount.count C.p R S C.prefixLength raws words maps D.targets C.nO

def Reads (μ : ℕ → ℤ) (base n : ℕ) (f : ℕ → ℕ) := ∀i<n, μ (base+i)=(f i : ℤ)

def BuiltB (C : Config) (D : Data C) (μ ν : ℕ → ℤ) : Prop :=
  Kept μ ν C.Bnew ∧ Reads ν C.Bnew C.nB D.newB

def BuiltC (C : Config) (D : Data C) (μ ν : ℕ → ℤ) : Prop :=
  BuiltB C D μ ν ∧ Reads ν C.Cnew C.nC D.newC

def BuiltO (C : Config) (D : Data C) (μ ν : ℕ → ℤ) : Prop :=
  BuiltC C D μ ν ∧ Reads ν C.Onew C.nO D.newO

def Built (C : Config) (D : Data C) (R S : ℕ) (raws : List ℤ) (words maps : List ℕ)
    (μ ν : ℕ → ℤ) : Prop :=
  BuiltO C D μ ν ∧ Seg ν C.wanted (D.wantedRows R S raws words maps)

/-- All preexisting arrays used by the three append calls are immutable
below the first destination. The destinations themselves are ordered. -/
structure AppendGuard (C : Config) (D : Data C) (lim : Limits) (depth : ℕ) (μ : ℕ → ℤ) : Prop where
  spaceWord : (lim.space : ℤ)≤lim.word
  depth : depth+4<lim.depth
  matrixB : C.Bmatrix+C.nB*(C.J+2)≤C.Bnew
  matrixC : C.Cmatrix+C.nC*(C.J+2)≤C.Bnew
  matrixO : C.Omatrix+C.nO*(C.J+2)≤C.Bnew
  rowBefore : C.row+(C.J+2)≤C.Bnew
  oldB : C.Bold+C.nB≤C.Bnew
  oldC : C.Cold+C.nC≤C.Bnew
  oldO : C.Oold+C.nO≤C.Bnew
  BC : C.Bnew+C.nB≤C.Cnew
  CO : C.Cnew+C.nC≤C.Onew
  outScratch : C.Onew+C.nO≤C.hashWork
  scratchSpace : C.hashWork+(C.J+2)≤lim.space
  bB : D.bB<C.p
  bC : D.bC<C.p
  bO : D.bO<C.p
  Bword : (LightTernaryAppendKeys.word (C.J+2) C.p D.bB C.power : ℤ)≤lim.word
  Cword : (LightTernaryAppendKeys.word (C.J+2) C.p D.bC C.power : ℤ)≤lim.word
  Oword : (LightTernaryAppendKeys.word (C.J+2) C.p D.bO C.power : ℤ)≤lim.word
  Bbound : ∀i<C.nB, ∀k<C.J+2, |D.B i k|≤(D.bB : ℤ)
  Cbound : ∀i<C.nC, ∀k<C.J+2, |D.Cvalues i k|≤(D.bC : ℤ)
  Obound : ∀i<C.nO, ∀k<C.J+2, |D.O i k|≤(D.bO : ℤ)
  coeffBound : ∀k<C.J+2, D.coeff k≤C.p
  oldBBound : ∀i<C.nB, D.oldB i<C.power
  oldCBound : ∀i<C.nC, D.oldC i<C.power
  oldOBound : ∀i<C.nO, D.oldO i<C.power
  BRead : ∀i<C.nB, ∀k<C.J+2, μ (C.Bmatrix+i*(C.J+2)+k)=D.B i k
  CRead : ∀i<C.nC, ∀k<C.J+2, μ (C.Cmatrix+i*(C.J+2)+k)=D.Cvalues i k
  ORead : ∀i<C.nO, ∀k<C.J+2, μ (C.Omatrix+i*(C.J+2)+k)=D.O i k
  coeffRead : ∀k<C.J+2, μ (C.row+k)=(D.coeff k : ℤ)
  oldBRead : Reads μ C.Bold C.nB D.oldB
  oldCRead : Reads μ C.Cold C.nC D.oldC
  oldORead : Reads μ C.Oold C.nO D.oldO

variable {lim : Limits}

theorem AppendGuard.runB {C : Config} {D : Data C} {depth : ℕ} {μ : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) :
    Meets lim LightTernaryAppendKeys.program 6 (depth+1)
      [C.Bmatrix,C.row,C.Bold,C.Bnew,C.nB,C.J+2,C.p,C.power,C.hashWork] μ
      (LightTernaryAppendKeys.time C.nB (C.J+2) C.p D.bB)
      (fun _ ν => BuiltB C D μ ν) := by
  have hh := LightTernaryAppendKeys.procs.meets (depth := depth+1) (matrix := C.Bmatrix) (row := C.row) (oldBase := C.Bold) (dst := C.Bnew) (scratch := C.hashWork) μ D.oldB D.B D.coeff
    G.spaceWord (by have := G.depth; omega) G.bB G.matrixB G.rowBefore G.oldB
    (by have := G.BC; have := G.CO; have := G.outScratch; omega) G.scratchSpace
    G.BRead G.coeffRead G.oldBRead G.Bbound G.coeffBound G.oldBBound G.Bword
  exact hh.mono le_rfl (fun _ ν h => ⟨h.2,h.1⟩)

theorem AppendGuard.runC {C : Config} {D : Data C} {depth : ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : BuiltB C D μ ν) :
    Meets lim LightTernaryAppendKeys.program 6 (depth+1)
      [C.Cmatrix,C.row,C.Cold,C.Cnew,C.nC,C.J+2,C.p,C.power,C.hashWork] ν
      (LightTernaryAppendKeys.time C.nC (C.J+2) C.p D.bC)
      (fun _ ξ => BuiltC C D μ ξ) := by
  have hh := LightTernaryAppendKeys.procs.meets (depth := depth+1) (matrix := C.Cmatrix) (row := C.row) (oldBase := C.Cold) (dst := C.Cnew) (scratch := C.hashWork) ν D.oldC D.Cvalues D.coeff
    G.spaceWord (by have := G.depth; omega) G.bC (by have := G.matrixC; have := G.BC; omega)
    (by have := G.rowBefore; have := G.BC; omega) (by have := G.oldC; have := G.BC; omega)
    (by have := G.CO; have := G.outScratch; omega) G.scratchSpace
    (by intro i hi k hk; rw [H.1 _ (by have := G.matrixC; nlinarith),G.CRead i hi k hk])
    (by intro k hk; rw [H.1 _ (by have := G.rowBefore; omega),G.coeffRead k hk])
    (by intro i hi; rw [H.1 _ (by have := G.oldC; omega),G.oldCRead i hi])
    G.Cbound G.coeffBound G.oldCBound G.Cword
  apply hh.mono le_rfl
  intro _ ξ h
  refine ⟨⟨?_,?_⟩,h.1⟩
  · intro x hx; rw [h.2 x (by have := G.BC; omega),H.1 x hx]
  · intro i hi; rw [h.2 _ (by have := G.BC; omega),H.2 i hi]

theorem AppendGuard.runO {C : Config} {D : Data C} {depth : ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : BuiltC C D μ ν) :
    Meets lim LightTernaryAppendKeys.program 6 (depth+1)
      [C.Omatrix,C.row,C.Oold,C.Onew,C.nO,C.J+2,C.p,C.power,C.hashWork] ν
      (LightTernaryAppendKeys.time C.nO (C.J+2) C.p D.bO)
      (fun _ ξ => BuiltO C D μ ξ) := by
  have hh := LightTernaryAppendKeys.procs.meets (depth := depth+1) (matrix := C.Omatrix) (row := C.row) (oldBase := C.Oold) (dst := C.Onew) (scratch := C.hashWork) ν D.oldO D.O D.coeff
    G.spaceWord (by have := G.depth; omega) G.bO
    (by have := G.matrixO; have := G.BC; have := G.CO; omega)
    (by have := G.rowBefore; have := G.BC; have := G.CO; omega)
    (by have := G.oldO; have := G.BC; have := G.CO; omega)
    G.outScratch G.scratchSpace
    (by intro i hi k hk; rw [H.1.1 _ (by have := G.matrixO; nlinarith),G.ORead i hi k hk])
    (by intro k hk; rw [H.1.1 _ (by have := G.rowBefore; omega),G.coeffRead k hk])
    (by intro i hi; rw [H.1.1 _ (by have := G.oldO; omega),G.oldORead i hi])
    G.Obound G.coeffBound G.oldOBound G.Oword
  apply hh.mono le_rfl
  intro _ ξ h
  refine ⟨⟨⟨?_,?_⟩,?_⟩,h.1⟩
  · intro x hx; rw [h.2 x (by have := G.BC; have := G.CO; omega),H.1.1 x hx]
  · intro i hi; rw [h.2 _ (by have := G.BC; have := G.CO; omega),H.1.2 i hi]
  · intro i hi; rw [h.2 _ (by have := G.CO; omega),H.2 i hi]


structure SpanGuard (C : Config) [Fact C.p.Prime] (D : Data C) (lim : Limits) (μ : ℕ → ℤ) : Prop where
  represents : TernaryStoredSpan.Represents D.catalog C.catalogRows
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J))
  catalogSpace : C.catalog+C.J*C.catalogRows≤lim.space
  controls : ((C.catalogRows+C.J+16 : ℕ) : ℤ)≤lim.word
  pword : (C.p : ℤ)≤lim.word
  bounded : ∀k<C.catalogRows, ∀i<C.J, D.catalog k i<C.p
  read : ∀k<C.catalogRows, ∀i<C.J, μ (C.catalog+C.J*k+i)=(D.catalog k i : ℤ)
  digits : ∀i<C.J, D.coeff i=LightStoredSpan.rowValues
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i

structure WantedGuard (C : Config) (D : Data C) (lim : Limits) (depth R S cap V : ℕ)
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ → ℤ) : Prop where
  prime : 2≤C.p
  nonempty : 1≤raws.length
  Rpos : 1≤R
  Spos : 1≤S
  capPos : 1≤cap
  capBound : ∀x, (TernaryWantedRadix.localBucket (C.p : ℤ) raws x).length≤cap
  rawBound : ∀i<raws.length, |raws.getD i 0|≤(V : ℤ)
  wordBound : ∀i<raws.length, words.getD i 0<R
  mapBound : ∀i<raws.length, maps.getD i 0<S
  Rword : (R : ℤ)≤lim.word
  Sword : (S : ℤ)≤lim.word
  Nword : (raws.length : ℤ)≤lim.word
  division : Emod.Pre lim C.p (2*V) C.work
  targetEnd : C.Onew+C.nO≤C.wanted
  positionsEnd : C.positions+C.nO≤C.Bnew
  positionsRead : ∀i<C.nO, μ (C.positions+i)=(D.position i : ℤ)
  targetBound : ∀i<C.nO, |D.targets i|≤(V : ℤ)
  codesWord : (((2*R)^C.prefixLength : ℕ) : ℤ)≤lim.word
  mapsWord : (((2*S)^C.prefixLength : ℕ) : ℤ)≤lim.word
  positionsWord : ∀i<C.nO, (D.position i : ℤ)≤lim.word
  prefixWord : (C.prefixLength : ℤ)≤lim.word
  outputSpace : C.wanted+3*C.nO*cap^C.prefixLength≤C.work
  depth : depth+C.prefixLength+5≤lim.depth

theorem BuiltO.transfer {C : Config} {D : Data C} {μ ν ξ : ℕ → ℤ} {cutoff depth : ℕ}
    (G : AppendGuard C D lim depth μ) (H : BuiltO C D μ ν) (K : Kept ν ξ cutoff)
    (hcut : C.Onew+C.nO≤cutoff) : BuiltO C D μ ξ := by
  refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
  · intro x hx; rw [K x (by have := G.BC; have := G.CO; omega),H.1.1.1 x hx]
  · intro i hi; rw [K _ (by have := G.BC; have := G.CO; omega),H.1.1.2 i hi]
  · intro i hi; rw [K _ (by have := G.CO; omega),H.1.2 i hi]
  · intro i hi; rw [K _ (by omega),H.2 i hi]

theorem runSpan {C : Config} [Fact C.p.Prime] {D : Data C} {depth : ℕ} {μ : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (H : SpanGuard C D lim μ) :
    Meets lim LightStoredSpan.program 6 (depth+1) [C.catalog,C.catalogRows,C.J,C.row] μ
      (LightSpanCatalogTest.time C.J C.catalogRows) (fun r ν => r=D.flag ∧ ν=μ) := by
  exact LightStoredSpan.program_admissible_meets μ D.catalog
    (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow)
    (D.logicalRows.map (TernaryPhysicalDigitSpan.reversal C.J)) H.represents G.spaceWord H.catalogSpace
    (by have := G.rowBefore; have := G.BC; have := G.CO; have := G.outScratch; have := G.scratchSpace; omega)
    H.controls H.pword H.bounded H.read
    (by intro i hi; rw [G.coeffRead i (by omega),H.digits i hi]) (by have := G.depth; omega)

theorem runWanted {C : Config} {D : Data C} {depth R S cap V : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (H : BuiltO C D μ ν) :
    Meets lim (LightTernaryWantedBatch.program C.p R S raws words maps) 4 (depth+1)
      [C.prefixLength,C.Onew,C.positions,C.nO,C.wanted,C.work] ν
      (LightTernaryWantedBatch.time C.p cap V C.prefixLength C.nO)
      (fun r ξ => r=((C.wanted+3*D.H R S raws words maps : ℕ) : ℤ) ∧ Built C D R S raws words maps μ ξ) := by
  have hh := LightTernaryWantedBatch.program_meets (P := C.p) (R := R) (S := S) (C := cap)
    (V := V) (work := C.work) (J := C.prefixLength) (d := depth+1)
    (targetBase := C.Onew) (positionBase := C.positions) (n := C.nO) (dst := C.wanted)
    W.prime W.nonempty W.Rpos W.Spos W.capPos W.capBound W.rawBound W.wordBound W.mapBound
    W.Rword W.Sword W.Nword W.division ν D.targets D.position W.targetEnd
    (by have := W.positionsEnd; have := G.BC; have := G.CO; have := W.targetEnd; omega)
    H.2 (by intro i hi; rw [H.1.1.1 _ (by have := W.positionsEnd; omega),W.positionsRead i hi])
    W.targetBound W.codesWord W.mapsWord W.positionsWord W.prefixWord W.outputSpace (by have := W.depth; omega)
  apply hh.mono le_rfl
  rintro r ξ ⟨hr,hrows,hkeep⟩
  refine ⟨?_,?_,hrows⟩
  · simpa only [Data.H,TernaryWantedBatchCount.rows_length] using hr
  · refine ⟨⟨⟨?_,?_⟩,?_⟩,?_⟩
    · intro x hx; rw [hkeep x (by have := G.BC; have := G.CO; have := W.targetEnd; omega),H.1.1.1 x hx]
    · intro i hi; rw [hkeep _ (by have := G.BC; have := G.CO; have := W.targetEnd; omega),H.1.1.2 i hi]
    · intro i hi; rw [hkeep _ (by have := G.CO; have := W.targetEnd; omega),H.1.2 i hi]
    · intro i hi; rw [hkeep _ (by have := W.targetEnd; omega),H.2 i hi]


structure CollisionGuard (C : Config) (D : Data C) (lim : Limits) (R S : ℕ)
    (raws : List ℤ) (words maps : List ℕ) : Prop where
  histogramAfter : C.wanted+(D.wantedRows R S raws words maps).length≤C.hist
  histogramSpace : C.hist+C.power*C.p≤lim.space
  Bword : ((C.nB*C.nB+C.nB+C.power*C.p+16 : ℕ) : ℤ)≤lim.word
  Cword : ((C.nC*C.nC+C.nC+C.power*C.p+16 : ℕ) : ℤ)≤lim.word

theorem Built.transfer {C : Config} {D : Data C} {depth R S cap V cutoff : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν ξ : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (H : Built C D R S raws words maps μ ν) (K : Kept ν ξ cutoff)
    (hcut : C.wanted+(D.wantedRows R S raws words maps).length≤cutoff) :
    Built C D R S raws words maps μ ξ := by
  exact ⟨H.1.transfer G K (by have := W.targetEnd; omega),H.2.of_kept K hcut⟩

theorem runCollisionB {C : Config} [Fact C.p.Prime] {D : Data C} {depth R S cap V : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (X : CollisionGuard C D lim R S raws words maps) (H : Built C D R S raws words maps μ ν) :
    Meets lim LightOriginalCollisionScore.program 0 (depth+1) [C.Bnew,C.nB,C.hist,C.power*C.p] ν
      (LightOriginalCollisionScore.time C.nB (C.power*C.p))
      (fun r ξ => r=D.collisionB ∧ Built C D R S raws words maps μ ξ) := by
  have hEnd : C.Bnew+C.nB≤C.hist := by
    have := G.BC; have := G.CO; have := W.targetEnd; have := X.histogramAfter; omega
  have hh := LightOriginalCollisionScore.program_meets (d := depth+1) (src := C.Bnew)
    (n := C.nB) (hist := C.hist) (q := C.power*C.p) ν D.newB G.spaceWord
    (by have := X.histogramSpace; omega) X.histogramSpace (Or.inl hEnd) X.Bword
    (by intro i hi; exact LightTernaryAppendKeys.key_lt _ _ _ _ _ _ i (Fact.out : C.p.Prime).pos (G.oldBBound i hi))
    H.1.1.1.2 (by have := G.depth; omega)
  apply hh.mono le_rfl
  rintro r ξ ⟨hr,hCounts,hKeep⟩
  exact ⟨hr,H.transfer G W (fun x hx => hKeep x (Or.inl hx)) X.histogramAfter⟩

theorem runCollisionC {C : Config} [Fact C.p.Prime] {D : Data C} {depth R S cap V : ℕ}
    {raws : List ℤ} {words maps : List ℕ} {μ ν : ℕ → ℤ}
    (G : AppendGuard C D lim depth μ) (W : WantedGuard C D lim depth R S cap V raws words maps μ)
    (X : CollisionGuard C D lim R S raws words maps) (H : Built C D R S raws words maps μ ν) :
    Meets lim LightOriginalCollisionScore.program 0 (depth+1) [C.Cnew,C.nC,C.hist,C.power*C.p] ν
      (LightOriginalCollisionScore.time C.nC (C.power*C.p))
      (fun r ξ => r=D.collisionC ∧ Built C D R S raws words maps μ ξ) := by
  have hEnd : C.Cnew+C.nC≤C.hist := by
    have := G.CO; have := W.targetEnd; have := X.histogramAfter; omega
  have hh := LightOriginalCollisionScore.program_meets (d := depth+1) (src := C.Cnew)
    (n := C.nC) (hist := C.hist) (q := C.power*C.p) ν D.newC G.spaceWord
    (by have := X.histogramSpace; omega) X.histogramSpace (Or.inl hEnd) X.Cword
    (by intro i hi; exact LightTernaryAppendKeys.key_lt _ _ _ _ _ _ i (Fact.out : C.p.Prime).pos (G.oldCBound i hi))
    H.1.1.2 (by have := G.depth; omega)
  apply hh.mono le_rfl
  rintro r ξ ⟨hr,hCounts,hKeep⟩
  exact ⟨hr,H.transfer G W (fun x hx => hKeep x (Or.inl hx)) X.histogramAfter⟩


structure Ready (C : Config) [Fact C.p.Prime] (D : Data C) (lim : Limits)
    (depth R mapRadix cap V K N U : ℕ) (host : TernarySourceCountExecutionFactory.Setup N)
    (L Rvalues : ℕ → ℕ → ℤ) (scoreBound : ℤ)
    (raws : List ℤ) (words maps : List ℕ) (μ : ℕ → ℤ) : Prop where
  append : AppendGuard C D lim depth μ
  span : SpanGuard C D lim μ
  wanted : WantedGuard C D lim depth R mapRadix cap V raws words maps μ
  collision : CollisionGuard C D lim R mapRadix raws words maps
  leftN : host.left.NL=C.nB
  rightN : host.right.NL=C.nC
  count : host.front.count=D.H R mapRadix raws words maps
  countOutput : host.front.dst=C.countOutput
  leftWeights : host.left.weightBase=C.leftWeights
  rightWeights : host.right.weightBase=C.rightWeights
  headerBefore : C.header+106≤C.Bnew
  tensorAfter : C.Bnew≤C.tensor
  tensor : ∀ν, Built C D R mapRadix raws words maps μ ν →
    LightTernaryTensorFactory.Ready host lim (depth+1) K C.J C.header C.leftTagged C.rightTagged
      C.tensor C.quadScratch C.quadPowers C.potentialColumns C.potentialPowers
      (Function.update ν (C.header+104) (D.H R mapRadix raws words maps : ℤ)) L Rvalues U scoreBound
  flagAddr : C.flags+C.seed<lim.space
  BAddr : C.scoreB+C.seed<lim.space
  CAddr : C.scoreC+C.seed<lim.space
  PAddr : C.scorePaired+C.seed<lim.space
  BWord : |D.collisionB|≤lim.word
  CWord : |D.collisionC|≤lim.word
  divideWord : ((3*D.H R mapRadix raws words maps+5 : ℕ) : ℤ)≤lim.word

/-- The preserved immutable input prefix permits the one actual dynamic
wanted-count update to header cell104. -/
def KeptInput (C : Config) (μ ν : ℕ → ℤ) : Prop :=
  ∀x<C.Bnew, x≠C.header+104 → ν x=μ x

def runtime {C : Config} (D : Data C) {N : ℕ} (host : TernarySourceCountExecutionFactory.Setup N)
    (K R mapRadix cap V : ℕ) (raws : List ℤ) (words maps : List ℕ) : ℕ :=
  LightTernarySeedScore.time (LightSpanCatalogTest.time C.J C.catalogRows)
    (LightTernaryAppendKeys.time C.nB (C.J+2) C.p D.bB)
    (LightTernaryAppendKeys.time C.nC (C.J+2) C.p D.bC)
    (LightTernaryAppendKeys.time C.nO (C.J+2) C.p D.bO)
    (LightTernaryWantedBatch.time C.p cap V C.prefixLength C.nO)
    (LightSmallDivide.time (3*D.H R mapRadix raws words maps) 3)
    (LightOriginalCollisionScore.time C.nB (C.power*C.p))
    (LightOriginalCollisionScore.time C.nC (C.power*C.p))
    (LightTernaryTensorDriver.time K C.J C.nB C.nC (D.H R mapRadix raws words maps) host.runtime)

open scoped BigOperators

theorem Ready.run {C : Config} [Fact C.p.Prime] {D : Data C}
    {depth R mapRadix cap V K N U a b : ℕ} {host : TernarySourceCountExecutionFactory.Setup N}
    {L Rvalues : ℕ → ℕ → ℤ} {scoreBound : ℤ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ → ℤ}
    (G : Ready C D lim depth R mapRadix cap V K N U host L Rvalues scoreBound raws words maps μ)
    (hleft : ∀pair∈host.left.records, TernaryBank.rank (host.front.E.word (host.left.key pair.2))=a)
    (hright : ∀pair∈host.right.records, TernaryBank.rank (host.front.E.word (host.right.key pair.2))=b)
    (hQ : ∀j<host.front.count, TernaryBank.rank (host.front.Q j)=a+b)
    (P : Fin host.front.count → Type*) [∀i, Fintype (P i)]
    (A B : ∀i, P i → Fin (C.J+2) → ℤ) (s : ℤ)
    (hModel : ∀(i : Fin host.front.count) (a b c e : Fin (C.J+2)),
      LightTernaryTensorFactory.score host C.J L Rvalues i.val
        (LightTernaryPairedPolynomial.tensorIndex (C.J+2) a.val b.val c.val e.val)=
        s*TernaryPairedTensor.tensor (A i) (B i) a b c e)
    (hPairedWord : |s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
      TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ)|≤lim.word) :
    Meets lim (LightTernarySeedScore.program C.p R mapRadix K raws words maps
      host.left.xs host.left.ys host.left.zs host.right.xs host.right.ys host.right.zs)
      164 depth C.argv μ (runtime D host K R mapRadix cap V raws words maps)
      (fun r ν => r=D.flag ∧ ∃ξ, KeptInput C μ ξ ∧ ν=
        Function.update (Function.update (Function.update (Function.update ξ
          (C.flags+C.seed) D.flag) (C.scoreB+C.seed) D.collisionB) (C.scoreC+C.seed) D.collisionC)
          (C.scorePaired+C.seed) (s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
            TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ))) := by
  let paired : ℤ := s^K*((∑i : Fin host.front.count, ∑e : Fin K→P i,
    TernaryPairedPotential.rowWeight (Sum.elim (fun j => A i (e j)) (fun j => B i (e j)))) : ℤ)
  have hSpace := G.append.scratchSpace
  have hBScratch := G.append.outScratch
  have hBC := G.append.BC
  have hCO := G.append.CO
  have hWanted := G.wanted.targetEnd
  have hHist := G.collision.histogramAfter
  have hHistSpace := G.collision.histogramSpace
  have hLen : C.J+2≤lim.space := by have := G.append.rowBefore; omega
  have hRow : C.row≤lim.space := by have := G.append.rowBefore; omega
  have hFlagWord : |D.flag|≤lim.word := by
    have hp := G.span.pword
    have hprime := (Fact.out : C.p.Prime).one_lt
    unfold Data.flag LightStoredSpan.admissibleFlag
    split_ifs <;> norm_num <;> omega
  have hHrows := TernaryWantedBatchCount.rows_length C.p R mapRadix C.prefixLength raws words maps
    D.targets D.position C.nO
  have hCursor : C.wanted+3*D.H R mapRadix raws words maps≤lim.space := by
    have hBound := LightTernaryWantedBatch.rows_length_le C.p R mapRadix C.prefixLength cap raws words maps
      D.targets D.position G.wanted.capBound C.nO
    change (D.wantedRows R mapRadix raws words maps).length=3*D.H R mapRadix raws words maps at hHrows
    rw [hHrows] at hHist
    omega
  have hTensor : ∀ν, Built C D R mapRadix raws words maps μ ν →
      Meets lim (LightTernaryTensorFactory.program host K) 138 (depth+1)
        [C.header,C.leftTagged,C.nB,C.rightTagged,C.nC,C.J,C.leftWeights,C.rightWeights,C.tensor,
          D.H R mapRadix raws words maps,C.countOutput,C.quadScratch,C.quadPowers,C.potentialColumns,C.potentialPowers]
        (Function.update ν (C.header+104) (D.H R mapRadix raws words maps : ℤ))
        (LightTernaryTensorDriver.time K C.J C.nB C.nC (D.H R mapRadix raws words maps) host.runtime)
        (fun r ξ => r=paired ∧ KeptInput C μ ξ) := by
    intro ν H
    have HT := G.tensor ν H
    have hh := HT.run_scaled hleft hright hQ P A B s hModel
    have hh' := hh.mono le_rfl (fun r ξ h => show r=paired ∧ KeptInput C μ ξ from ⟨h.1,by
      intro x hx hne
      have hquad : C.Bnew≤C.quadScratch := by have := HT.tensorEnd; have := G.tensorAfter; omega
      have he := h.2 x ⟨by omega,Or.inl (by have := G.tensorAfter; omega)⟩
      rw [Function.update_of_ne hne] at he
      exact he.trans (H.1.1.1.1 x hx)⟩)
    simpa only [G.leftN,G.rightN,G.leftWeights,G.rightWeights,G.count,G.countOutput] using hh'
  have hh := LightTernarySeedScore.program_meets (menu := C.menu) (seed := C.seed) (J := C.J)
    (catalog := C.catalog) (catalogRows := C.catalogRows) (p := C.p) (power := C.power)
    (Bmatrix := C.Bmatrix) (Bold := C.Bold) (Bnew := C.Bnew) (nB := C.nB)
    (Cmatrix := C.Cmatrix) (Cold := C.Cold) (Cnew := C.Cnew) (nC := C.nC)
    (Omatrix := C.Omatrix) (Oold := C.Oold) (Onew := C.Onew) (nO := C.nO)
    (positions := C.positions) (wanted := C.wanted) (work := C.work) (hashWork := C.hashWork)
    (hist := C.hist) (header := C.header) (leftTagged := C.leftTagged) (rightTagged := C.rightTagged)
    (leftWeights := C.leftWeights) (rightWeights := C.rightWeights) (tensor := C.tensor)
    (countOutput := C.countOutput) (quadScratch := C.quadScratch) (quadPowers := C.quadPowers)
    (potentialColumns := C.potentialColumns) (potentialPowers := C.potentialPowers)
    (flags := C.flags) (scoreB := C.scoreB) (scoreC := C.scoreC) (scorePaired := C.scorePaired)
    (prefixLength := C.prefixLength) (d := depth) (H := D.H R mapRadix raws words maps)
    raws words maps host.left.xs host.left.ys host.left.zs host.right.xs host.right.ys host.right.zs
    μ D.flag D.collisionB D.collisionC paired
    (BuiltB C D μ) (BuiltC C D μ) (BuiltO C D μ)
    (Built C D R mapRadix raws words maps μ) (Built C D R mapRadix raws words maps μ)
    (Built C D R mapRadix raws words maps μ) (KeptInput C μ)
    G.append.spaceWord hLen hRow (by omega) (by have := G.headerBefore; omega) hCursor G.divideWord
    G.flagAddr G.BAddr G.CAddr G.PAddr hFlagWord G.BWord G.CWord hPairedWord
    (by have := G.append.depth; omega) le_rfl (runSpan G.append G.span) G.append.runB
    (fun ν H => G.append.runC H) (fun ν H => G.append.runO H)
    (fun ν H => runWanted G.append G.wanted H)
    (fun ν H => runCollisionB G.append G.wanted G.collision H)
    (fun ν H => runCollisionC G.append G.wanted G.collision H) hTensor
  exact hh


theorem Data.flag_eq_one {C : Config} [Fact C.p.Prime] (D : Data C) :
    D.flag=1 ↔ D.logicalRow∉TernaryPhysicalDigitSpan.forbidden D.logicalRows := by
  unfold flag
  rw [Nat.cast_eq_one,LightStoredSpan.admissibleFlag_eq_one]
  exact not_congr (TernaryPhysicalDigitSpan.physical_span_iff D.logicalRows D.logicalRow)


/-- Original-pair semantics require only the actual homogeneous output type;
no external finite tensor-model equality is supplied. -/
theorem Ready.run_native {C : Config} [Fact C.p.Prime] {D : Data C}
    {depth R mapRadix cap V K N U a b t : ℕ} {host : TernarySourceCountExecutionFactory.Setup N}
    {L Rvalues : ℕ → ℕ → ℤ} {scoreBound : ℤ} {raws : List ℤ} {words maps : List ℕ} {μ : ℕ → ℤ}
    (G : Ready C D lim depth R mapRadix cap V K N U host L Rvalues scoreBound raws words maps μ)
    (hleft : ∀pair∈host.left.records, TernaryBank.rank (host.front.E.word (host.left.key pair.2))=a)
    (hright : ∀pair∈host.right.records, TernaryBank.rank (host.front.E.word (host.right.key pair.2))=b)
    (hQ : ∀j<host.front.count, TernaryBank.rank (host.front.Q j)=a+b)
    (hcountTwo : ∀j<host.front.count, TernaryJointType.digitCount (host.front.Q j) 2=t)
    (hPairedWord : |((2 : ℤ)^t)^K*(TernaryNativeTensorScore.pairedPotential host K C.J L Rvalues : ℤ)|≤lim.word) :
    Meets lim (LightTernarySeedScore.program C.p R mapRadix K raws words maps
      host.left.xs host.left.ys host.left.zs host.right.xs host.right.ys host.right.zs)
      164 depth C.argv μ (runtime D host K R mapRadix cap V raws words maps)
      (fun r ν => r=D.flag ∧ ∃ξ, KeptInput C μ ξ ∧ ν=
        Function.update (Function.update (Function.update (Function.update ξ
          (C.flags+C.seed) D.flag) (C.scoreB+C.seed) D.collisionB) (C.scoreC+C.seed) D.collisionC)
          (C.scorePaired+C.seed) (((2 : ℤ)^t)^K*(TernaryNativeTensorScore.pairedPotential host K C.J L Rvalues : ℤ))) := by
  have hh := G.run hleft hright hQ
    (fun i : Fin host.front.count => TernaryNativePairMoments.Pair host i.val)
    (fun i => TernaryNativeTensorScore.originalLeft host C.J L i.val)
    (fun i => TernaryNativeTensorScore.originalRight host C.J Rvalues i.val) ((2 : ℤ)^t)
    (by
      intro i a b c e
      rw [TernaryNativeTensorScore.score_eq_original_tensor,TernaryConvolution.factorial_eq_power_two,
        hcountTwo i.val i.isLt])
    (by simpa only [TernaryNativeTensorScore.pairedPotential,Nat.cast_sum] using hPairedWord)
  simpa only [TernaryNativeTensorScore.pairedPotential,Nat.cast_sum] using hh

end ThreeSum.LightTernarySeedScoreFactory
