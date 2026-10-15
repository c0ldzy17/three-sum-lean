import Submission.ThreeSum.TernaryArenaLoopState

noncomputable section
namespace ThreeSum.TernaryArenaLoop
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryArenaLayout
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSeedData
open TernaryArenaSelectedBudgets TernaryArenaAllocation TernaryArenaPrefixInputs
open LightTernarySeedScoreFactory LightTernaryControllerFactory
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
variable {p m F K N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

/-- Every premise concerns actual input reads, fixed finite mathematics, or
explicit integer resource bounds. No execution or kernel-read callback. -/
structure Ready (S : Setup p m F K N E) (lim : Limits) (depth : ℕ) : Prop where
  hardware : (TernaryArenaAllocationResources.need S.allocation S.n S.U).Ok lim S.input.free (depth+2)
  capacity : S.input.capacity=capacity S.allocation.D S.allocation.E (S.n+S.U)
  mpos : 0<m
  rounds : S.rounds≤Nat.clog S.M (S.n^2)
  roundsPositive : 0<S.rounds
  dimension : S.arrays.J=LightTernaryDimensions.J S.M S.radix S.n S.U
  belowDimension : S.rounds≤S.arrays.J
  leftCount : S.input.nB≤S.n
  rightCount : S.input.nC≤S.n
  targetCount : S.input.requesterCount≤S.n*2^(LightTernaryDimensions.J S.M S.radix S.n S.U)
  positions : S.positionCap≤S.n
  seeds : N≤(p^(LightTernaryDimensions.dim S.M S.radix p K S.n S.U))^2
  weights : S.input.weightCap≤TernaryArenaPrefixFootprints.weight S.H S.wordRadix S.U
  tags : S.tagBound≤2*S.wordRadix+1
  weightLower : S.tagBound^2≤S.input.weightCap
  prefixAt : S.input.prefixFree=addr S.input.free S.input.capacity 13
  family : 1<F
  locals : ∀right,0<(TernaryNativeCompleteFrontend.localRecords S.maps S.cap right).length
  queryTime : ∀j<S.rounds,TernaryArenaCountReady.queryTime (m:=m) (r:=j+1) S.input
    (valueCap (r:=j+1) S.maps S.cap S.input)≤S.input.queryTime
  originals : Originals S.input S.arrays N S.featureBound S.tagBound S.positionCap S.ell
    (TernaryArenaFamilyBudget.seedAt S.enumeration) S.L S.R S.O S.initial
  prepareEnvelope : ∀j<S.rounds,TernaryArenaPrefixPrepare.envelope (S.prefixInput j)≤S.input.capacity
  selectorWord : ∀j<S.rounds,(LightTernaryRowSelector.word N
    (TernaryArenaPrefixFootprints.numbers S.maps S.threshold S.cap S.M S.radix K S.H S.drift S.scale S.n S.U (j+1)).candidateScore
    (p^(j+1)) (p^(j+1)) (S.alpha^(j+1)) (9^(j+1)*S.n^2) (9^(j+1)*S.n^2)
    (S.U0*(S.beta*S.budgetScale)^(j+1)):ℤ)≤lim.word
  budgets : ∀j≤S.rounds,TernaryArenaSelectedBudgets.Budget S.maps S.threshold S.cap S.Q S.input S.arrays K S.n S.U0
    S.L S.R S.O j (S.state j)
  ellNonzero : S.ell≠0
  prime : 3≤p
  leftBound : ∀i (t : Fin (S.arrays.J+2)),(S.L i t.val).natAbs≤S.featureBound
  rightBound : ∀i (t : Fin (S.arrays.J+2)),(S.R i t.val).natAbs≤S.featureBound
  leftNonneg : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.L i t.val
  rightNonneg : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.R i t.val
  targetNonneg : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.O i t.val
  leftInjective : Function.Injective (fun i : Fin S.input.nB=>fun t : Fin (S.arrays.J+2)=>(S.L i.val t.val:ZMod p))
  rightInjective : Function.Injective (fun i : Fin S.input.nC=>fun t : Fin (S.arrays.J+2)=>(S.R i.val t.val:ZMod p))
  minor : (K+K).factorial*S.featureBound^(K+K)<p
  fieldSize1 : 8*(S.arrays.J+2)*p^2≤Fintype.card E
  fieldSize : 8*(S.arrays.J+2)*p^(2*(K+K))≤Fintype.card E
  threshold : 0<S.threshold
  nonempty : 1≤S.raws.length
  roundsWord : (S.rounds:ℤ)≤lim.word
  powerWords : ∀j≤S.rounds,((p^j:ℕ):ℤ)≤lim.word

/-- Every loop phase is the concrete canonical phase constructor. -/
def Ready.phaseAt {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) (j : ℕ) (hj : j<S.rounds) (μ : ℕ→ℤ) (h : Invariant S j μ) :=by
  let catalog:=Classical.choose h
  have hc:=Classical.choose_spec h
  have hg:=TernaryArenaPhaseBudget.good S.maps S.threshold S.cap S.tagBound S.Q S.input S.arrays j S.featureBound K S.n S.U0
    S.enumeration S.ell (S.state j) S.L S.R S.O catalog (H.budgets j hj.le)
    (hj.trans_le H.belowDimension) H.ellNonzero H.prime H.leftBound H.rightBound H.leftNonneg H.rightNonneg H.targetNonneg
    H.leftInjective H.rightInjective H.minor H.fieldSize1 H.fieldSize
  have hr:=H.rounds
  exact TernaryArenaPhase.phase (depth:=depth+1) S.maps S.threshold S.cap S.Q S.allocation S.input S.arrays S.ell
    (TernaryArenaFamilyBudget.seedAt S.enumeration) S.L S.R S.O (S.state j) catalog S.initial μ
    H.hardware H.capacity H.mpos (by omega) H.dimension H.leftCount H.rightCount H.targetCount H.positions H.seeds H.weights
    H.tags H.weightLower H.prefixAt H.family H.locals (H.queryTime j hj) H.originals hc.1 hc.2.2.1 hc.2.1
    (H.prepareEnvelope j hj) H.threshold H.nonempty (H.selectorWord j hj) hg

theorem Ready.phaseAt_time {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) (j : ℕ) (hj : j<S.rounds) (μ : ℕ→ℤ) (h : Invariant S j μ) :
    (H.phaseAt j hj μ h).time=S.timeAt j :=by
  rfl

theorem Ready.capacities {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) (j : ℕ) (hj : j<S.rounds) :
    106≤S.input.capacity ∧ S.input.nB≤S.input.capacity ∧ S.input.nC≤S.input.capacity ∧
    S.input.requesterCount≤S.input.capacity ∧ S.arrays.J*p^j≤S.input.capacity ∧
    S.arrays.J*p^j*p≤S.input.capacity :=by
  have hr:=H.rounds
  have HC : TernaryArenaPrefixFootprints.Fits S.input.capacity
    (TernaryArenaPrefixFootprints.numbers S.maps S.threshold S.cap S.M S.radix K S.H S.drift S.scale S.n S.U (j+1)):=by
    rw [H.capacity];exact S.allocation.fits S.n S.U (j+1) (by omega)
  have hsp:=TernaryArenaPrimitiveBounds.spatial (r:=j+1) S.maps S.threshold S.cap S.M S.radix K S.H S.drift S.scale
    S.input S.arrays S.n S.U H.dimension H.leftCount H.rightCount H.targetCount HC
  have h106 : 106≤S.input.capacity:=by
    have hh:=capacity_pos S.allocation.D S.allocation.E (S.n+S.U)
    rw [←H.capacity] at hh;omega
  refine ⟨h106,hsp.1,hsp.2.1,hsp.2.2.1,?_,?_⟩
  · simpa only [Nat.add_sub_cancel] using hsp.2.2.2.2.1
  · have hh:=HC.spanCells
    simpa only [TernaryArenaPrefixFootprints.numbers,←H.dimension,pow_succ,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using hh

/-- The complete semantic and physical invariant advances through the
literal phase's actual preparation, selected replay and two commits. -/
theorem Ready.transition {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) (j : ℕ) (hj : j<S.rounds) (μ : ℕ→ℤ) (h : Invariant S j μ)
    (ω : ℕ→ℤ) (hω : (H.phaseAt j hj μ h).Output ω) : Invariant S (j+1) ω :=by
  let catalog:=Classical.choose h
  have hc:=Classical.choose_spec h
  obtain ⟨h106,hB,hC,hO,hSpan,hSpanFull⟩:=H.capacities j hj
  obtain ⟨ν,HP,ξ,HF,HC,hSeed⟩:=hω
  have hp : LightTernaryPrefixStep.Prepared (S.prefixInput j) μ ν:=HP
  have hf : TernaryArenaControllerPlan.Final S.input (S.family j catalog) K S.wordRadix F
    (S.chosen j catalog) S.newSpan S.raws S.words S.mapCodes ν ξ:=HF
  have hcommitted : LightTernaryPrefixFinish.Committed (config p (j+1) S.input S.arrays 0)
    (p^(j+1)) S.newSpan ξ ω:=by
    change LightTernaryPrefixFinish.Committed (config p (j+1) S.input S.arrays 0) (p^j*p) S.newSpan ξ ω at HC
    simpa only [pow_succ] using HC
  have preparedMemory:=TernaryArenaPrefixState.prepared S.input S.arrays (fun i t=>S.L i t.val)
    (fun i t=>S.R i t.val) (fun i t=>S.O i t.val) j (S.state j) catalog S.initial μ ν (S.prefixInput j) hp
    rfl rfl rfl h106 hB hC hO hSpan hc.1
  have nextMemory:=TernaryArenaPrefixState.final_transition S.maps S.threshold S.cap S.valueTag S.V S.scoreBound S.tagBound
    S.Q S.input S.arrays j S.featureBound K S.n S.U0 S.wordRadix F S.enumeration S.ell S.L S.R S.O
    S.catalogs catalog S.raws S.words S.mapCodes S.initial ν ξ ω preparedMemory H.leftNonneg H.rightNonneg H.targetNonneg hSpanFull
    (by
      dsimp only [Setup.family,TernaryArenaPhase.family,TernaryArenaPhase.dataAt,Setup.state,Setup.newSpan,Setup.chosen,Setup.alpha,Setup.beta,Setup.budgetScale] at hf ⊢
      have hdata : TernaryArenaPhase.dataAt S.input S.arrays j S.featureBound S.ell
          (TernaryArenaFamilyBudget.seedAt S.enumeration) S.L S.R S.O (S.state j) catalog =
          (fun k => data S.input S.arrays j S.featureBound k S.ell
            (TernaryArenaFamilyBudget.seedAt S.enumeration k) (S.state j).row
            (fun i t=>S.L i t.val) (fun i t=>S.R i t.val) (fun i t=>S.O i t.val)
            (S.state j).rows catalog) := by funext k; rfl
      dsimp only [Setup.state] at hdata
      rw [hdata] at hf
      simpa only [TernaryArenaPhaseBudget.threshold] using hf)
    hcommitted
  obtain ⟨catalog',hm'⟩:=nextMemory
  have hframe:=TernaryArenaPhaseFrames.receipts S.Q h106 hp hf HC
  have hTemplate : Seg ω (addr S.input.free S.input.capacity 0)
      (TernaryArenaHeaderAgreement.templateValues S.input p m F):=by
    apply hc.2.2.1.congr
    intro i hi
    apply hframe
    apply Or.inl
    apply offset_lt hi
    rw [TernaryArenaHeaderAgreement.templateValues_length]
    exact h106
  refine ⟨catalog',hm',hSeed,hTemplate,?_⟩
  exact ⟨{
    before:=μ
    catalog:=catalog
    oldMemory:=hc.1
    oldTemplate:=hc.2.2.1
    preparedMemory:=ν
    prepared:=hp
    finalMemory:=ξ
    final:=hf
    committed:=hcommitted }⟩

def Ready.loopPlan {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) (μ : ℕ→ℤ) (hstart : Invariant S 0 μ) :=by
  have hd : depth<lim.depth:=by have hh:=H.hardware.depth;omega
  exact ({
    invariant:=Invariant S
    initial:=hstart
    roundsWord:=H.roundsWord
    depthBound:=hd
    powerWords:=H.powerWords
    inputs:=S.prefixInput
    arguments:=fun j _=>rfl
    powers:=fun j _=>by simp only [Setup.prefixInput,TernaryArenaPrefixPrepare.inputs,pow_succ]
    stages:=H.phaseAt
    costs:=fun j hj ν h=>by
      exact (le_of_eq (H.phaseAt_time j hj ν h)).trans
        (Finset.le_sup (f:=S.timeAt) (Finset.mem_range.mpr hj))
    transition:=H.transition } : LightTernaryPrefixPhases.LoopPlan lim S.rounds m F p
      (addr S.input.free S.input.capacity 3) (addr S.input.free S.input.capacity 0)
      (addr S.input.free S.input.capacity 1) (addr S.input.free S.input.capacity 13)
      (fixedAlpha m 2) (alphaRank m) (TernaryCodeSemantics.address S.Q.val) S.wordRadix S.arrays.J
      S.alpha S.beta S.budgetScale depth K S.wordRadix F S.stepTime S.raws S.words S.mapCodes
      ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap false).map (TernaryCanonicalDictionaries.native false S.maps))
      ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap false).map TernaryCanonicalDictionaries.wordCode)
      ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap false).map TernaryCanonicalDictionaries.mapCode)
      ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap true).map (TernaryCanonicalDictionaries.native true S.maps))
      ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap true).map TernaryCanonicalDictionaries.wordCode)
      ((TernaryNativeCompleteFrontend.localRecords S.maps S.cap true).map TernaryCanonicalDictionaries.mapCode) μ)

theorem Ready.start {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim depth) {μ ν : ℕ→ℤ}
    (hinit : LightTernaryPrefixInit.Initialized (config p 0 S.input S.arrays 0)
      (addr S.input.free S.input.capacity 3) (S.seedHeader 0) μ ν)
    (hkeep : Kept S.initial μ S.input.free)
    (hTemplate : Seg μ (addr S.input.free S.input.capacity 0)
      (TernaryArenaHeaderAgreement.templateValues S.input p m F)) : Invariant S 0 ν :=by
  have hc:=H.capacities 0 H.roundsPositive
  have HM:=TernaryArenaPrefixState.start_initialized (p:=p) S.input S.arrays (fun i t=>S.L i t.val)
    (fun i t=>S.R i t.val) (fun i t=>S.O i t.val) (S.seedHeader 0) μ ν hinit
  have template : Seg ν (addr S.input.free S.input.capacity 0)
      (TernaryArenaHeaderAgreement.templateValues S.input p m F):=by
    intro i hi
    have hx : addr S.input.free S.input.capacity 0+i<addr S.input.free S.input.capacity 1:=by
      apply offset_lt hi
      rw [TernaryArenaHeaderAgreement.templateValues_length]
      exact hc.1
    rw [hinit.2.2.2.2.2 _ (Or.inl (by unfold addr at *;omega))
      (Or.inl (by change addr S.input.free S.input.capacity 0+i<addr S.input.free S.input.capacity 4;unfold addr at *;omega))
      (Or.inl (by change addr S.input.free S.input.capacity 0+i<addr S.input.free S.input.capacity 7;unfold addr at *;omega))]
    exact hTemplate i hi
  exact ⟨(fun _ _=>0),HM.rebase hkeep,hinit.1,template,trivial⟩

/-- The entire actual 185-procedure prefix program, including zero
initialization, executes from real constructed control headers. -/
theorem Ready.init_meets {S : Setup p m F K N E} {lim : Limits} {depth : ℕ}
    (H : Ready S lim (depth+1)) (μ : ℕ→ℤ)
    (hkeep : Kept S.initial μ S.input.free)
    (hTemplate : Seg μ (addr S.input.free S.input.capacity 0)
      (TernaryArenaHeaderAgreement.templateValues S.input p m F))
    (hSeed : Seg μ (addr S.input.free S.input.capacity 2) (S.seedHeader 0)) :
    Meets lim S.program 182 depth S.initArgs μ S.initTime
      (fun z ν=>z=((p^S.rounds:ℕ):ℤ) ∧ Invariant S S.rounds ν) :=by
  have caps:=H.capacities 0 H.roundsPositive
  have h106:=caps.1
  have hB:=caps.2.1
  have hC:=caps.2.2.1
  have hO:=caps.2.2.2.1
  have hJ : S.arrays.J≤S.input.capacity:=by simpa using caps.2.2.2.2.1
  have hardware:=TernaryArenaAllocationResources.ok S.allocation H.hardware
  have hend : finish S.input.free S.input.capacity≤lim.space:=by simpa only [H.capacity] using hardware.1
  have hw:=hardware.2.2.2
  have hd : depth+1<lim.depth:=by have hh:=H.hardware.depth;omega
  have hs : Seg μ (addr S.input.free S.input.capacity 2)
      (LightTernaryPrefixFinish.header (config p 0 S.input S.arrays 0) N 1 1 1 (S.n^2) (S.n^2) S.U0 S.newSpan):=by
    simpa only [Setup.seedHeader,pow_zero,one_mul,mul_one] using hSeed
  have hi:=LightTernaryPrefixInit.meets μ hw
    (before (by decide : 2<3) (show 48≤S.input.capacity by omega))
    (before (by decide : 3<4) (show 48≤S.input.capacity by omega))
    (before (by decide : 4<5) hB) (before (by decide : 5<6) hC) (before (by decide : 6<7) hO)
    (region_space (by decide : 7<slots) hJ hend) rfl hd hs
    (fun ν hinit=>H.loopPlan ν (H.start (by simpa only [Setup.seedHeader,pow_zero,one_mul,mul_one] using hinit) hkeep hTemplate))
  apply hi.mono le_rfl
  rintro z ν ⟨hz,ω,hinit,hinv⟩
  exact ⟨hz,hinv⟩

end ThreeSum.TernaryArenaLoop
