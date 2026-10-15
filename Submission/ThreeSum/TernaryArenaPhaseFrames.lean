import Submission.ThreeSum.TernaryArenaPhase

noncomputable section
namespace ThreeSum.TernaryArenaPhaseFrames
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open LightTernarySeedScoreFactory LightTernaryControllerFactory
open TernaryArenaControllerPlan TernaryArenaScoreScan
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

/-- These are exactly the low immutable arena bands: the host template and
seed template/constants, before the live seed record at slot three. -/
def Stable (I : Input) (x : ℕ) : Prop :=
  x<addr I.free I.capacity 1 ∨
    (addr I.free I.capacity 2≤x ∧ x<addr I.free I.capacity 3)

/-- Real preparation, replay/span extension and commit receipts preserve
both immutable arena bands. This contains no execution or frame callback. -/
theorem receipts {I : Input} {A : Inputs} {j J n U0 a b scale K R S i : ℕ}
    {D : Family (config p (j+1) I A 0)} {μ ν ξ ω : ℕ→ℤ}
    {raws : List ℤ} {words maps : List ℕ}
    (Q : TernaryGoodOutputCatalog.Output m) (hcap : 106≤I.capacity)
    (HP : LightTernaryPrefixStep.Prepared
      (TernaryArenaPrefixPrepare.inputs p m F j J n U0 a b scale I
        Q) μ ν)
    (HF : Final I D K R S i (addr I.free I.capacity 8) raws words maps ν ξ)
    (HC : LightTernaryPrefixFinish.Committed (config p (j+1) I A 0) (p^j*p)
      (addr I.free I.capacity 8) ξ ω) :
    ∀x,Stable I x→ω x=μ x := by
  intro x hx
  have hx3 : x<addr I.free I.capacity 3 := by
    simp only [Stable,addr] at hx ⊢
    omega
  have hx4 : x<addr I.free I.capacity 4 := by unfold addr at *;omega
  have hx8 : x<addr I.free I.capacity 8 := by unfold addr at *;omega
  have hx13 : x<addr I.free I.capacity 13 := by unfold addr at *;omega
  have hxhost : x<addr I.free I.capacity 1 ∨ addr I.free I.capacity 1+106≤x := by
    simp only [Stable,addr] at hx ⊢
    omega
  have hprotect : Protected I x := by
    unfold Protected Stable addr at *
    omega
  obtain ⟨ρ,hReplay,hSpan⟩:=HF
  calc
    ω x=ξ x := HC.1 x hx4
    _=ρ x := hSpan.2.2.2 x (Or.inl hx8)
    _=ν x := hReplay.1 x hprotect
    _=μ x := TernaryPrefixSeedHeader.prepared_kept_regions HP x hx13 hxhost (Or.inl hx3)


open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSeedData TernaryArenaPrefixInputs TernaryNativeCompleteFrontend
open TernaryArenaSelectedBudgets TernaryArenaAllocation TernaryArenaPhase
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

/-- Full concrete phase output preserves the templates and stored constants;
all frames are derived from the actual phase's component receipts. -/
theorem output {lim : Limits} {depth K H M b drift scale n U seedCount featureBound tagBound positionCap j U0 alpha beta budgetScale : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (Alloc : Allocation maps τ cap M b K H drift scale)
    (I : Input) (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free (depth+1))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hm : 0<m) (hr : j+1≤Nat.clog M (n^2)) (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hpos : positionCap≤n) (hseeds : seedCount≤(p^(LightTernaryDimensions.dim M b p K n U))^2)
    (hweight : I.weightCap≤TernaryArenaPrefixFootprints.weight H (4^fixedLength m) U)
    (htag : tagBound≤2*(4^fixedLength m)+1) (hweightLower : tagBound^2≤I.weightCap)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) (hfamily : 1<F)
    (hlocal : ∀right,0<(localRecords maps cap right).length)
    (htime : TernaryArenaCountReady.queryTime (m:=m) (r:=j+1) I (valueCap (r:=j+1) maps cap I)≤I.queryTime)
    (h : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O initial)
    (HM : TernaryArenaPrefixState.Memory I A (fun i t=>L i t.val) (fun i t=>R i t.val)
      (fun i t=>O i t.val) j s catalog initial μ)
    (hTemplate : Seg μ (addr I.free I.capacity 0) (TernaryArenaHeaderAgreement.templateValues I p m F))
    (hSeed : Seg μ (addr I.free I.capacity 3)
      (LightTernaryPrefixFinish.header (config p j I A 0) seedCount (p^j) (p^j) (alpha^j)
        (9^j*n^2) (9^j*n^2) (U0*(beta*budgetScale)^j) (addr I.free I.capacity 8)))
    (hPrepare : TernaryArenaPrefixPrepare.envelope
      (TernaryArenaPrefixPrepare.inputs p m F j A.J n U0 alpha beta budgetScale I Q)≤I.capacity)
    (hτ : 0<τ) (hnonempty : 1≤(TernaryGoodOutputCatalog.raws maps τ).length)
    (hSelector : (LightTernaryRowSelector.word seedCount
      (TernaryArenaPrefixFootprints.numbers maps τ cap M b K H drift scale n U (j+1)).candidateScore
      (p^(j+1)) (p^(j+1)) (alpha^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (U0*(beta*budgetScale)^(j+1)):ℤ)≤lim.word)
    (hGood : ∃i<seedCount,LightTernaryRowSelector.Good
      (family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).flag
      (family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).scoreB
      (family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).scoreC
      ((family maps τ cap tagBound Q I A j featureBound ℓ seeds L R O s catalog).scoreP K)
      (p^(j+1)) (p^(j+1)) (alpha^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2) (U0*(beta*budgetScale)^(j+1)) i)
    (ω : ℕ→ℤ) (hω : (TernaryArenaPhase.phase (depth:=depth) (K:=K) (H:=H) (M:=M) (b:=b) (drift:=drift)
      (scale:=scale) (n:=n) (U:=U) (seedCount:=seedCount) (featureBound:=featureBound)
      (tagBound:=tagBound) (positionCap:=positionCap) (j:=j) (U0:=U0) (alpha:=alpha)
      (beta:=beta) (budgetScale:=budgetScale) maps τ cap Q Alloc I A ℓ seeds L R O s catalog
      initial μ hok hcap hm hr hJ hnB hnC hO hpos hseeds hweight htag hweightLower hprefix
      hfamily hlocal htime h HM hTemplate hSeed hPrepare hτ hnonempty hSelector hGood).Output ω) :
    ∀x,Stable I x→ω x=μ x := by
  obtain ⟨ν,HP,ξ,HF,HC,_⟩:=hω
  simp only [TernaryArenaPhase.phase] at HF HC HP
  dsimp only [TernaryArenaControllerPlan.plan] at HF
  change TernaryArenaControllerPlan.Final (p:=p) (r:=j+1) I _ K (4^fixedLength m) F _
    (addr I.free I.capacity 8) (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) ν ξ at HF
  change LightTernaryPrefixFinish.Committed (config p (j+1) I A 0) (p^j*p)
    (addr I.free I.capacity 8) ξ ω at HC
  have h106 : 106≤I.capacity := by
    have hh:=capacity_pos Alloc.D Alloc.E (n+U)
    rw [←hcap] at hh
    omega
  exact receipts Q h106 HP HF HC

/-- The preserved low bands retain the exact host template segment. -/
theorem template {I : Input} {μ ω : ℕ→ℤ} {xs : List ℤ}
    (hframe : ∀x,Stable I x→ω x=μ x) (hlen : xs.length≤I.capacity)
    (hseg : Seg μ (addr I.free I.capacity 0) xs) :
    Seg ω (addr I.free I.capacity 0) xs := by
  intro i hi
  have hx : addr I.free I.capacity 0+i<addr I.free I.capacity 1 := by
    unfold addr
    omega
  rw [hframe _ (Or.inl hx)]
  exact hseg i hi

/-- The seed template and its adjoining three-word constant block survive
all actual phase writes. -/
theorem seed_region {I : Input} {μ ω : ℕ→ℤ} {xs : List ℤ} {offset : ℕ}
    (hframe : ∀x,Stable I x→ω x=μ x) (hlen : offset+xs.length≤I.capacity)
    (hseg : Seg μ (addr I.free I.capacity 2+offset) xs) :
    Seg ω (addr I.free I.capacity 2+offset) xs := by
  intro i hi
  have hx : addr I.free I.capacity 2≤addr I.free I.capacity 2+offset+i ∧
      addr I.free I.capacity 2+offset+i<addr I.free I.capacity 3 := by
    unfold addr
    omega
  rw [hframe _ (Or.inr hx)]
  exact hseg i hi

/-- The original input-length sentinel fits the canonical 2N-bit mask.
This uses the true input length, even when deduplication shrinks the arrays. -/
theorem input_lt_mask {n M r L : ℕ} (hn : 1<n) (hsize : n^2≤M^r) (hM : M≤4^L) :
    n<2^(2*(r*L)) := by
  calc
    n<n^2 := by nlinarith
    _≤M^r := hsize
    _≤(4^L)^r := Nat.pow_le_pow_left hM r
    _=2^(2*(r*L)) := by
      rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_mul]
      congr 1
      ring

end ThreeSum.TernaryArenaPhaseFrames

