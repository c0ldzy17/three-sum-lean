import Submission.ThreeSum.TernaryArenaControllerPlan
import Submission.ThreeSum.TernaryArenaPrefixCommit
import Submission.ThreeSum.LightTernaryPrefixStep
import Submission.ThreeSum.TernaryArenaSelectedBudgets
import Submission.ThreeSum.LightTernaryPrefixInit
import Submission.ThreeSum.TernaryPrefixSeedHeader

noncomputable section
namespace ThreeSum.TernaryArenaPrefixState
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open TernaryArenaSeedData TernaryArenaSelectedBudgets TernaryArenaBudgetExistence TernaryArenaFamilyBudget
open LightTernarySeedScoreFactory LightTernaryControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

/-- Exact retained physical state. The immutable prefix contains all original
matrices, extension-field menu coefficients and requester provenance. -/
structure Memory (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (j : ℕ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ) : Prop where
  immutable : Kept initial μ I.free
  B : Reads μ (addr I.free I.capacity 4) I.nB
    (fun i => TernaryExtensionEncoding.coefficientCode (hash s.row j L i))
  Cvalues : Reads μ (addr I.free I.capacity 5) I.nC
    (fun i => TernaryExtensionEncoding.coefficientCode (hash s.row j R i))
  Ovalues : Reads μ (addr I.free I.capacity 6) I.requesterCount
    (fun i => TernaryExtensionEncoding.coefficientCode (hash s.row j O i))
  represents : TernaryStoredSpan.Represents catalog (p^j)
    (s.rows.map (TernaryPhysicalDigitSpan.reversal A.J))
  bounded : ∀k<p^j,∀i<A.J,catalog k i<p
  read : ∀k<p^j,∀i<A.J,μ (addr I.free I.capacity 7+A.J*k+i)=(catalog k i:ℤ)

def extend (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (j : ℕ)
    (s : State (p := p) A) (seed : E×E) : State (p := p) A :=
  ⟨Function.update s.row j (TernaryOriginalRowMenu.row (A.J+2) ℓ seed),
    TernaryPhysicalDigitSpan.digitProjection A.J (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ seed)::s.rows⟩

def nextCatalog (A : Inputs) (ℓ : E→ₗ[ZMod p] ZMod p) (j : ℕ)
    (catalog : ℕ→ℕ→ℕ) (seed : E×E) : ℕ→ℕ→ℕ :=
  TernaryStoredSpan.next catalog (LightStoredSpan.rowValues
    (TernaryPhysicalDigitSpan.physicalDigits (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ seed))) p (p^j)

/-- Replay and span receipts followed by the actual key/span commit establish
the next retained physical state, with no read or semantic callback. -/
theorem transition (I : Input) (A : Inputs) (j b ordinal Rb Sb : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E) (s : State (p := p) A)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (catalog : ℕ→ℕ→ℕ)
    (raws : List ℤ) (words maps : List ℕ) (initial μ ξ ζ ν : ℕ→ℤ)
    (hmem : Memory I A L R O j s catalog initial μ)
    (hkeep : TernaryArenaScoreScan.KeepInputs I μ ξ)
    (houtputs : LightTernarySeedScoreFull.Outputs (config p (j+1) I A ordinal)
      (data I A j b ordinal ℓ seed s.row L R O s.rows catalog) Rb Sb raws words maps ξ)
    (hspan : SpanDone (config p (j+1) I A ordinal)
      (data I A j b ordinal ℓ seed s.row L R O s.rows catalog) (addr I.free I.capacity 8) ξ ζ)
    (hcommit : LightTernaryPrefixFinish.Committed (config p (j+1) I A ordinal)
      (p^(j+1)) (addr I.free I.capacity 8) ζ ν)
    (hcapacity : A.J*(p^j)*p≤I.capacity)
    (hL : ∀i t,0≤(p:ℤ)+L i t) (hR : ∀i t,0≤(p:ℤ)+R i t) (hO : ∀i t,0≤(p:ℤ)+O i t) :
    Memory I A L R O (j+1) (extend A ℓ j s seed) (nextCatalog A ℓ j catalog seed) initial ν := by
  have hcount : p*p^j=p^(j+1) := by rw [pow_succ'];
  have hspan' :
      (∀q<p^(j+1),∀i<A.J,ζ (addr I.free I.capacity 8+A.J*q+i)=
        (nextCatalog A ℓ j catalog seed q i:ℤ)) ∧
      TernaryStoredSpan.Represents (nextCatalog A ℓ j catalog seed) (p^(j+1))
        ((extend A ℓ j s seed).rows.map (TernaryPhysicalDigitSpan.reversal A.J)) ∧
      (∀q<p^(j+1),∀i<A.J,nextCatalog A ℓ j catalog seed q i<p) ∧
      SameOutside ξ ζ (addr I.free I.capacity 8) (A.J*(p^j)*p) := by
    set_option backward.isDefEq.respectTransparency false in
      simpa only [SpanDone,config,data,Nat.add_sub_cancel,hcount,nextCatalog,extend,List.map_cons,
        TernaryPhysicalDigitSpan.physicalDigits] using hspan
  have spanHigh (x : ℕ) (hx : addr I.free I.capacity 16≤x) : ζ x=ξ x := by
    apply hspan'.2.2.2
    right
    have hh := before (free := I.free) (C := I.capacity) (by decide : 8<16) hcapacity
    omega
  have spanLow (x : ℕ) (hx : x<I.free) : ζ x=ξ x := hspan'.2.2.2 x (Or.inl (by unfold addr;omega))
  refine ⟨?_,?_,?_,?_,hspan'.2.1,hspan'.2.2.1,?_⟩
  · intro x hx
    have hk : ν x=ζ x := TernaryArenaPrefixCommit.outside hcommit x
      (Or.inl (by change x<addr I.free I.capacity 4; unfold addr;omega))
      (Or.inl (by change x<addr I.free I.capacity 7; unfold addr;omega))
    rw [hk,spanLow x hx,hkeep x ?_]
    · exact hmem.immutable x hx
    · exact TernaryArenaScoreScan.protected_low (by unfold addr;omega) (by unfold addr;omega)
  · intro i hi
    calc
      ν (addr I.free I.capacity 4+i)=ζ (addr I.free I.capacity 16+i) := hcommit.2.1 i hi
      _=ξ (addr I.free I.capacity 16+i) := spanHigh _ (Nat.le_add_right _ _)
      _=(data I A j b ordinal ℓ seed s.row L R O s.rows catalog).newB i := houtputs.B i hi
      _=_ := by exact_mod_cast newB_eq I A j b ordinal ℓ seed s.row L R O s.rows catalog hL i
  · intro i hi
    calc
      ν (addr I.free I.capacity 5+i)=ζ (addr I.free I.capacity 17+i) := hcommit.2.2.1 i hi
      _=ξ (addr I.free I.capacity 17+i) := spanHigh _ (by unfold addr;omega)
      _=(data I A j b ordinal ℓ seed s.row L R O s.rows catalog).newC i := houtputs.Cvalues i hi
      _=_ := by exact_mod_cast newC_eq I A j b ordinal ℓ seed s.row L R O s.rows catalog hR i
  · intro i hi
    calc
      ν (addr I.free I.capacity 6+i)=ζ (addr I.free I.capacity 18+i) := hcommit.2.2.2.1 i hi
      _=ξ (addr I.free I.capacity 18+i) := spanHigh _ (by unfold addr;omega)
      _=(data I A j b ordinal ℓ seed s.row L R O s.rows catalog).newO i := houtputs.O i hi
      _=_ := by exact_mod_cast newO_eq I A j b ordinal ℓ seed s.row L R O s.rows catalog hO i
  · intro q hq i hi
    exact (hcommit.2.2.2.2.1 q hq i hi).trans (hspan'.1 q hq i hi)

theorem start (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ) (initial μ : ℕ→ℤ)
    (hkeep : Kept initial μ I.free)
    (hB : ∀i<I.nB,μ (addr I.free I.capacity 4+i)=0)
    (hC : ∀i<I.nC,μ (addr I.free I.capacity 5+i)=0)
    (hO : ∀i<I.requesterCount,μ (addr I.free I.capacity 6+i)=0)
    (hSpan : ∀i<A.J,μ (addr I.free I.capacity 7+i)=0) :
    Memory I A L R O 0 (TernaryArenaSelectedBudgets.initial (p := p) A) (fun _ _ => 0) initial μ := by
  refine ⟨hkeep,?_,?_,?_,?_,?_,?_⟩
  · intro i hi
    simpa [TernaryArenaSeedData.hash,TernaryExtensionEncoding.coefficientCode] using hB i hi
  · intro i hi
    simpa [TernaryArenaSeedData.hash,TernaryExtensionEncoding.coefficientCode] using hC i hi
  · intro i hi
    simpa [TernaryArenaSeedData.hash,TernaryExtensionEncoding.coefficientCode] using hO i hi
  · simpa [TernaryArenaSelectedBudgets.initial] using (TernaryStoredSpan.represents_zero (p := p) (J := A.J))
  · intro k hk i hi
    exact (Fact.out : p.Prime).pos
  · intro k hk i hi
    have : k=0 := by
      simp only [pow_zero] at hk
      omega
    subst k
    simpa using hSpan i hi

/-- Resource caps and stored catalog values do not enter the literal flag
or score expressions checked by the selector. -/
theorem chosen_eq_core (maps : Fin F→TernaryCoverGoodMaps.Weight m p) (τ cap U V scoreBound U' : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (b K n U0 j : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (s : State (p := p) A)
    (L R O : ℕ→ℕ→ℤ) (catalog : ℕ→ℕ→ℕ) (catalogs : ℕ→ℕ→ℕ→ℕ) :
    (TernaryArenaControllerCore.family maps τ cap U' Q I A
      (fun k => data I A j b k ℓ (TernaryArenaFamilyBudget.seedAt e k) s.row
        (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog) L R).pick
      K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
      (scale m j K*(9*pairFactor m F K)^(j+1)*U0)-1=
      chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j s := by
  unfold chosen budgetGood Family.pick
  congr 2

/-- The committed next row is exactly the deterministic selected-state run.
The actual catalog may use any physical representation of the old span. -/
theorem transition_run (maps : Fin F→TernaryCoverGoodMaps.Weight m p) (τ cap U V scoreBound : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (j b K n U0 Rb Sb : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (L R O : ℕ→ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ)
    (raws : List ℤ) (words localMaps : List ℕ) (initial μ ξ ζ ν : ℕ→ℤ)
    (hmem : Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) j
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j) catalog initial μ)
    (hkeep : TernaryArenaScoreScan.KeepInputs I μ ξ)
    (hL : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+L i t.val)
    (hR : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+R i t.val)
    (hO : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+O i t.val)
    (hcapacity : A.J*(p^j)*p≤I.capacity) :
    let s := run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j
    let ordinal := chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j s
    let seed := TernaryArenaFamilyBudget.seedAt e ordinal
    let D := data I A j b ordinal ℓ seed s.row (fun i t => L i t.val)
      (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog
    LightTernarySeedScoreFull.Outputs (config p (j+1) I A ordinal) D Rb Sb raws words localMaps ξ→
    SpanDone (config p (j+1) I A ordinal) D (addr I.free I.capacity 8) ξ ζ→
    LightTernaryPrefixFinish.Committed (config p (j+1) I A ordinal) (p^(j+1)) (addr I.free I.capacity 8) ζ ν→
    ∃catalog', Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) (j+1)
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs (j+1)) catalog' initial ν := by
  intro s ordinal seed D houtputs hspan hcommit
  refine ⟨nextCatalog A ℓ j catalog seed,?_⟩
  exact transition I A j b ordinal Rb Sb ℓ seed s _ _ _ catalog raws words localMaps initial μ ξ ζ ν
    hmem hkeep houtputs hspan hcommit hcapacity hL hR hO

theorem start_initialized (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (values : List ℤ) (initial μ : ℕ→ℤ)
    (H : LightTernaryPrefixInit.Initialized (config p 1 I A 0) (addr I.free I.capacity 3) values initial μ) :
    Memory I A L R O 0 (TernaryArenaSelectedBudgets.initial (p := p) A) (fun _ _ => 0) initial μ := by
  apply start I A L R O initial μ ?_ H.2.1 H.2.2.1 H.2.2.2.1 H.2.2.2.2.1
  intro x hx
  exact H.2.2.2.2.2 x (Or.inl (by unfold addr;omega))
    (Or.inl (by change x<addr I.free I.capacity 4;unfold addr;omega))
    (Or.inl (by change x<addr I.free I.capacity 7;unfold addr;omega))

/-- Actual preparation preserves every retained semantic field, while it
constructs the next prefix bank and updates its two control headers. -/
theorem prepared (I : Input) (A : Inputs) (L R O : ℕ→Fin (A.J+2)→ℤ)
    (j : ℕ) (s : State (p := p) A) (catalog : ℕ→ℕ→ℕ) (initial μ ν : ℕ→ℤ)
    (X : LightTernaryPrefixStep.Inputs) (H : LightTernaryPrefixStep.Prepared X μ ν)
    (hhost : X.liveHeader=addr I.free I.capacity 1)
    (hseed : X.seed=addr I.free I.capacity 3)
    (hprefix : X.prefixFree=addr I.free I.capacity 13)
    (hcap : 106≤I.capacity) (hB : I.nB≤I.capacity) (hC : I.nC≤I.capacity)
    (hO : I.requesterCount≤I.capacity) (hSpan : A.J*p^j≤I.capacity)
    (hmem : Memory I A L R O j s catalog initial μ) : Memory I A L R O j s catalog initial ν := by
  have hlow (x : ℕ) (hx : x<I.free) : ν x=μ x :=
    TernaryPrefixSeedHeader.prepared_kept_regions H x
      (by rw [hprefix];unfold addr;omega)
      (Or.inl (by rw [hhost];unfold addr;omega))
      (Or.inl (by rw [hseed];unfold addr;omega))
  have hregions (x : ℕ) (hx : addr I.free I.capacity 4≤x) (hy : x<addr I.free I.capacity 8) : ν x=μ x :=
    TernaryPrefixSeedHeader.prepared_kept_regions H x
      (by rw [hprefix];unfold addr at *;omega)
      (Or.inr (by rw [hhost];unfold addr at *;omega))
      (Or.inr (by rw [hseed];unfold addr at *;omega))
  have hkeys (slot count : ℕ) (hs : 4≤slot ∧ slot<7) (hc : count≤I.capacity) (i : ℕ) (hi : i<count) :
      ν (addr I.free I.capacity slot+i)=μ (addr I.free I.capacity slot+i) := by
    apply hregions
    · unfold addr
      have hh := Nat.mul_le_mul_right I.capacity hs.1
      omega
    · have hh := offset_lt (free := I.free) (C := I.capacity) (slot := slot) hi hc
      unfold addr at *
      have hm := Nat.mul_le_mul_right I.capacity (show slot+1≤8 by omega)
      omega
  refine ⟨?_,?_,?_,?_,hmem.represents,hmem.bounded,?_⟩
  · intro x hx
    exact (hlow x hx).trans (hmem.immutable x hx)
  · intro i hi
    exact (hkeys 4 I.nB (by omega) hB i hi).trans (hmem.B i hi)
  · intro i hi
    exact (hkeys 5 I.nC (by omega) hC i hi).trans (hmem.Cvalues i hi)
  · intro i hi
    exact (hkeys 6 I.requesterCount (by omega) hO i hi).trans (hmem.Ovalues i hi)
  · intro q hq i hi
    have hindex : A.J*q+i<A.J*p^j := by nlinarith
    have htop := offset_lt (free := I.free) (C := I.capacity) (slot := 7) hindex hSpan
    rw [←Nat.add_assoc] at htop
    exact (hregions _ (by unfold addr;omega) htop).trans (hmem.read q hq i hi)

/-- Root's concrete canonical Plan.Final receipt discharges the complete
selected-state memory transition after the actual commit. -/
theorem final_transition (maps : Fin F→TernaryCoverGoodMaps.Weight m p)
    (τ cap U V scoreBound U' : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (j b K n U0 Rb Sb : ℕ) (e : (E×E)≃Fin N)
    (ℓ : E→ₗ[ZMod p] ZMod p) (L R O : ℕ→ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ) (raws : List ℤ) (words localMaps : List ℕ)
    (initial μ ζ ν : ℕ→ℤ)
    (hmem : Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) j
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j) catalog initial μ)
    (hL : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+L i t.val)
    (hR : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+R i t.val)
    (hO : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+O i t.val)
    (hcapacity : A.J*(p^j)*p≤I.capacity) :
    let s := run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j
    let Ds := fun k => data I A j b k ℓ (seedAt e k) s.row
      (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog
    let f := TernaryArenaControllerCore.family maps τ cap U' Q I A Ds L R
    let ordinal := f.pick K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2) (scale m j K*(9*pairFactor m F K)^(j+1)*U0)-1
    TernaryArenaControllerPlan.Final I f K Rb Sb ordinal (addr I.free I.capacity 8)
      raws words localMaps μ ζ→
    LightTernaryPrefixFinish.Committed (config p (j+1) I A 0) (p^(j+1)) (addr I.free I.capacity 8) ζ ν→
    ∃catalog', Memory I A (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) (j+1)
      (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs (j+1)) catalog' initial ν := by
  intro s Ds f ordinal hfinal hcommit
  rcases hfinal with ⟨ξ,⟨hkeep,houtputs⟩,hspan⟩
  have hchosen : ordinal=chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j s :=
    chosen_eq_core maps τ cap U V scoreBound U' Q I A b K n U0 j e ℓ s L R O catalog catalogs
  have ho : LightTernarySeedScoreFull.Outputs (config p (j+1) I A ordinal) (Ds ordinal) Rb Sb raws words localMaps ξ := houtputs
  have hs : SpanDone (config p (j+1) I A ordinal) (Ds ordinal) (addr I.free I.capacity 8) ξ ζ := hspan
  unfold Ds at ho hs
  rw [hchosen] at ho hs
  exact transition_run maps τ cap U V scoreBound Q I A j b K n U0 Rb Sb e ℓ L R O catalogs catalog
    raws words localMaps initial μ ξ ζ ν hmem hkeep hL hR hO hcapacity ho hs hcommit

/-- The invariant may refer back to the original preprocessing memory,
through actual arena and control initialization that preserves this prefix. -/
theorem Memory.rebase {I : Input} {A : Inputs} {L R O : ℕ→Fin (A.J+2)→ℤ}
    {j : ℕ} {s : State (p := p) A} {catalog : ℕ→ℕ→ℕ} {initial initial' μ : ℕ→ℤ}
    (H : Memory I A L R O j s catalog initial μ) (hk : Kept initial' initial I.free) :
    Memory I A L R O j s catalog initial' μ :=
  {H with immutable:=fun x hx => (H.immutable x hx).trans (hk x hx)}

end ThreeSum.TernaryArenaPrefixState
