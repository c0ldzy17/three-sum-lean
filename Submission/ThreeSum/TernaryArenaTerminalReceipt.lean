import Submission.ThreeSum.TernaryArenaPhaseBudget
import Submission.ThreeSum.TernaryArenaFinalMetadata
import Submission.ThreeSum.TernaryArenaFinalSolver
import Submission.ThreeSum.TernaryArenaLoopState
import Submission.ThreeSum.TernaryArenaPreparedMemory

noncomputable section
namespace ThreeSum.TernaryArenaTerminalReceipt
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open TernaryArenaSeedData TernaryArenaSelectedBudgets TernaryArenaBudgetExistence TernaryArenaFamilyBudget
open TernaryArenaSelectedSigned TernaryArenaSelectedTerminal TernaryCoverGoodMaps TernaryLocalParameters
open LightTernarySeedScoreFactory LightTernaryControllerFactory
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 7000000
variable {p m F N : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

/-- The actual selected replay's append arrays, including requester/carry
keys and provenance, are the exact next selected original-prefix input. -/
theorem source_input_run (maps : Fin F→Weight m p) (τ cap U V scoreBound tag : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (j b K n U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (L R O : ℕ→ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ)
    (hL : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+L i t.val)
    (hR : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+R i t.val)
    (hO : ∀i (t : Fin (A.J+2)),0≤(p:ℤ)+O i t.val) :
    let s := run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j
    let f := TernaryArenaPhase.family maps τ cap tag Q I A j b ℓ (seedAt e) L R O s catalog
    let i := f.pick K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2) (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1))-1
    sourceInput I A i (f.candidate i).data=
      TernaryArenaSelectedTerminal.input I A
        (run maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs (j+1)) L R O (j+1) := by
  intro s f i
  have hi : i=chosen maps τ cap U V scoreBound Q I A b K n U0 e ℓ L R O catalogs j s := by
    dsimp only [i]
    rw [TernaryArenaPhaseBudget.threshold]
    exact TernaryArenaPrefixState.chosen_eq_core maps τ cap U V scoreBound tag Q I A b K n U0 j e ℓ s L R O catalog catalogs
  change sourceInput I A i (data I A j b i ℓ (seedAt e i) s.row
    (fun i t => L i t.val) (fun i t => R i t.val) (fun i t => O i t.val) s.rows catalog)=_
  rw [sourceInput_eq I A j b i ℓ (seedAt e i) s.row _ _ _ s.rows catalog hL hR hO,hi]
  rfl

/-- Exact final-solver semantic input, with every actual requester/carry
occurrence retained. This is an equality of functions, not bounded samples. -/
theorem source_input_signed (maps : Fin F→Weight m p) (τ cap U V scoreBound tag : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (j radix K n nA U0 : ℕ)
    (e : (E×E)≃Fin N) (ℓ : E→ₗ[ZMod p] ZMod p) (X B C : ℕ→ℤ)
    (catalogs : ℕ→ℕ→ℕ→ℕ) (catalog : ℕ→ℕ→ℕ)
    (hb : 1<radix) (hp : radix≤p) (hbase : TernaryArenaSelectedSigned.base I A.J nA=I) :
    let L := left U radix A.J B
    let R := right U radix A.J C
    let O := requester U radix A.J X
    let s := run maps τ cap U V scoreBound Q I A radix K n U0 e ℓ L R O catalogs j
    let f := TernaryArenaPhase.family maps τ cap tag Q I A j radix ℓ (seedAt e) L R O s catalog
    let i := f.pick K N (p^(j+1)) (p^(j+1)) ((p^(2*K))^(j+1))
      (9^(j+1)*n^2) (9^(j+1)*n^2) (U0*((9*pairFactor m F K)*(2^((fixedPi m 2)*K)))^(j+1))-1
    let s' := run maps τ cap U V scoreBound Q I A radix K n U0 e ℓ L R O catalogs (j+1)
    sourceInput I A i (f.candidate i).data=
      TernaryArenaNativeComplete.input I U radix nA (selectedHash A s' (j+1)) X B C := by
  intro L R O s f i s'
  have hh := source_input_run maps τ cap U V scoreBound tag Q I A j radix K n U0 e ℓ L R O catalogs catalog
    (fun i t => signed_nonnegative hp (left_bound hb B i t.val))
    (fun i t => signed_nonnegative hp (right_bound hb C i t.val))
    (fun i t => signed_nonnegative hp (requester_bound hb X i t.val))
  have hs := TernaryArenaSelectedSigned.input_eq I A s' (j+1) U radix nA X B C
  rw [hbase] at hs
  exact hh.trans hs

structure QueryReceipt (maps : Fin F→Weight m p) (τ cap r : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ) : Prop where
  metadata : TernaryArenaPostMemory.Metadata (r := r) maps τ I μ
  host : Seg μ (addr I.free I.capacity 1) (setup (r := r) maps τ cap Q I).argv

/-- Plan.Final's retained replay reads suffice for all actual metadata and
106 host words; the execution proof itself need not be retained in memory. -/
theorem queries_of_final (maps : Fin F→Weight m p) (τ cap K j : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs)
    (f : Family (config p (j+1) I A 0)) (ordinal : ℕ) (μ ζ ν : ℕ→ℤ)
    (H : TernaryArenaControllerPlan.Final I f K (4^fixedLength m) F ordinal (addr I.free I.capacity 8)
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ ζ)
    (HC : LightTernaryPrefixFinish.Committed (config p (j+1) I A 0) (p^(j+1)) (addr I.free I.capacity 8) ζ ν)
    (hcap : 106≤I.capacity) (hO : I.requesterCount≤I.capacity)
    (hspan : A.J*(p^j)*p≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hbank : I.prefixFree+nb m (j+1)≤addr I.free I.capacity 16)
    (hpower : I.prefixFree+4^(TernaryArenaSourceSetup.N m (j+1))+(2*TernaryArenaSourceSetup.N m (j+1)+1)≤addr I.free I.capacity 16)
    (hcodes : Seg μ I.prefixFree ((bankCodes m (j+1)).map (fun (c : ℕ)=>(c:ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(TernaryArenaSourceSetup.N m (j+1))) (2*TernaryArenaSourceSetup.N m (j+1)))
    (ret : ℤ) (hheader : Seg μ (addr I.free I.capacity 1)
      (TernaryArenaHeaderAgreement.emittedHeader I p m F j Q ret)) :
    QueryReceipt maps τ cap (j+1) Q (sourceInput I A ordinal (f.candidate ordinal).data) ν := by
  rcases H with ⟨ξ,⟨hkeep,houtputs⟩,hspanDone⟩
  let D := (f.candidate ordinal).data
  let I' := sourceInput I A ordinal D
  have hMeta : TernaryArenaPostMemory.Metadata (r := j+1) maps τ I' ξ := by
    refine ⟨?_,?_,?_⟩
    · have hc : Seg ξ I.prefixFree ((bankCodes m (j+1)).map (fun (c : ℕ)=>(c:ℤ))) := by
        intro i hi
        have hii : i<nb m (j+1) := by simpa [nb] using hi
        rw [hkeep _ (TernaryArenaScoreScan.protected_bank (by rw [←hprefix];omega) (by omega) hcap)]
        exact hcodes i hi
      have cast_map (l : List ℕ) : (l : List ℤ).map (fun c => c)=l.map (fun (c : ℕ)=>(c:ℤ)) := by
        induction l with
        | nil => rfl
        | cons x xs ih => simp_all
      change Seg ξ I.prefixFree ((bankCodes m (j+1) : List ℤ).map (fun c=>c))
      rw [cast_map]
      exact hc
    · change LightSubsetAddress.Powers ξ (I.prefixFree+4^(TernaryArenaSourceSetup.N m (j+1))) (2*TernaryArenaSourceSetup.N m (j+1))
      intro i hi
      rw [hkeep _ (TernaryArenaScoreScan.protected_bank (by rw [←hprefix];exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) (by omega) hcap)]
      exact hpowers i hi
    · have hh := houtputs.wanted
      change Seg ξ (addr I.free I.capacity 19) _ at hh ⊢
      dsimp only [TernaryArenaSourceSetup.entries,I',sourceInput]
      rw [TernaryWantedBatchIndex.cells_entries_eq_rows]
      exact hh
  have host : Seg ξ (addr I.free I.capacity 1) (setup (r := j+1) maps τ cap Q I').argv := by
    have head := TernaryArenaTensorGuardAllocation.header_read maps τ cap Q I A ordinal D μ ret (by omega) hheader
    intro i hi
    have hi106 : i<106 := hi
    by_cases he : i=104
    · subst i
      change ξ (addr I.free I.capacity 1+104)=((setup (r := j+1) maps τ cap Q I').front.count:ℤ)
      rw [TernaryArenaSeedScoreReady.count_eq maps τ cap Q I A ordinal D]
      exact houtputs.count
    · rw [hkeep _ (TernaryArenaScoreScan.protected_low (by unfold addr;omega) (by omega))]
      exact (head i hi106 he).trans (List.getD_eq_getElem _ _ hi)
  have hs : SameOutside ξ ζ (addr I.free I.capacity 8) (A.J*(p^j)*p) := by
    simpa only [SpanDone,withSeed,config,Nat.add_sub_cancel] using hspanDone.2.2.2
  have metaSpan := TernaryArenaFinalMetadata.after_span hMeta hs hspan hprefix
  have hostSpan := TernaryArenaFinalMetadata.host_after_span hs hcap _ rfl host
  have hc : LightTernaryPrefixFinish.Committed (config p (j+1) I' A 0) (p^(j+1))
      (addr I'.free I'.capacity 8) ζ ν := HC
  refine ⟨TernaryArenaFinalMetadata.after_commit metaSpan hc hO ?_ hprefix,
    TernaryArenaFinalMetadata.host_after_commit hc hcap _ rfl hostSpan⟩
  simpa only [I',sourceInput,pow_succ,mul_comm,mul_left_comm,mul_assoc] using hspan

variable {K : ℕ}

/-- The last actual loop record supplies the complete bank, wanted rows and
live host header for the exact next selected original-prefix state. -/
theorem queries_of_record (S : TernaryArenaLoop.Setup p m F K N E) (j : ℕ) (ω : ℕ→ℤ)
    (T : TernaryArenaLoop.LastRecord S j ω)
    (hcap : 106≤S.input.capacity) (hB : S.input.nB≤S.input.capacity)
    (hC : S.input.nC≤S.input.capacity) (hO : S.input.requesterCount≤S.input.capacity)
    (hspan : S.arrays.J*(p^j)*p≤S.input.capacity)
    (hprefix : S.input.prefixFree=addr S.input.free S.input.capacity 13)
    (hbank : S.input.prefixFree+nb m (j+1)≤addr S.input.free S.input.capacity 16)
    (hpower : S.input.prefixFree+4^(TernaryArenaSourceSetup.N m (j+1))+
      (2*TernaryArenaSourceSetup.N m (j+1)+1)≤addr S.input.free S.input.capacity 16)
    (hL : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.L i t.val)
    (hR : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.R i t.val)
    (hOraw : ∀i (t : Fin (S.arrays.J+2)),0≤(p:ℤ)+S.O i t.val) :
    QueryReceipt S.maps S.threshold S.cap (j+1) S.Q
      (TernaryArenaSelectedTerminal.input S.input S.arrays (S.state (j+1)) S.L S.R S.O (j+1)) ω := by
  have hp : 1≤p := (Fact.out : p.Prime).pos
  have hold : S.arrays.J*p^j≤S.input.capacity :=
    (Nat.le_mul_of_pos_right _ hp).trans hspan
  obtain ⟨_,hcodes,hpowers,ret,hheader⟩ := TernaryArenaPreparedMemory.prepared S.input S.arrays j S.n S.U0
    S.alpha S.beta S.budgetScale S.Q _ _ _ (S.state j) T.catalog S.initial T.before T.preparedMemory
    T.prepared hprefix hcap hB hC hO hold T.oldTemplate T.oldMemory
  have hqueries := queries_of_final S.maps S.threshold S.cap K j S.Q S.input S.arrays
    (S.family j T.catalog) (S.chosen j T.catalog) T.preparedMemory T.finalMemory ω T.final T.committed
    hcap hO hspan hprefix hbank hpower hcodes hpowers ret hheader
  have heq := source_input_run S.maps S.threshold S.cap S.valueTag S.V S.scoreBound S.tagBound
    S.Q S.input S.arrays j S.featureBound K S.n S.U0 S.enumeration S.ell S.L S.R S.O
    S.catalogs T.catalog hL hR hOraw
  exact heq ▸ hqueries

/-- Committed packed original endpoint keys are exactly the selected signed
feature hashes. Their equality is proved for every stored original index. -/
theorem signed_keys_of_memory (I : Input) (A : Inputs) (s : State (p := p) A)
    (r U radix : ℕ) (X B C : ℕ→ℤ) (catalog : ℕ→ℕ→ℕ) (initial μ : ℕ→ℤ)
    (H : TernaryArenaPrefixState.Memory I A
      (fun i t=>left U radix A.J B i t.val) (fun i t=>right U radix A.J C i t.val)
      (fun i t=>requester U radix A.J X i t.val) r s catalog initial μ) :
    Reads μ (addr I.free I.capacity 4) I.nB
      (fun i=>TernaryExtensionEncoding.coefficientCode
        (TernaryNativeRequesterCoverage.sourceLeft (selectedHash A s r) U radix (B i))) ∧
    Reads μ (addr I.free I.capacity 5) I.nC
      (fun i=>TernaryExtensionEncoding.coefficientCode
        (TernaryNativeRequesterCoverage.sourceRight (selectedHash A s r) U radix (C i))) := by
  constructor
  · intro i hi
    simp only [TernaryNativeRequesterCoverage.sourceLeft]
    rw [selectedHash_raw]
    exact H.B i hi
  · intro i hi
    simp only [TernaryNativeRequesterCoverage.sourceRight]
    rw [selectedHash_raw]
    exact H.Cvalues i hi

end ThreeSum.TernaryArenaTerminalReceipt
