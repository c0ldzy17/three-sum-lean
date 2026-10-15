import Submission.ThreeSum.TernaryArenaSeedScoreReady
import Submission.ThreeSum.TernaryArenaPostMemory
import Submission.ThreeSum.LightTernaryControllerFull
import Submission.ThreeSum.TernaryArenaPrefixCommit
import Submission.ThreeSum.TernaryArenaSeedCandidate

noncomputable section
namespace ThreeSum.TernaryArenaFinalMetadata
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaSeedCandidate
open LightTernarySeedScoreFactory LightTernaryControllerFactory TernaryArenaPostMemory
open TernaryCoverGoodMaps TernaryLocalParameters
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000
variable {p m F r : ℕ} [Fact p.Prime]

theorem keep_bank {I : Input} {A : Inputs} {seed K : ℕ}
    {D : Candidate (config p r I A seed)} {μ ν : ℕ→ℤ}
    (H : D.Done K μ ν) (hs : seed<I.capacity) (hcap : 106≤I.capacity)
    {x : ℕ} (hlo : addr I.free I.capacity 13≤x) (hhi : x<addr I.free I.capacity 16) :
    ν x=μ x := by
  obtain ⟨ξ,hkeep,rfl⟩ := H
  have hne (slot : ℕ) (hslot : slot≤12) : x≠addr I.free I.capacity slot+seed := by
    unfold addr at *
    nlinarith
  simp only [config] at hkeep ⊢
  rw [Function.update_of_ne (hne 12 (by decide)),Function.update_of_ne (hne 11 (by decide)),
    Function.update_of_ne (hne 10 (by decide)),Function.update_of_ne (hne 9 (by decide))]
  apply hkeep x hhi
  change x≠addr I.free I.capacity 1+104
  unfold addr at *
  omega

/-- The real replay output, together with preserved literal bank cells,
supplies all final metadata. No wanted-list representation is assumed. -/
theorem from_full_done (maps : Fin F→Weight m p) (τ cap K : ℕ)
    (I : Input) (A : Inputs) (seed : ℕ) (D : Candidate (config p r I A seed))
    (μ ν : ℕ→ℤ)
    (H : D.FullDone K (4^fixedLength m) F (TernaryGoodOutputCatalog.raws maps τ)
      (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) μ ν)
    (hs : seed<I.capacity) (hcap : 106≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hbankEnd : I.prefixFree+nb m r≤addr I.free I.capacity 16)
    (hpowerEnd : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c=>(c : ℤ))))
    (hpowers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)) :
    Metadata (r := r) maps τ (sourceInput I A seed D.data) ν := by
  refine ⟨?_,?_,?_⟩
  · change Seg ν I.prefixFree ((bankCodes m r).map (fun c=>(c : ℤ)))
    intro i hi
    have hii : i<nb m r := by simpa [nb] using hi
    rw [keep_bank H.1 hs hcap (by rw [←hprefix]; omega) (by omega)]
    exact hcodes i hi
  · change LightSubsetAddress.Powers ν (I.prefixFree+4^(N m r)) (2*N m r)
    intro i hi
    rw [keep_bank H.1 hs hcap (by rw [←hprefix]; exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) (by omega)]
    exact hpowers i hi
  · have hw := H.2.wanted
    change Seg ν (addr I.free I.capacity 19) _ at hw ⊢
    dsimp only [TernaryArenaSourceSetup.entries,sourceInput]
    rw [TernaryWantedBatchIndex.cells_entries_eq_rows]
    exact hw

theorem compact {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {μ : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ) (nB nC : ℕ) (fB fC : ℕ→ℕ) :
    Metadata (r := r) maps τ (TernaryArenaPairRestriction.restrict I nB nC fB fC) μ := by
  exact ⟨M.codes,M.powers,M.wanted⟩

/-- The real span construction writes only the eighth arena window. -/
theorem after_span {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {len : ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (H : SameOutside μ ν (addr I.free I.capacity 8) len) (hlen : len≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) :
    Metadata (r := r) maps τ I ν := by
  have high (x : ℕ) (hx : addr I.free I.capacity 9≤x) : ν x=μ x := by
    apply H x (Or.inr ?_)
    unfold addr at *
    omega
  have hb : addr I.free I.capacity 9≤I.prefixFree := by rw [hprefix];unfold addr;omega
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [high _ (by omega)]
    exact M.codes i hi
  · intro i hi
    rw [high _ (hb.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))]
    exact M.powers i hi
  · intro i hi
    rw [high _ (by unfold addr;omega)]
    exact M.wanted i hi

theorem host_after_span {I : Input} {len : ℕ} {μ ν : ℕ→ℤ}
    (H : SameOutside μ ν (addr I.free I.capacity 8) len)
    (hcap : 106≤I.capacity) (args : List ℤ) (hlen : args.length=106)
    (hhost : Seg μ (addr I.free I.capacity 1) args) :
    Seg ν (addr I.free I.capacity 1) args := by
  intro i hi
  have hii : i<106 := by simpa only [hlen] using hi
  rw [H _ (Or.inl (by unfold addr;omega))]
  exact hhost i hi

theorem after_commit {maps : Fin F→Weight m p} {τ : ℕ} {I : Input} {A : Inputs}
    {rows newSpan : ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (H : LightTernaryPrefixFinish.Committed (config p r I A 0) rows newSpan μ ν)
    (hO : I.requesterCount≤I.capacity) (hspan : rows*A.J≤I.capacity)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) :
    Metadata (r := r) maps τ I ν := by
  have high (x : ℕ) (hx : addr I.free I.capacity 8≤x) : ν x=μ x := by
    apply TernaryArenaPrefixCommit.outside H x
    · change x<addr I.free I.capacity 4 ∨ addr I.free I.capacity 6+I.requesterCount≤x
      right
      have hh := before (free := I.free) (i := 6) (j := 8) (by decide) hO
      omega
    · change x<addr I.free I.capacity 7 ∨ addr I.free I.capacity 7+rows*A.J≤x
      right
      have hh := before (free := I.free) (i := 7) (j := 8) (by decide) hspan
      omega
  have hbase : addr I.free I.capacity 8≤I.prefixFree := by rw [hprefix]; unfold addr; omega
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [high _ (by omega)]
    exact M.codes i hi
  · intro i hi
    rw [high _ (hbase.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))]
    exact M.powers i hi
  · intro i hi
    rw [high _ (by unfold addr; omega)]
    exact M.wanted i hi

theorem keep_low {I : Input} {A : Inputs} {seed K : ℕ}
    {D : Candidate (config p r I A seed)} {μ ν : ℕ→ℤ}
    (H : D.Done K μ ν) {x : ℕ} (hx : x<addr I.free I.capacity 9)
    (hne : x≠addr I.free I.capacity 1+104) : ν x=μ x := by
  obtain ⟨ξ,hkeep,rfl⟩ := H
  have hother (slot : ℕ) (hslot : 9≤slot) : x≠addr I.free I.capacity slot+seed := by
    unfold addr at *
    nlinarith
  simp only [config]
  rw [Function.update_of_ne (hother 12 (by decide)),Function.update_of_ne (hother 11 (by decide)),
    Function.update_of_ne (hother 10 (by decide)),Function.update_of_ne (hother 9 (by decide))]
  apply hkeep x
  · change x<addr I.free I.capacity 16
    unfold addr at *
    omega
  · exact hne

/-- The replay's literal header104 store completes the106 live host words.
All other words are preserved by the actual candidate program. -/
theorem host_from_full_done (maps : Fin F→Weight m p) (τ cap K : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed : ℕ)
    (D : Candidate (config p r I A seed)) (μ ν : ℕ→ℤ)
    (H : D.FullDone K (4^fixedLength m) F (TernaryGoodOutputCatalog.raws maps τ)
      (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) μ ν)
    (hcap : 106≤I.capacity)
    (hheader : ∀i<106,i≠104→μ (addr I.free I.capacity 1+i)=
      (setup (r := r) maps τ cap Q (sourceInput I A seed D.data)).argv.getD i 0) :
    Seg ν (addr I.free I.capacity 1)
      (setup (r := r) maps τ cap Q (sourceInput I A seed D.data)).argv := by
  intro i hi
  have hii : i<106 := hi
  by_cases he : i=104
  · subst i
    change ν (addr I.free I.capacity 1+104)=
      ((setup (r := r) maps τ cap Q (sourceInput I A seed D.data)).front.count : ℤ)
    rw [TernaryArenaSeedScoreReady.count_eq maps τ cap Q I A seed D.data]
    exact H.2.count
  · rw [keep_low H.1 (by unfold addr; omega) (by omega)]
    exact (hheader i hii he).trans (List.getD_eq_getElem _ _ hi)

theorem host_after_commit {I : Input} {A : Inputs} {rows newSpan : ℕ} {μ ν : ℕ→ℤ}
    (H : LightTernaryPrefixFinish.Committed (config p r I A 0) rows newSpan μ ν)
    (hcap : 106≤I.capacity) (args : List ℤ) (hlen : args.length=106)
    (hhost : Seg μ (addr I.free I.capacity 1) args) :
    Seg ν (addr I.free I.capacity 1) args := by
  intro i hi
  have hii : i<106 := by simpa only [hlen] using hi
  rw [TernaryArenaPrefixCommit.outside H _ (Or.inl ?_) (Or.inl ?_)]
  · exact hhost i hi
  · change addr I.free I.capacity 1+i<addr I.free I.capacity 4
    unfold addr
    omega
  · change addr I.free I.capacity 1+i<addr I.free I.capacity 7
    unfold addr
    omega

end ThreeSum.TernaryArenaFinalMetadata
