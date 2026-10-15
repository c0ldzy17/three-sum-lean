import Submission.ThreeSum.TernaryArenaPostSelection
import Submission.ThreeSum.TernaryArenaCleanupLayout

noncomputable section
namespace ThreeSum.TernaryArenaPostMemory
open Light TernaryArenaLayout TernaryArenaSourceSetup TernaryArenaPostSelection
open LightOriginalSurvivors LightOriginalSurvivorPair TernaryExtensionEncoding
open TernaryCoverGoodMaps
set_option maxHeartbeats 4000000
variable {p m F r J : ℕ} [Fact p.Prime]

/-- Literal bank and query arrays retained from the executed selected prefix. -/
structure Metadata (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) (μ : ℕ→ℤ) : Prop where
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
  wanted : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I))

theorem Metadata.after_cleanup {maps : Fin F→Weight m p} {τ : ℕ} {I : Input}
    {aBase nA bBase nB cBase nC q L : ℕ} {keysB keysC : ℕ→ℕ} {μ ν : ℕ→ℤ}
    (M : Metadata (r := r) maps τ I μ)
    (hB : nB≤I.capacity) (hC : nC≤I.capacity)
    (hcounts : nB+3*nC+1≤I.capacity) (hCc : nC+1≤I.capacity)
    (hlo : addr I.free I.capacity 11≤I.prefixFree)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 16)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (h : (TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase nB cBase nC q L).Unchanged keysB keysC μ ν) :
    Metadata (r := r) maps τ I ν := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [TernaryArenaCleanupLayout.unchanged_bank hB hC h
      (by omega) (by simpa only [List.length_map,nb] using (show I.prefixFree+i<addr I.free I.capacity 16 by
        have hi' : i<nb m r := by simpa [nb] using hi
        omega))]
    exact M.codes i hi
  · intro i hi
    rw [TernaryArenaCleanupLayout.unchanged_bank hB hC h (hlo.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _))) (by omega : I.prefixFree+4^(N m r)+i<addr I.free I.capacity 16)]
    exact M.powers i hi
  · intro i hi
    rw [TernaryArenaCleanupLayout.unchanged_high hcounts hCc h
      (show addr I.free I.capacity 18≤addr I.free I.capacity 19+i by unfold addr; omega)]
    exact M.wanted i hi

theorem Metadata.after_preparation {maps : Fin F→Weight m p} {τ : ℕ} {I : Input}
    {L q : ℕ} {μ ν : ℕ→ℤ} (M : Metadata (r := r) maps τ I μ)
    (hL : L+1≤I.capacity) (hq : q≤I.capacity)
    (hlo : addr I.free I.capacity 9≤I.prefixFree)
    (h : ∀x, LightTernaryFinalPreparation.Unwritten (addr I.free I.capacity 6) L
      (addr I.free I.capacity 7) (addr I.free I.capacity 8) q x→ν x=μ x) :
    Metadata (r := r) maps τ I ν := by
  refine ⟨?_,?_,?_⟩
  · intro i hi
    rw [TernaryArenaCleanupLayout.preparation_bank hL hq h (by omega)]
    exact M.codes i hi
  · intro i hi
    rw [TernaryArenaCleanupLayout.preparation_bank hL hq h (hlo.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))]
    exact M.powers i hi
  · intro i hi
    rw [TernaryArenaCleanupLayout.preparation_bank hL hq h
      (show addr I.free I.capacity 9≤addr I.free I.capacity 19+i by unfold addr; omega)]
    exact M.wanted i hi

theorem input_bound (v : Fin r→ZMod p) :
    |(coefficientCode v : ℤ)|≤(p*(p+1)^r : ℕ) := by
  rw [abs_of_nonneg (Int.natCast_nonneg _)]
  apply Int.ofNat_le.mpr
  have hp : 1≤p := (Fact.out : p.Prime).one_lt.le
  exact (coefficientCode_lt v).le.trans
    ((Nat.pow_le_pow_left (by omega : p≤p+1) r).trans (Nat.le_mul_of_pos_left _ (by omega)))

theorem reads {maps : Fin F→Weight m p} {τ cap : ℕ}
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (U radix nA aBase bBase cBase q L : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ ν : ℕ→ℤ)
    (M : Metadata (r := r) maps τ (selectedInput I U radix nA H A B C keysB keysC) μ)
    (hcounts : I.nB+3*I.nC+1≤I.capacity) (hCc : I.nC+1≤I.capacity)
    (hlo : addr I.free I.capacity 11≤I.prefixFree)
    (hbank : I.prefixFree+nb m r≤addr I.free I.capacity 16)
    (hpowers : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16)
    (h : (TernaryArenaCleanupLayout.layout I.free I.capacity aBase nA bBase I.nB cBase I.nC q L).Unchanged keysB keysC μ ν)
    (hOutB : Output ν keysB B I.nB (addr I.free I.capacity 9) (addr I.free I.capacity 10)
      (addr I.free I.capacity 16) (addr I.free I.capacity 16+I.nB))
    (hOutC : Output ν keysC C I.nC (addr I.free I.capacity 16+I.nB+1)
      (addr I.free I.capacity 16+I.nB+1+2*I.nC)
      (addr I.free I.capacity 17) (addr I.free I.capacity 17+I.nC))
    (hkB : ∀j<I.nB,keysB j=coefficientCode (TernaryNativeRequesterCoverage.sourceLeft H U radix (B j)))
    (hkC : ∀j<I.nC,keysC j=coefficientCode (TernaryNativeRequesterCoverage.sourceRight H U radix (C j))) :
    TernaryArenaSourceCountSeed.Reads (r := r) maps τ (selectedInput I U radix nA H A B C keysB keysC) ν := by
  have M' := M.after_cleanup (by dsimp [selectedInput,compactInput,TernaryArenaNativeComplete.input]; omega)
    (by dsimp [selectedInput,compactInput,TernaryArenaNativeComplete.input]; omega) hcounts hCc hlo hbank hpowers h
  refine ⟨?_,?_,?_,?_,M'.codes,M'.powers,M'.wanted⟩
  · intro i hi
    change ν (addr I.free I.capacity 16+i)=_
    rw [hOutB.2.2.2 i hi,hkB _ (index_lt hi)]
    rfl
  · intro i hi
    change ν (addr I.free I.capacity 17+i)=_
    rw [hOutC.2.2.2 i hi,hkC _ (index_lt hi)]
    rfl
  · intro i hi
    exact input_bound _
  · intro i hi
    exact input_bound _

end ThreeSum.TernaryArenaPostMemory
