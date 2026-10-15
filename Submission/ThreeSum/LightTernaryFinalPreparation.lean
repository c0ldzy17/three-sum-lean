import Submission.ThreeSum.LightOriginalCollisionScore
import Submission.ThreeSum.LightSubsetAddress

/-! Actual final cleanup prerequisites: one power table and both literal
original-source collision histograms, with exact untouched-memory semantics. -/
noncomputable section
namespace ThreeSum.LightTernaryFinalPreparation
open Light LightSubsetAddress
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def body : Stmt :=
  .call 4 [v 5,v 6 +' k 1,k 2] 9 ;;
  .call 0 [v 0,v 1,v 7,v 4] 9 ;;
  .call 0 [v 2,v 3,v 8,v 4] 0

def program : Program := LightOriginalCollisionScore.program ++ [powTableBody,body]
def time (nB nC q W : ℕ) : ℕ :=
  powTableTime (W+1)+LightOriginalCollisionScore.time nB q+LightOriginalCollisionScore.time nC q+200

def Unwritten (powers W histB histC q x : ℕ) : Prop :=
  (x < powers ∨ powers+(W+1) ≤ x) ∧ (x < histB ∨ histB+q ≤ x) ∧ (x < histC ∨ histC+q ≤ x)

variable {lim : Limits}

theorem meets {keyB nB keyC nC q powers W histB histC d : ℕ}
    (μ : ℕ → ℤ) (keysB keysC : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeyB : keyB+nB ≤ powers) (hkeyC : keyC+nC ≤ powers)
    (hpowers : powers+(W+1) ≤ histB) (hhistB : histB+q ≤ histC) (hhistC : histC+q ≤ lim.space)
    (hwordB : ((nB*nB+nB+q+16 : ℕ) : ℤ) ≤ lim.word)
    (hwordC : ((nC*nC+nC+q+16 : ℕ) : ℤ) ≤ lim.word)
    (hpowerWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysB : ∀ i < nB, keysB i < q) (hkeysC : ∀ i < nC, keysC i < q)
    (hreadB : ∀ i < nB, μ (keyB+i) = (keysB i : ℤ))
    (hreadC : ∀ i < nC, μ (keyC+i) = (keysC i : ℤ))
    (hd : d+3 ≤ lim.depth) :
    Meets lim program 5 d [keyB,nB,keyC,nC,q,powers,W,histB,histC] μ (time nB nC q W)
      (fun _ ν => Powers ν powers W ∧
        (∀ k < q, ν (histB+k) = (LightHistogram.count keysB k nB : ℤ)) ∧
        (∀ k < q, ν (histC+k) = (LightHistogram.count keysC k nC : ℤ)) ∧
        Kept μ ν powers ∧ (∀ x, Unwritten powers W histB histC q x → ν x = μ x)) := by
  have hp := powTable_meets (P := program) (p := 4) (d := d+1) (μ := μ)
    (dst := powers) (L := W+1) (b := 2) rfl hw (by omega) (by
      intro j hj
      exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowerWord)
  apply Meets.of_body (p := 5) (by rfl : program[5]? = some body)
  unfold body time
  light_call hp using powTableTime,LightOriginalCollisionScore.time
    with ignored ν ⟨hPowers,hRestP⟩
  have hPB := powers_of_segment hPowers
  have hreadB' : ∀ i < nB, ν (keyB+i) = (keysB i : ℤ) := by
    intro i hi
    exact (hRestP _ (Or.inl (by omega))).trans (hreadB i hi)
  have hB := LightOriginalCollisionScore.meets (P := program) (pMain := 0) (pHist := 1)
    (pFill := 2) (pSum := 3) (d := d+1) (src := keyB) (n := nB) (hist := histB) (q := q) rfl rfl rfl rfl ν keysB hw (by omega) (by omega)
    (Or.inl (by omega)) hwordB hkeysB hreadB' (by omega)
  light_call hB using powTableTime,LightOriginalCollisionScore.time
    with ignoredB ξ ⟨hScoreB,hCountsB,hRestB⟩
  have hreadC' : ∀ i < nC, ξ (keyC+i) = (keysC i : ℤ) := by
    intro i hi
    exact (hRestB _ (Or.inl (by omega))).trans ((hRestP _ (Or.inl (by omega))).trans (hreadC i hi))
  have hC := LightOriginalCollisionScore.meets (P := program) (pMain := 0) (pHist := 1)
    (pFill := 2) (pSum := 3) (d := d+1) (src := keyC) (n := nC) (hist := histC) (q := q) rfl rfl rfl rfl ξ keysC hw (by omega) (by omega)
    (Or.inl (by omega)) hwordC hkeysC hreadC' (by omega)
  light_call hC using powTableTime,LightOriginalCollisionScore.time
    with ignoredC ζ ⟨hScoreC,hCountsC,hRestC⟩
  refine ⟨?_,?_,hCountsC,?_,?_⟩
  · intro i hi
    change ζ (powers+i) = (2^i : ℕ)
    rw [hRestC _ (Or.inl (by omega)),hRestB _ (Or.inl (by omega))]
    exact hPB i hi
  · intro k hk
    exact (hRestC _ (Or.inl (by omega))).trans (hCountsB k hk)
  · intro x hx
    exact (hRestC _ (Or.inl (by omega))).trans
      ((hRestB _ (Or.inl (by omega))).trans (hRestP _ (Or.inl hx)))
  · intro x hx
    exact (hRestC x hx.2.2).trans ((hRestB x hx.2.1).trans (hRestP x hx.1))

@[simp] theorem program_length : program.length = 6 := rfl

theorem time_eq (nB nC q W : ℕ) : time nB nC q W = 74*(nB+nC)+26*q+17*W+659 := by
  unfold time
  rw [LightOriginalCollisionScore.time_eq,LightOriginalCollisionScore.time_eq]
  unfold powTableTime
  ring

end ThreeSum.LightTernaryFinalPreparation
