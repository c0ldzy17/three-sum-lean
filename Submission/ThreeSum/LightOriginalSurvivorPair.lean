import Submission.ThreeSum.LightOriginalSurvivorStage

/-! Closed actual cleanup and compaction of both original source classes. -/
noncomputable section
namespace ThreeSum.LightOriginalSurvivorPair
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

def body : Stmt :=
  .call 7 [v 6,v 3,v 8,v 10,v 13,v 2,v 0,v 1,v 4,v 5,v 11,v 12,k 1,v 14,v 15,v 16] 21 ;;
  .call 7 [v 7,v 5,v 9,v 10,v 17,v 4,v 0,v 1,v 2,v 3,v 11,v 12,k 0 -' k 1,v 18,v 19,v 20] 22 ;;
  .ite (v 21 =' k 0) (.set 0 (v 22)) (.set 0 (k 1))

def program : Program := LightOriginalSurvivorStage.program ++ [body]
def time (keysB keysC : ℕ → ℕ) (nA nB nC L : ℕ) : ℕ :=
  LightOriginalSurvivorStage.time keysB nB nA L + LightOriginalSurvivorStage.time keysC nC nA L+200

def Output (ν : ℕ → ℤ) (keys : ℕ → ℕ) (values : ℕ → ℤ)
    (n out dstValues dstKeys lengthCell : ℕ) : Prop :=
  ν lengthCell = ((indices keys n).length : ℤ) ∧
  Seg ν out (cells (indices keys n)) ∧
  (∀ i < (indices keys n).length, ν (dstValues+i) = values (index keys n i)) ∧
  (∀ i < (indices keys n).length, ν (dstKeys+i) = (keys (index keys n i) : ℤ))

theorem Output.of_kept {μ ν : ℕ → ℤ} {keys : ℕ → ℕ} {values : ℕ → ℤ}
    {n out dstValues dstKeys lengthCell bound : ℕ}
    (h : Output μ keys values n out dstValues dstKeys lengthCell)
    (hk : Kept μ ν bound) (ha : out+n ≤ bound) (hb : dstValues+n ≤ bound)
    (hc : dstKeys+n ≤ bound) (hd : lengthCell < bound) :
    Output ν keys values n out dstValues dstKeys lengthCell := by
  have ht := length_le keys n
  refine ⟨(hk _ hd).trans h.1,?_,?_,?_⟩
  · intro i hi
    have hi' : i < (indices keys n).length := by simpa [cells] using hi
    exact (hk _ (by omega)).trans (h.2.1 i hi)
  · intro i hi
    exact (hk _ (by omega)).trans (h.2.2.1 i hi)
  · intro i hi
    exact (hk _ (by omega)).trans (h.2.2.2 i hi)

variable {lim : Limits}

theorem program_meets {aBase nA bBase nB cBase nC keyB keyC histB histC q powers W L U d
    outB valueB packedB lengthB outC valueC packedC lengthC : ℕ}
    (μ : ℕ → ℤ) (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hA : aBase+nA ≤ outB) (hB : bBase+nB ≤ outB) (hC : cBase+nC ≤ outB)
    (hkB : keyB+nB ≤ outB) (hkC : keyC+nC ≤ outB)
    (hhB : histB+q ≤ outB) (hhC : histC+q ≤ outB) (hp : powers+(W+1) ≤ outB)
    (hB1 : outB+2*nB ≤ valueB) (hB2 : valueB+nB ≤ packedB) (hB3 : packedB+nB ≤ lengthB)
    (hBC : lengthB+1 ≤ outC)
    (hC1 : outC+2*nC ≤ valueC) (hC2 : valueC+nC ≤ packedC) (hC3 : packedC+nC ≤ lengthC)
    (hEnd : lengthC+1 ≤ lim.space)
    (hword : ((nB+nC+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hkeysB : ∀ i < nB, keysB i < q) (hkeysC : ∀ i < nC, keysC i < q)
    (hreadKB : ∀ i < nB, μ (keyB+i) = (keysB i : ℤ))
    (hreadKC : ∀ i < nC, μ (keyC+i) = (keysC i : ℤ))
    (hcountsB : ∀ k < q, μ (histB+k) = (counts keysB nB k : ℤ))
    (hcountsC : ∀ k < q, μ (histC+k) = (counts keysC nC k : ℤ))
    (hboundA : ∀ i < nA, |A i| ≤ U) (hboundB : ∀ i < nB, |B i| ≤ U)
    (hboundC : ∀ i < nC, |C i| ≤ U)
    (hreadA : ∀ i < nA, μ (aBase+i) = A i) (hreadB : ∀ i < nB, μ (bBase+i) = B i)
    (hreadC : ∀ i < nC, μ (cBase+i) = C i)
    (hvalueWord : 2*(U : ℤ)+3 ≤ lim.word) (hpowers : Powers μ powers W)
    (hsortedB : ∀ i j, i < j → j < nB → B i < B j)
    (hsortedC : ∀ i j, i < j → j < nC → C i < C j)
    (hL : L ≤ W) (hnB : nB < 2^L) (hnC : nC < 2^L) (hd : d+L+5 ≤ lim.depth) :
    Meets lim program 8 d
      [aBase,nA,bBase,nB,cBase,nC,keyB,keyC,histB,histC,q,powers,L,
        outB,valueB,packedB,lengthB,outC,valueC,packedC,lengthC]
      μ (time keysB keysC nA nB nC L)
      (fun ret ν =>
        ret = (if LightDeletedTwoSum.flag (badIndex keysB nB) B A C nC nA
          (badIndices keysB nB).length 1 = 0 then
          (LightDeletedTwoSum.flag (badIndex keysC nC) C A B nB nA
            (badIndices keysC nC).length (-1) : ℤ) else 1) ∧
        Output ν keysB B nB outB valueB packedB lengthB ∧
        Output ν keysC C nC outC valueC packedC lengthC ∧ Kept μ ν outB ∧
          LightOriginalSurvivorStage.Above μ ν lengthC ∧
          (∀ x, LightOriginalSurvivorStage.Unwritten outB nB valueB packedB (indices keysB nB).length lengthB x →
            LightOriginalSurvivorStage.Unwritten outC nC valueC packedC (indices keysC nC).length lengthC x →
            ν x = μ x)) := by
  have hfirst := (LightOriginalSurvivorStage.program_meets (d := d+1) (W := W) (U := U) (L := L)
    (keyBase := keyB) (n := nB) (hist := histB) (q := q) (out := outB)
    (valuesBase := bBase) (scanBase := aBase) (scanN := nA) (targetBase := cBase) (targetN := nC)
    (powers := powers) (dstValues := valueB) (dstKeys := packedB) (lengthCell := lengthB)
    1 μ keysB B A C hw hkB hhB hB hA hC hp hB1 hB2 hB3 (by omega)
    (by omega) hkeysB hreadKB hcountsB hboundB hreadB hboundA hreadA hreadC
    (by norm_num) hvalueWord hpowers hsortedC hL hnC (by omega)).append [body]
  apply Meets.of_body (p := 8) (by rfl : program[8]? = some body)
  unfold body time
  light_call hfirst using LightOriginalSurvivorStage.time with retB ν ⟨hrB,hlB,hiB,hvB,hkB,hKeepB,hAboveB,hRestB⟩
  have hOutB : Output ν keysB B nB outB valueB packedB lengthB := ⟨hlB,hiB,hvB,hkB⟩
  have hPowers : Powers ν powers W := by
    intro i hi
    rw [hKeepB _ (by omega),hpowers i hi]
  have hsecond := (LightOriginalSurvivorStage.program_meets (d := d+1) (W := W) (U := U) (L := L)
    (keyBase := keyC) (n := nC) (hist := histC) (q := q) (out := outC)
    (valuesBase := cBase) (scanBase := aBase) (scanN := nA) (targetBase := bBase) (targetN := nB)
    (powers := powers) (dstValues := valueC) (dstKeys := packedC) (lengthCell := lengthC)
    (-1) ν keysC C A B hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    hC1 hC2 hC3 hEnd (by omega) hkeysC
    (fun i hi => (hKeepB _ (by omega)).trans (hreadKC i hi))
    (fun k hk => (hKeepB _ (by omega)).trans (hcountsC k hk)) hboundC
    (fun i hi => (hKeepB _ (by omega)).trans (hreadC i hi)) hboundA
    (fun i hi => (hKeepB _ (by omega)).trans (hreadA i hi))
    (fun i hi => (hKeepB _ (by omega)).trans (hreadB i hi))
    (by norm_num) hvalueWord hPowers hsortedB hL hnB (by omega)).append [body]
  light_call hsecond using LightOriginalSurvivorStage.time with retC ξ ⟨hrC,hlC,hiC,hvC,hkC,hKeepC,hAboveC,hRestC⟩
  have hOutB' := hOutB.of_kept hKeepC (by omega) (by omega) (by omega) (by omega)
  have hOutC : Output ξ keysC C nC outC valueC packedC lengthC := ⟨hlC,hiC,hvC,hkC⟩
  have hKeep : Kept μ ξ outB := fun x hx => (hKeepC x (by omega)).trans (hKeepB x hx)
  have hAbove : LightOriginalSurvivorStage.Above μ ξ lengthC := by
    intro x hx
    exact (hAboveC x hx).trans (hAboveB x (by omega))
  light_if hz hnz : LightDeletedTwoSum.flag (badIndex keysB nB) B A C nC nA
      (badIndices keysB nB).length 1 = 0 using hrB
  · light_set retC
    refine ⟨?_,hOutB',hOutC,hKeep,hAbove,fun x hxB hxC => (hRestC x hxC).trans (hRestB x hxB)⟩
    change retC = _
    simpa only [if_pos hz] using hrC
  · light_set (1 : ℤ)
    refine ⟨?_,hOutB',hOutC,hKeep,hAbove,fun x hxB hxC => (hRestC x hxC).trans (hRestB x hxB)⟩
    change (1 : ℤ) = _
    simp only [if_neg hnz]

def cleanupFlag (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) : ℕ :=
  if LightDeletedTwoSum.flag (badIndex keysB nB) B A C nC nA
      (badIndices keysB nB).length 1 = 0 then
    LightDeletedTwoSum.flag (badIndex keysC nC) C A B nB nA
      (badIndices keysC nC).length (-1) else 1

theorem cleanupFlag_le_one (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    cleanupFlag A B C keysB keysC nA nB nC ≤ 1 := by
  unfold cleanupFlag
  split
  · exact LightDeletedTwoSum.flag_le_one _ _ _ _ _ _ _ _
  · omega

theorem cleanupFlag_eq_one_iff (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    cleanupFlag A B C keysB keysC nA nB nC = 1 ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) := by
  unfold cleanupFlag LightDeletedTwoSum.flag
  by_cases hB : LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1
  · simp [hB]
  · by_cases hC : LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA
        (badIndices keysC nC).length (-1) <;> simp [hB,hC]

theorem solution_iff (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i < nA, ∃ j < nB, ∃ k < nC, C k = A i+B j) ↔
      cleanupFlag A B C keysB keysC nA nB nC = 1 ∨
      ∃ i < nA, ∃ j < (indices keysB nB).length, ∃ k < (indices keysC nC).length,
        C (index keysC nC k) = A i+B (index keysB nB j) := by
  rw [cleanupFlag_eq_one_iff,or_assoc]
  exact LightOriginalSurvivors.colored_decomposition _ _ _ _ _ _ _ _

theorem stage_time_bound (keys : ℕ → ℕ) (n scanN L : ℕ) :
    LightOriginalSurvivorStage.time keys n scanN L ≤ 280*n+720+
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card*
        (scanN*(120*L+330)+300) := by
  have h := LightOriginalCollisionCleanup.time_bound keys n scanN L
  have ht := length_le keys n
  unfold LightOriginalSurvivorStage.time LightReportingGather.time
  omega

theorem time_bound (keysB keysC : ℕ → ℕ) (nA nB nC L : ℕ) :
    time keysB keysC nA nB nC L ≤ 280*(nB+nC)+1640+
      ((TernaryOriginalCollisions.collisionPairs (fun i : Fin nB => keysB i.val)).card+
       (TernaryOriginalCollisions.collisionPairs (fun i : Fin nC => keysC i.val)).card)*
        (nA*(120*L+330)+300) := by
  have hb := stage_time_bound keysB nB nA L
  have hc := stage_time_bound keysC nC nA L
  unfold time
  rw [Nat.add_mul]
  omega

end ThreeSum.LightOriginalSurvivorPair
