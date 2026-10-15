import Submission.ThreeSum.LightTernaryFinalPreparation
import Submission.ThreeSum.LightTernaryPostSelectionClosed

noncomputable section
namespace ThreeSum.LightTernaryPreparedPostSelection
open Light LightSubsetAddress LightOriginalSurvivorPair LightOriginalCollisionCleanup
set_option maxHeartbeats 4000000
set_option maxRecDepth 24000

structure Inputs (c : Layout) (lim : Limits) (d U W : ℕ) (μ : ℕ → ℤ)
    (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) : Prop where
  hw : (lim.space : ℤ) ≤ lim.word
  hA : c.aBase+c.nA ≤ c.outB
  hB : c.bBase+c.nB ≤ c.outB
  hC : c.cBase+c.nC ≤ c.outB
  hkB : c.keyB+c.nB ≤ c.outB
  hkC : c.keyC+c.nC ≤ c.outB
  hhB : c.histB+c.q ≤ c.outB
  hhC : c.histC+c.q ≤ c.outB
  hp : c.powers+(W+1) ≤ c.outB
  hB1 : c.outB+2*c.nB ≤ c.valueB
  hB2 : c.valueB+c.nB ≤ c.packedB
  hB3 : c.packedB+c.nB ≤ c.lengthB
  hBC : c.lengthB+1 ≤ c.outC
  hC1 : c.outC+2*c.nC ≤ c.valueC
  hC2 : c.valueC+c.nC ≤ c.packedC
  hC3 : c.packedC+c.nC ≤ c.lengthC
  hEnd : c.lengthC+1 ≤ lim.space
  hword : ((c.nB+c.nC+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word
  hkeysB : ∀ i < c.nB, keysB i < c.q
  hkeysC : ∀ i < c.nC, keysC i < c.q
  hreadKB : ∀ i < c.nB, μ (c.keyB+i) = (keysB i : ℤ)
  hreadKC : ∀ i < c.nC, μ (c.keyC+i) = (keysC i : ℤ)
  hboundA : ∀ i < c.nA, |A i| ≤ U
  hboundB : ∀ i < c.nB, |B i| ≤ U
  hboundC : ∀ i < c.nC, |C i| ≤ U
  hreadA : ∀ i < c.nA, μ (c.aBase+i) = A i
  hreadB : ∀ i < c.nB, μ (c.bBase+i) = B i
  hreadC : ∀ i < c.nC, μ (c.cBase+i) = C i
  hvalueWord : 2*(U : ℤ)+3 ≤ lim.word
  hsortedB : ∀ i j, i < j → j < c.nB → B i < B j
  hsortedC : ∀ i j, i < j → j < c.nC → C i < C j
  hL : c.L ≤ W
  hnB : c.nB < 2^c.L
  hnC : c.nC < 2^c.L
  hd : d+c.L+5 ≤ lim.depth

  beforeA : c.aBase+c.nA ≤ c.powers
  beforeB : c.bBase+c.nB ≤ c.powers
  beforeC : c.cBase+c.nC ≤ c.powers
  beforeKeyB : c.keyB+c.nB ≤ c.powers
  beforeKeyC : c.keyC+c.nC ≤ c.powers
  powerBeforeHist : c.powers+(W+1) ≤ c.histB
  histBeforeHist : c.histB+c.q ≤ c.histC
  scoreWordB : ((c.nB*c.nB+c.nB+c.q+16 : ℕ) : ℤ) ≤ lim.word
  scoreWordC : ((c.nC*c.nC+c.nC+c.q+16 : ℕ) : ℤ) ≤ lim.word

theorem Inputs.finish {c : Layout} {lim : Limits} {d U W : ℕ} {μ ν : ℕ → ℤ}
    {A B C : ℕ → ℤ} {keysB keysC : ℕ → ℕ}
    (S : Inputs c lim d U W μ A B C keysB keysC)
    (hpowers : Powers ν c.powers W)
    (hcB : ∀ k < c.q, ν (c.histB+k) = (LightHistogram.count keysB k c.nB : ℤ))
    (hcC : ∀ k < c.q, ν (c.histC+k) = (LightHistogram.count keysC k c.nC : ℤ))
    (hkeep : Kept μ ν c.powers) : Resources c lim d U W ν A B C keysB keysC := by
  exact {
    hw := S.hw
    hA := S.hA
    hB := S.hB
    hC := S.hC
    hkB := S.hkB
    hkC := S.hkC
    hhB := S.hhB
    hhC := S.hhC
    hp := S.hp
    hB1 := S.hB1
    hB2 := S.hB2
    hB3 := S.hB3
    hBC := S.hBC
    hC1 := S.hC1
    hC2 := S.hC2
    hC3 := S.hC3
    hEnd := S.hEnd
    hword := S.hword
    hkeysB := S.hkeysB
    hkeysC := S.hkeysC
    hreadKB := fun i hi => (hkeep _ (by have := S.beforeKeyB; omega)).trans (S.hreadKB i hi)
    hreadKC := fun i hi => (hkeep _ (by have := S.beforeKeyC; omega)).trans (S.hreadKC i hi)
    hboundA := S.hboundA
    hboundB := S.hboundB
    hboundC := S.hboundC
    hreadA := fun i hi => (hkeep _ (by have := S.beforeA; omega)).trans (S.hreadA i hi)
    hreadB := fun i hi => (hkeep _ (by have := S.beforeB; omega)).trans (S.hreadB i hi)
    hreadC := fun i hi => (hkeep _ (by have := S.beforeC; omega)).trans (S.hreadC i hi)
    hvalueWord := S.hvalueWord
    hsortedB := S.hsortedB
    hsortedC := S.hsortedC
    hL := S.hL
    hnB := S.hnB
    hnC := S.hnC
    hd := S.hd
    hcountsB := hcB
    hcountsC := hcC
    hpowers := hpowers }

def body (pPost : ℕ) : Stmt :=
  .call 5 [v 6,v 3,v 7,v 5,v 10,v 11,v 12,v 8,v 9] 148 ;;
  .call pPost (LightTernarySourceCountHost.callArgs 0 148) 0

def libraries {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightTernaryFinalPreparation.program (LightTernaryPostSelection.program S H)

def program {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  libraries S H ++ [body (6+(LightTernaryPostSelection.libraries S H).length)]

def args {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (c : Layout) (scratch matrix : ℕ) : List ℤ :=
  LightTernaryPostSelection.args S c scratch matrix

def time {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) (c : Layout)
    (keysB keysC : ℕ → ℕ) : ℕ :=
  LightTernaryFinalPreparation.time c.nB c.nC c.q c.L + LightTernaryPostSelection.time S H c keysB keysC+200

theorem meets {lim : Limits} {N d H a b U V detectorU scratch matrix : ℕ}
    (S : TernarySourceCountExecutionFactory.Setup N) (c : Layout)
    (μ : ℕ → ℤ) (A B C : ℕ → ℤ) (keysB keysC position : ℕ → ℕ)
    (R : Inputs c lim (d+2) U c.L μ A B C keysB keysC)
    (F : ∀ ν,
      Powers ν c.powers c.L →
      (∀ k < c.q, ν (c.histB+k) = (LightHistogram.count keysB k c.nB : ℤ)) →
      (∀ k < c.q, ν (c.histC+k) = (LightHistogram.count keysC k c.nC : ℤ)) →
      Kept μ ν c.powers →
      (∀ x, LightTernaryFinalPreparation.Unwritten c.powers c.L c.histB c.histC c.q x → ν x = μ x) →
      LightTernaryPostSelection.Certificate S c lim (d+1) H a b U V detectorU scratch matrix ν A B C keysB keysC position) :
    Meets lim (program S H) (libraries S H).length d (args S c scratch matrix) μ (time S H c keysB keysC)
      (fun ret ν => ret = (if ∃ i < c.nA, ∃ j < c.nB, ∃ k < c.nC, C k=A i+B j then 1 else 0 : ℤ) ∧
        Kept μ ν c.powers) := by
  have hp : Meets lim (program S H) 5 (d+1)
      [c.keyB,c.nB,c.keyC,c.nC,c.q,c.powers,c.L,c.histB,c.histC] μ
      (LightTernaryFinalPreparation.time c.nB c.nC c.q c.L)
      (fun _ ν => Powers ν c.powers c.L ∧
        (∀ k < c.q, ν (c.histB+k) = (LightHistogram.count keysB k c.nB : ℤ)) ∧
        (∀ k < c.q, ν (c.histC+k) = (LightHistogram.count keysC k c.nC : ℤ)) ∧
        Kept μ ν c.powers ∧
        (∀ x, LightTernaryFinalPreparation.Unwritten c.powers c.L c.histB c.histC c.q x → ν x = μ x)) := by
    have hh := (LightTernaryFinalPreparation.meets (d := d+1) μ keysB keysC R.hw R.beforeKeyB R.beforeKeyC
      R.powerBeforeHist R.histBeforeHist (by
        have := R.hhC; have := R.hB1; have := R.hB2; have := R.hB3; have := R.hBC
        have := R.hC1; have := R.hC2; have := R.hC3; have := R.hEnd; omega)
      R.scoreWordB R.scoreWordC (by have := R.hword; omega) R.hkeysB R.hkeysC R.hreadKB R.hreadKC
      (by have := R.hd; omega)).append
        ((LightTernaryPostSelection.program S H).map (ReportingHostRelocation.relocate 6)++
          [body (6+(LightTernaryPostSelection.libraries S H).length)])
    simpa only [program,libraries,ReportingHostRelocation.program,LightTernaryFinalPreparation.program_length,
      List.append_assoc] using hh
  apply Meets.of_body (by simp [program] : (program S H)[(libraries S H).length]? =
    some (body (6+(LightTernaryPostSelection.libraries S H).length)))
  unfold body time
  have hd := R.hd
  light_call hp using args,LightTernaryPostSelection.args,Layout.args,LightTernaryFinalPreparation.time,
    LightTernaryPostSelection.time with ignored ν ⟨hPowers,hCountsB,hCountsC,hkeep,hRest⟩
  have RR := R.finish hPowers hCountsB hCountsC hkeep
  have FF := F ν hPowers hCountsB hCountsC hkeep hRest
  have hr := (ReportingHostRelocation.meets
    (LightTernaryPostSelection.meets (d := d+1) S c ν A B C keysB keysC position RR FF)
    LightTernaryFinalPreparation.program).append [body (6+(LightTernaryPostSelection.libraries S H).length)]
  have hr' : Meets lim (program S H) (6+(LightTernaryPostSelection.libraries S H).length) (d+1)
      (LightTernaryPostSelection.args S c scratch matrix) ν (LightTernaryPostSelection.time S H c keysB keysC)
      (fun ret ξ => ret = (if ∃ i < c.nA, ∃ j < c.nB, ∃ k < c.nC, C k=A i+B j then 1 else 0 : ℤ) ∧
        Kept ν ξ c.outB) := by
    simpa only [program,libraries,LightTernaryFinalPreparation.program_length] using hr
  have hreads : LightTernarySourceCountHost.Reads
      (frame (setLocal (args S c scratch matrix) 148 ignored)) 0
      (LightTernaryPostSelection.args S c scratch matrix) := by
    intro i hi
    have hii : i < 148 := by simpa using hi
    rw [frame_setLocal,if_neg (by omega)]
    simp only [args,frame,Nat.zero_add]
  refine Ends.callTo hr' ?_
    (ha := ⟨LightTernarySourceCountHost.callArgs_safe _ _ _ _,
      LightTernarySourceCountHost.callArgs_values _ _ _ _ _ (by rfl) hreads⟩)
    (hd := by omega)
    (hT := by simp only [LightTernarySourceCountHost.callArgs_cost,List.map_cons,List.map_nil,
      List.sum_cons,List.sum_nil,Expr.cost]; omega)
  intro ret ξ ⟨hret,hkeepR⟩
  refine ⟨?_,fun x hx => (hkeepR x (by have := R.hp; omega)).trans (hkeep x hx)⟩
  change ret = _
  exact hret

def closedProgram (xl yl zl xr yr zr : List ℤ) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightTernaryFinalPreparation.program
    (LightTernaryPostSelection.closedProgram xl yl zl xr yr zr H)++
      [body (6+(127*(TernaryMomentSchedule.channels (2*H+1)).length+17))]

theorem program_eq_closed {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    program S H = closedProgram S.left.xs S.left.ys S.left.zs S.right.xs S.right.ys S.right.zs H := by
  unfold program libraries closedProgram
  rw [LightTernaryPostSelection.program_eq_closed,LightTernaryPostSelection.libraries_length]

@[simp] theorem libraries_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    (libraries S H).length = 127*(TernaryMomentSchedule.channels (2*H+1)).length+24 := by
  simp [libraries,ReportingHostRelocation.program] <;> omega

@[simp] theorem program_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) :
    (program S H).length = 127*(TernaryMomentSchedule.channels (2*H+1)).length+25 := by
  simp [program]

@[simp] theorem args_length {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (c : Layout) (scratch matrix : ℕ) : (args S c scratch matrix).length = 148 := rfl

@[simp] theorem closedProgram_length (xl yl zl xr yr zr : List ℤ) (H : ℕ) :
    (closedProgram xl yl zl xr yr zr H).length =
      127*(TernaryMomentSchedule.channels (2*H+1)).length+25 := by
  have hpair : LightOriginalSurvivorPair.program.length = 9 := rfl
  have hdriver : (LightTernaryMomentDriver.program xl yl zl xr yr zr
      (TernaryMomentSchedule.channels (2*H+1)) (2*H+1) 115).length =
        127*(TernaryMomentSchedule.channels (2*H+1)).length+2 := by
    simp [LightTernaryMomentDriver.program]
  unfold closedProgram LightTernaryPostSelection.closedProgram
    LightTernaryCompactReporter.closedProgram LightTernaryMomentReporter.closedProgram
  simp only [ReportingHostRelocation.program,List.length_append,List.length_map,List.length_cons,List.length_nil,
    LightTernaryFinalPreparation.program_length,hpair,hdriver,LightTernaryMomentBatch.program]
  omega

end ThreeSum.LightTernaryPreparedPostSelection
