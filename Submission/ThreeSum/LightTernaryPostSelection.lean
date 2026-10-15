import Submission.ThreeSum.LightOriginalSurvivorResources
import Submission.ThreeSum.LightTernaryCompactReporter
import Submission.ThreeSum.TernaryCompactPairedSupport

/-! Actual post-selection solver: exact original collision cleanup, physical
compaction, empty-source guards, complete signed moment reporting and detector. -/
noncomputable section
namespace ThreeSum.LightTernaryPostSelection
open Light LightOriginalSurvivors LightOriginalSurvivorPair
open scoped BigOperators
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 24000

def body (pReporter : ℕ) : Stmt :=
  .call 8 (LightTernarySourceCountHost.callArgs 0 21) 148 ;;
  .ite (v 148 =' k 0)
    (.ite (M (v 16) =' k 0) (.set 0 (k 0))
      (.ite (M (v 20) =' k 0) (.set 0 (k 0))
        (.call pReporter (LightTernarySourceCountHost.callArgs 21 127) 0)))
    (.set 0 (k 1))

def libraries {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  ReportingHostRelocation.program LightOriginalSurvivorPair.program
    (LightTernaryCompactReporter.program S H)

def program {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ) : Program :=
  libraries S H ++ [body (9+(LightTernaryMomentReporter.program S H).length)]

def args {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (c : Layout)
    (scratch matrix : ℕ) : List ℤ := c.args ++
  LightTernaryCompactReporter.args S c.aBase c.nA scratch
    c.valueB c.packedB c.lengthB c.valueC c.packedC c.lengthC matrix

def time {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) (H : ℕ)
    (c : Layout) (keysB keysC : ℕ → ℕ) : ℕ :=
  LightOriginalSurvivorPair.time keysB keysC c.nA c.nB c.nC c.L+
    LightTernaryCompactReporter.time S H+600

def compact (keys : ℕ → ℕ) (values : ℕ → ℤ) (n : ℕ) : ℕ → ℤ :=
  fun j => values (index keys n j)

/-- Pure certificates linking the actual compact arrays to the complete source
and query model. No execution assumption occurs in this certificate. -/
structure Certificate {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (c : Layout) (lim : Limits) (d H a b U W detectorU scratch matrix : ℕ)
    (μ : ℕ → ℤ) (A B C : ℕ → ℤ) (keysB keysC position : ℕ → ℕ) : Prop where
  leftCount : S.left.NL = (indices keysB c.nB).length
  rightCount : S.right.NL = (indices keysC c.nC).length
  leftSrc : S.left.src = c.packedB
  rightSrc : S.right.src = c.packedC
  beforeMatrix : c.lengthC+1 ≤ matrix
  recordsApart : S.front.records+3*S.front.count ≤ c.outB ∨ c.lengthC < S.front.records
  matrixWindow : matrix+(2*H+1)*S.front.count ≤ scratch
  scratchSpace : scratch+(2*H+1) ≤ lim.space
  positions : ∀ i < S.front.count, position i < c.nA
  positionRead : ∀ i < S.front.count, μ (S.front.records+3*i) = (position i : ℤ)
  originalAbs : ∀ i < c.nA, |A i| ≤ (detectorU : ℤ)
  detectorWord : max (detectorU : ℤ) (LightMomentDeterminant.wordBound detectorU H) ≤ lim.word
  resources : ∀ ν,
    Output ν keysB B c.nB c.outB c.valueB c.packedB c.lengthB →
    Output ν keysC C c.nC c.outC c.valueC c.packedC c.lengthC → Kept μ ν c.outB →
    LightOriginalSurvivorStage.Above μ ν c.lengthC → c.Unchanged keysB keysC μ ν → LightTernaryCertifiedMomentDriver.Resources S lim (d+3) c.valueB c.valueC matrix
      (2*H+1) a b U W ν (compact keysB B c.nB) (compact keysC C c.nC)
  support : ∀ i < S.front.count,
    (TernaryPairedSupport.physicalSupport (TernaryNativePairMoments.mode (S := S) (i := i)
      (compact keysB B c.nB) (compact keysC C c.nC))).card ≤ H
  momentAbs : ∀ i < S.front.count, ∀ k ≤ 2*H,
    |∑ p : TernaryNativePairMoments.Pair S i,
      TernaryNativePairMoments.mass S i p*TernaryNativePairMoments.mode
        (compact keysB B c.nB) (compact keysC C c.nC) p^k| ≤ (detectorU : ℤ)
  nativeComplete :
    (∃ i < S.front.count, ∃ p : TernaryNativePairMoments.Pair S i,
      TernaryNativePairMoments.mode (compact keysB B c.nB) (compact keysC C c.nC) p=A (position i)) ↔
    (∃ i < c.nA, ∃ j < (indices keysB c.nB).length, ∃ k < (indices keysC c.nC).length,
      compact keysC C c.nC k=A i+compact keysB B c.nB j)

private theorem zero_test {lim : Limits} {loc μ : ℕ → ℤ} {x cell count : ℕ}
    (hp : loc x = (cell : ℤ)) (hr : μ cell = (count : ℤ)) (hc : cell < lim.space)
    (hw : (0 : ℤ) ≤ lim.word) :
    (M (v x) =' k 0).Safe lim ⟨loc,μ⟩ ∧
      ((M (v x) =' k 0).Holds ⟨loc,μ⟩ ↔ count = 0) := by
  constructor
  · change (True ∧ (0 ≤ loc x ∧ loc x < (lim.space : ℤ))) ∧ (0 : ℤ) ≤ lim.word
    rw [hp]
    exact ⟨⟨trivial,Int.natCast_nonneg _,by exact_mod_cast hc⟩,hw⟩
  · change μ ((loc x).toNat) = (0 : ℤ) ↔ count = 0
    rw [hp,Int.toNat_natCast,hr]
    exact_mod_cast (Iff.rfl : count = 0 ↔ _)

variable {lim : Limits}

theorem meets {N H d a b U W lookupW detectorU scratch matrix : ℕ}
    (S : TernarySourceCountExecutionFactory.Setup N) (c : Layout)
    (μ : ℕ → ℤ) (A B C : ℕ → ℤ) (keysB keysC position : ℕ → ℕ)
    (R : Resources c lim (d+1) U lookupW μ A B C keysB keysC)
    (F : Certificate S c lim d H a b U W detectorU scratch matrix μ A B C keysB keysC position) :
    Meets lim (program S H) (libraries S H).length d (args S c scratch matrix) μ
      (time S H c keysB keysC)
      (fun ret ν => ret = (if ∃ i < c.nA, ∃ j < c.nB, ∃ k < c.nC, C k=A i+B j
        then 1 else 0 : ℤ) ∧ Kept μ ν c.outB) := by
  have hpairlen : LightOriginalSurvivorPair.program.length = 9 := rfl
  have hcleanup : Meets lim (program S H) 8 (d+1) c.args μ
      (LightOriginalSurvivorPair.time keysB keysC c.nA c.nB c.nC c.L)
      (fun ret ν => ret = (cleanupFlag A B C keysB keysC c.nA c.nB c.nC : ℤ) ∧
        Output ν keysB B c.nB c.outB c.valueB c.packedB c.lengthB ∧
        Output ν keysC C c.nC c.outC c.valueC c.packedC c.lengthC ∧ Kept μ ν c.outB ∧
          LightOriginalSurvivorStage.Above μ ν c.lengthC ∧ c.Unchanged keysB keysC μ ν) := by
    have hh := R.run.append ((LightTernaryCompactReporter.program S H).map
      (ReportingHostRelocation.relocate 9) ++ [body (9+(LightTernaryMomentReporter.program S H).length)])
    simpa only [program,libraries,ReportingHostRelocation.program,hpairlen,List.append_assoc] using hh
  have hmain : (program S H)[(libraries S H).length]? =
      some (body (9+(LightTernaryMomentReporter.program S H).length)) := by simp [program]
  have hreads : LightTernarySourceCountHost.Reads (frame (args S c scratch matrix)) 0 c.args := by
    intro i hi
    change (c.args++_).getD (0+i) 0 = _
    simp only [Nat.zero_add]
    rw [List.getD_append _ _ _ _ hi]
  have hdepth := R.hd
  have hd : d < lim.depth := by have := R.hd; omega
  apply Meets.of_body hmain
  unfold body time
  refine Ends.callToThen hcleanup ?_
    (ha := ⟨LightTernarySourceCountHost.callArgs_safe _ _ _ _,
      LightTernarySourceCountHost.callArgs_values _ _ _ _ _ rfl hreads⟩)
    (hd := hd) (hT := by simp only [LightTernarySourceCountHost.callArgs_cost,Cond.cost,Expr.cost]; omega)
  intro cleanup ν ⟨hcleanup,hOutB,hOutC,hkeep,hAbove,hUnchanged⟩
  have htB := length_le keysB c.nB
  have htC := length_le keysC c.nC
  have hm : c.outB ≤ matrix := by
    have := F.beforeMatrix
    have := R.hB1; have := R.hB2; have := R.hB3; have := R.hBC
    have := R.hC1; have := R.hC2; have := R.hC3
    omega
  have hw := R.hw
  have hone : (1 : ℤ) ≤ lim.word := by have := R.hvalueWord; omega
  have hlengthB : c.lengthB < lim.space := by
    have := R.hBC; have := R.hC1; have := R.hC2; have := R.hC3; have := R.hEnd; omega
  have hlengthC : c.lengthC < lim.space := by have := R.hEnd; omega
  have hflag := cleanupFlag_le_one A B C keysB keysC c.nA c.nB c.nC
  have hsol := solution_iff A B C keysB keysC c.nA c.nB c.nC
  have hlocalResult : frame (setLocal (args S c scratch matrix) 148 cleanup) 148 = cleanup := by
    simp only [frame_setLocal,ite_true]
  have hlocalB : frame (setLocal (args S c scratch matrix) 148 cleanup) 16 = (c.lengthB : ℤ) := by
    rw [frame_setLocal,if_neg (by decide)]
    rfl
  have hlocalC : frame (setLocal (args S c scratch matrix) 148 cleanup) 20 = (c.lengthC : ℤ) := by
    rw [frame_setLocal,if_neg (by decide)]
    rfl
  light_head
  refine Ends.iteIffThen (cleanupFlag A B C keysB keysC c.nA c.nB c.nC = 0)
    (fun hz => ?_) (fun hnz => ?_) ?_ ?_
  on_goal -1 => light_time
  on_goal -1 =>
    constructor
    · exact ⟨trivial,show (0 : ℤ) ≤ lim.word by omega⟩
    · change frame (setLocal (args S c scratch matrix) 148 cleanup) 148 = (0 : ℤ) ↔ _
      rw [hlocalResult,hcleanup]
      exact_mod_cast (Iff.rfl : cleanupFlag A B C keysB keysC c.nA c.nB c.nC = 0 ↔ _)
  all_goals light_assoc
  · light_head
    refine Ends.iteIffThen ((indices keysB c.nB).length = 0) (fun hb => ?_) (fun hnb => ?_)
      (zero_test hlocalB hOutB.1 hlengthB (by omega)) (by light_time)
    all_goals light_assoc
    · have hnsol : ¬(∃ i < c.nA, ∃ j < c.nB, ∃ k < c.nC, C k=A i+B j) := by
        rw [hsol]
        simp [hz,hb]
      light_set (0 : ℤ)
      refine ⟨?_,hkeep⟩
      change (0 : ℤ) = _
      simp only [if_neg hnsol]
    · light_head
      refine Ends.iteIffThen ((indices keysC c.nC).length = 0) (fun hc => ?_) (fun hnc => ?_)
        (zero_test hlocalC hOutC.1 hlengthC (by omega)) (by light_time)
      all_goals light_assoc
      · have hnsol : ¬(∃ i < c.nA, ∃ j < c.nB, ∃ k < c.nC, C k=A i+B j) := by
          rw [hsol]
          simp [hz,hc]
        light_set (0 : ℤ)
        refine ⟨?_,hkeep⟩
        change (0 : ℤ) = _
        simp only [if_neg hnsol]
      · have RR := F.resources ν hOutB hOutC hkeep hAbove hUnchanged
        have hreport := LightTernaryCompactReporter.meets (d := d+1) S ν A
          (compact keysB B c.nB) (compact keysC C c.nC) position RR F.leftSrc F.rightSrc
          (by rw [F.leftCount]; exact hOutB.1) (by rw [F.rightCount]; exact hOutC.1)
          (by have := R.hBC; have := R.hC1; have := R.hC2; have := R.hC3; omega)
          (by have := R.hEnd; omega) (by have := R.hA; omega) F.matrixWindow F.scratchSpace
          F.positions (fun i hi => (show ν (S.front.records+3*i)=μ (S.front.records+3*i) from by
            rcases F.recordsApart with hb | ha
            · apply hkeep
              have hh := Nat.mul_le_mul_left 3 (show i+1 ≤ S.front.count by omega)
              omega
            · exact hAbove _ (by omega)).trans (F.positionRead i hi))
          (fun i hi => (hkeep _ (by have := R.hA; omega)).trans (R.hreadA i hi))
          F.originalAbs F.detectorWord F.support F.momentAbs
        have hr := (ReportingHostRelocation.meets hreport LightOriginalSurvivorPair.program).append
          [body (9+(LightTernaryMomentReporter.program S H).length)]
        have hr' : Meets lim (program S H) (9+(LightTernaryMomentReporter.program S H).length) (d+1)
            (LightTernaryCompactReporter.args S c.aBase c.nA scratch c.valueB c.packedB c.lengthB
              c.valueC c.packedC c.lengthC matrix) ν (LightTernaryCompactReporter.time S H)
            (fun r ξ => r=(if ∃ i < S.front.count, ∃ p : TernaryNativePairMoments.Pair S i,
              TernaryNativePairMoments.mode (compact keysB B c.nB) (compact keysC C c.nC) p=A (position i)
              then 1 else 0 : ℤ) ∧ Kept ν ξ matrix) := by
          simpa only [program,libraries,hpairlen,Nat.add_comm] using hr
        have hreadRep : LightTernarySourceCountHost.Reads
            (frame (setLocal (args S c scratch matrix) 148 cleanup)) 21
            (LightTernaryCompactReporter.args S c.aBase c.nA scratch c.valueB c.packedB c.lengthB
              c.valueC c.packedC c.lengthC matrix) := by
          intro i hi
          have hlen : (LightTernaryCompactReporter.args S c.aBase c.nA scratch c.valueB c.packedB
              c.lengthB c.valueC c.packedC c.lengthC matrix).length = 127 := rfl
          have hi' : i < 127 := by simpa only [hlen] using hi
          rw [frame_setLocal,if_neg (by omega)]
          change (c.args++_).getD (21+i) 0 = _
          rw [List.getD_append_right _ _ _ _ (by simp [Layout.args])]
          simp only [Layout.args,List.length_cons,List.length_nil,Nat.reduceAdd,Nat.add_sub_cancel_left]
        refine Ends.callToThen hr' ?_
          (ha := ⟨LightTernarySourceCountHost.callArgs_safe _ _ _ _,
            LightTernarySourceCountHost.callArgs_values _ _ _ _ _ (by rfl) hreadRep⟩)
          (hd := by have := R.hd; omega)
          (hT := by simp only [LightTernarySourceCountHost.callArgs_cost,Cond.cost,Expr.cost]; omega)
        intro result ξ ⟨hresult,hkeepR⟩
        light_skip
        have heq : (∃ i < c.nA, ∃ j < c.nB, ∃ k < c.nC, C k=A i+B j) ↔
            (∃ i < S.front.count, ∃ p : TernaryNativePairMoments.Pair S i,
              TernaryNativePairMoments.mode (compact keysB B c.nB) (compact keysC C c.nC) p=A (position i)) := by
          rw [hsol]
          simpa only [hz,zero_ne_one,false_or,compact] using F.nativeComplete.symm
        refine ⟨?_,fun x hx => (hkeepR x (by omega)).trans (hkeep x hx)⟩
        change result = _
        simpa only [heq] using hresult
  · have hflagOne : cleanupFlag A B C keysB keysC c.nA c.nB c.nC = 1 := by omega
    have hyes : ∃ i < c.nA, ∃ j < c.nB, ∃ k < c.nC, C k=A i+B j := hsol.mpr (Or.inl hflagOne)
    light_set (1 : ℤ)
    refine ⟨?_,hkeep⟩
    change (1 : ℤ) = _
    simp only [if_pos hyes]

end ThreeSum.LightTernaryPostSelection
