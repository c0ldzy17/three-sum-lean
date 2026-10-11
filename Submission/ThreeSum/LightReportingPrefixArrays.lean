import Submission.ThreeSum.ReportingHostPairSegments
import Submission.ThreeSum.LightRadixKeys

/-!
# Constructing both complete prefix-mask product arrays in the same record order

The local pair arrays are built directly, then the verified positional-key
host is used twice with radix 2^L. Both results share the literal tuple order,
including separate entries for pairs with equal left or right projections.
-/

namespace ThreeSum.LightReportingPrefixArrays

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostPairEnumeration ReportingHostPairSegments

set_option maxHeartbeats 1200000
set_option maxRecDepth 8000

variable {lim : Limits}

def localCount (L h : ℕ) : ℕ := L.choose (2*h)*(2*h).choose h

def body (pPairs pPowers pKeys : ℕ) : Stmt :=
  .call pPairs [v 0,v 1,v 3,v 4,v 5,v 8] 9 ;;
  .call pPowers [v 8,v 0 +' k 1,k 2] 10 ;;
  .set 11 (M (v 8 +' v 0)) ;;
  .call pKeys [v 4,v 9,v 2,v 11,v 6] 12 ;;
  .call pKeys [v 5,v 9,v 2,v 11,v 7] 13 ;;
  .set 0 (v 12)

def program : Program := LightReportingPairRows.program ++
  [LightRadixKeys.body 8 9,LightRadixRows.body 6,body 7 2 8]

def time (L h k : ℕ) : ℕ :=
  LightReportingPairRows.time L h+powTableTime (L+1)+2*LightRadixKeys.time (localCount L h) k+250

theorem program_meets {μ : ℕ → ℤ} {L h k srcS pairL pairR stageL stageR work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hh : 2*h ≤ L)
    (hS : srcS+L.choose h ≤ pairL)
    (hL : pairL+localCount L h ≤ pairR) (hR : pairR+localCount L h ≤ stageL)
    (hstageL : LightRadixKeys.space stageL (localCount L h) k ≤ stageR)
    (hstageR : LightRadixKeys.space stageR (localCount L h) k ≤ work)
    (hspace : work+2*L+2 ≤ lim.space)
    (hpowWord : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^L) (2^L) k : ℤ) ≤ lim.word)
    (hd : d+L+k+4 ≤ lim.depth) :
    Meets lim program 10 d [L,h,k,srcS,pairL,pairR,stageL,stageR,work] μ (time L h k)
      (fun r μ' =>
        r = (stageL+LightRadixKeys.offset (localCount L h) k : ℕ) ∧
        μ' (stageL+LightRadixKeys.offset (localCount L h) k) = ((localCount L h)^k : ℕ) ∧
        μ' (stageR+LightRadixKeys.offset (localCount L h) k) = ((localCount L h)^k : ℕ) ∧
        Seg μ' (stageL+LightRadixKeys.offset (localCount L h) k+1)
          (RadixKeyLists.values ((2^L : ℕ) : ℤ) (leftMasks L h) k) ∧
        Seg μ' (stageR+LightRadixKeys.offset (localCount L h) k+1)
          (RadixKeyLists.values ((2^L : ℕ) : ℤ) (rightMasks L h) k) ∧
        Kept μ μ' srcS) := by
  have hpos : 0 < localCount L h := Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))
  have hleftLen : (leftMasks L h).length = localCount L h := leftMasks_length L h
  have hrightLen : (rightMasks L h).length = localCount L h := rightMasks_length L h
  have hstageOrder : stageL ≤ stageR := by unfold LightRadixKeys.space at hstageL; omega
  have hworkOrder : stageR ≤ work := by unfold LightRadixKeys.space at hstageR; omega
  have hpowBound : ∀ j ≤ L+1, ((2^j : ℕ) : ℤ) ≤ lim.word := by
    intro j hj
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hj)).trans hpowWord
  have hpairProd : L.choose h*(L-h).choose h = localCount L h := LayerCounts.vertex_degree_identity L h
  apply Meets.of_body (p := 10) (by rfl : program[10]? = some (body 7 2 8))
  unfold body time
  have hp := (ReportingHostPairSegments.program_meets (d := d+1) (μ := μ)
    (L := L) (h := h) (srcS := srcS) (dstL := pairL) (dstR := pairR) (work := work)
    hw hh hS (by simpa only [hpairProd] using hL) (by rw [hpairProd]; omega) hspace hpowWord (by omega)).append
      [LightRadixKeys.body 8 9,LightRadixRows.body 6,body 7 2 8]
  light_call hp using LightReportingPairRows.time,LightRadixKeys.time,powTableTime
    with count μ₁ ⟨hcount,hleft,hright,hkeepPair⟩
  have hcount' : count = (localCount L h : ℤ) := hcount
  have hpow := powTable_meets (P := program) (p := 2) (d := d+1) (μ := μ₁)
    (dst := work) (L := L+1) (b := 2) rfl hw (by omega) hpowBound
  light_call hpow using LightReportingPairRows.time,LightRadixKeys.time,powTableTime
    with powRet μ₂ ⟨hpowers,hkeepPowers⟩
  have hreadPow := powers_of_segment hpowers L le_rfl
  have hreadPowNat : μ₂ (work+L) = ((2^L : ℕ) : ℤ) := by simpa using hreadPow
  have hradix := hpowBound L (by omega)
  light_set (2^L : ℕ) using hreadPow,hreadPowNat,LightReportingPairRows.time,LightRadixKeys.time,powTableTime
  have hleft₂ : Seg μ₂ pairL (leftMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hleftLen] at hi; omega))]
    exact hleft i hi
  have hright₂ : Seg μ₂ pairR (rightMasks L h) := by
    intro i hi
    rw [hkeepPowers _ (Or.inl (by rw [hrightLen] at hi; omega))]
    exact hright i hi
  have hl := LightRadixKeys.meets (P := program) (pMain := 8) (pRows := 9) (pAffine := 6)
    (src := pairL) (dst := stageL) (p := 2^L) (U := 2^L) rfl rfl rfl
    (leftMasks L h) hw (by rw [hleftLen]; omega) (by rw [hleftLen]; exact hpos)
    (leftMasks_bounded L h) k (d+1) μ₂
    (by rw [hleftLen]; exact hstageL.trans (by omega)) hkeysWord (by omega) hleft₂
  simp only [hleftLen] at hl
  light_call hl using hcount',LightReportingPairRows.time,LightRadixKeys.time,powTableTime
    with leftHead μ₃ ⟨hleftHead,hleftHeader,hleftArray,hkeepLeft⟩
  have hright₃ : Seg μ₃ pairR (rightMasks L h) := by
    intro i hi
    rw [hkeepLeft _ (by rw [hrightLen] at hi; omega)]
    exact hright₂ i hi
  have hr := LightRadixKeys.meets (P := program) (pMain := 8) (pRows := 9) (pAffine := 6)
    (src := pairR) (dst := stageR) (p := 2^L) (U := 2^L) rfl rfl rfl
    (rightMasks L h) hw (by rw [hrightLen]; omega) (by rw [hrightLen]; exact hpos)
    (rightMasks_bounded L h) k (d+1) μ₃
    (by rw [hrightLen]; exact hstageR.trans (by omega)) hkeysWord (by omega) hright₃
  simp only [hrightLen] at hr
  light_call hr using hcount',LightReportingPairRows.time,LightRadixKeys.time,powTableTime
    with rightHead μ₄ ⟨hrightHead,hrightHeader,hrightArray,hkeepRight⟩
  have hleftBound : stageL+LightRadixKeys.offset (localCount L h) k+1+(localCount L h)^k ≤ stageR := hstageL
  light_set (stageL+LightRadixKeys.offset (localCount L h) k : ℕ)
    using hleftHead,LightReportingPairRows.time,LightRadixKeys.time,powTableTime
  refine ⟨by simp,?_,hrightHeader,?_,hrightArray,?_⟩
  · change μ₄ (stageL+LightRadixKeys.offset (localCount L h) k) = _
    rw [hkeepRight _ (by omega)]
    exact hleftHeader
  · intro i hi
    change μ₄ (stageL+LightRadixKeys.offset (localCount L h) k+1+i) = _
    rw [hkeepRight _ (by simp only [RadixKeyLists.values_length,hleftLen] at hi; omega)]
    exact hleftArray i hi
  · intro i hi
    exact (hkeepRight i (by omega)).trans ((hkeepLeft i (by omega)).trans
      ((hkeepPowers i (Or.inl (by omega))).trans (hkeepPair i hi)))

theorem time_bound {L h k : ℕ} (hh : 2*h ≤ L) :
    time L h k ≤ 5000*(L+1)^2*(localCount L h+1)+
      600*(k+1)*((localCount L h)^k+1)+300 := by
  have hp := LightReportingPairRows.time_bound hh
  have hk := LightRadixKeys.time_bound (localCount L h) k
    (Nat.one_le_of_lt (Nat.mul_pos (Nat.choose_pos hh) (Nat.choose_pos (by omega))))
  unfold time powTableTime
  change LightReportingPairRows.time L h ≤ 4000*(L+1)^2*(localCount L h+1) at hp
  nlinarith

end ThreeSum.LightReportingPrefixArrays
