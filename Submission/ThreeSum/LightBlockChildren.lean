import Submission.ThreeSum.ReportingHostMasks
import Submission.ThreeSum.LightQueryEnumeration
import Submission.ThreeSum.LightReportingAffine

/-!
# Actual construction of every next-block reporting child

The fixed program enumerates the balanced subsets of the next block directly
in global coordinates. Two affine scans then write the exact left and right
prefix masks of every child, and subtraction returns the next residual mask.
All enumeration and scan execution is discharged by concrete procedures.
-/

namespace ThreeSum.LightBlockChildren

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open QueryCoordinates ReportingHostMasks

variable {lim : Limits} {P : Program}

/-- Width, child cardinality, next-row mask, left/right prefixes, remaining
query mask, child-mask destination, left/right destinations, scratch. -/
def body (pEnum pAffine : ℕ) : Stmt :=
  .call pEnum [v 0,v 2,v 1,v 6,v 9] 10 ;;
  .set 11 (v 4 +' v 2) ;;
  .call pAffine [v 6,v 7,v 10,v 3,k 1] 12 ;;
  .call pAffine [v 6,v 8,v 10,v 11,k 0 -' k 1] 12 ;;
  .set 0 (v 5 -' v 2)

def time (W c h : ℕ) : ℕ :=
  LightQueryEnumeration.time W c h+2*LightReportingAffine.time (c.choose h)+100

def leftMasks {W : ℕ} (A Q : Finset (Fin W)) (h : ℕ) : List ℕ :=
  (missingSets Q h).map fun S => subsetMask (A ∪ S)

def rightMasks {W : ℕ} (B Q : Finset (Fin W)) (h : ℕ) : List ℕ :=
  (missingSets Q h).map fun S => subsetMask (B ∪ (Q \ S))

structure Procs (P : Program) (pEnum pAffine : ℕ) where
  pWeights : ℕ
  pPowers : ℕ
  pErase : ℕ
  pRec : ℕ
  enumBody : P[pEnum]? = some (LightQueryEnumeration.body pWeights pRec)
  weightsBody : P[pWeights]? = some (LightQueryWeights.body pPowers pErase)
  powersBody : P[pPowers]? = some powTableBody
  eraseBody : P[pErase]? = some (LightMaskErase.body pErase)
  recBody : P[pRec]? = some (LightSubsetEnumeration.body pRec)
  affineBody : P[pAffine]? = some LightReportingAffine.body

theorem meets {pMain pEnum pAffine : ℕ}
    (hmain : P[pMain]? = some (body pEnum pAffine)) (C : Procs P pEnum pAffine)
    {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    Meets lim P pMain d
      [W,h,subsetMask Q,subsetMask A,subsetMask B,subsetMask R,masks,dstL,dstR,work]
      μ (time W Q.card h)
      (fun r μ' =>
        r = (subsetMask (R \ Q) : ℤ) ∧
        SegN μ' masks ((missingSets Q h).map subsetMask) ∧
        SegN μ' dstL (leftMasks A Q h) ∧
        SegN μ' dstR (rightMasks B Q h) ∧ Kept μ μ' masks) := by
  have hmask (S : Finset (Fin W)) : |(subsetMask S : ℤ)| ≤ lim.word := by
    rw [Int.abs_natCast]
    have hs : subsetMask S ≤ 2^(W+1) :=
      (Nat.le_of_lt (subsetMask_isMask S).1).trans
        (Nat.pow_le_pow_right (by decide) (by omega))
    exact (by exact_mod_cast hs : (subsetMask S : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  have hcard : Q.card ≤ W := by simpa using Finset.card_le_univ Q
  have hbias : (subsetMask B : ℤ)+(subsetMask Q : ℤ) = (subsetMask (B ∪ Q) : ℤ) := by
    rw [mask_union _ _ hBQ]
    simp
  have hreturn := MaskDifference.subsetMask_sdiff_int R Q hQR
  have hAword := abs_le.mp (hmask A)
  have hBword := abs_le.mp (hmask B)
  have hQword := abs_le.mp (hmask Q)
  have hRword := abs_le.mp (hmask R)
  have hBiasWord := abs_le.mp (hmask (B ∪ Q))
  have hReturnWord := abs_le.mp (hmask (R \ Q))
  apply Meets.of_body hmain
  unfold body time
  have henum := LightQueryEnumeration.meets (d := d+1) (μ := μ)
    (dst := masks) (work := work) C.enumBody C.weightsBody C.powersBody C.eraseBody C.recBody Q
    hw hspace hword hh (by omega) (by omega)
  light_call henum using LightQueryEnumeration.time,LightReportingAffine.time
    with count μ₁ ⟨hcount,hstored,_,hkeep₁⟩
  light_set (subsetMask (B ∪ Q) : ℕ) using hbias,LightQueryEnumeration.time,LightReportingAffine.time
  have hread₁ (i : ℕ) (hi : i < Q.card.choose h) :
      μ₁ (masks+i) = (subsetMask ((missingSets Q h)[i]'(by simpa using hi)) : ℤ) := by
    have hs := hstored i (by simpa using hi)
    simpa only [List.getElem_map] using hs
  have hleftEq (i : ℕ) (hi : i < Q.card.choose h) :
      (subsetMask A : ℤ)+1*μ₁ (masks+i) =
        (subsetMask (A ∪ (missingSets Q h)[i]'(by simpa using hi)) : ℤ) := by
    have ht := (missingSets_mem Q _ h).mp (List.getElem_mem (by simpa using hi))
    rw [hread₁ i hi,one_mul,mask_union _ _ (hAQ.mono_right ht.1)]
    simp
  have hcallL := LightReportingAffine.meets (d := d+1) (μ := μ₁)
    (src := masks) (dst := dstL) (n := Q.card.choose h) (b := (subsetMask A : ℤ)) (c := 1)
    C.affineBody hw (by omega) (by omega) (Or.inr (Or.inl hmasks))
    (by intro i hi; rw [hread₁ i hi,one_mul]; exact hmask _)
    (by intro i hi; rw [hleftEq i hi]; exact hmask _)
  light_call hcallL using LightQueryEnumeration.time,LightReportingAffine.time,hcount
    with retL μ₂ ⟨houtL,hkeepL⟩
  have hstored₂ : SegN μ₂ masks ((missingSets Q h).map subsetMask) :=
    hstored.of_sameOutside hkeepL (Or.inl (by simpa using hmasks))
  have hread₂ (i : ℕ) (hi : i < Q.card.choose h) : μ₂ (masks+i) = μ₁ (masks+i) :=
    hkeepL _ (Or.inl (by omega))
  have hrightEq (i : ℕ) (hi : i < Q.card.choose h) :
      (subsetMask (B ∪ Q) : ℤ)+(-1)*μ₂ (masks+i) =
        (subsetMask (B ∪ (Q \ (missingSets Q h)[i]'(by simpa using hi))) : ℤ) := by
    have ht := (missingSets_mem Q _ h).mp (List.getElem_mem (by simpa using hi))
    rw [hread₂ i hi,hread₁ i hi,← hbias,mask_union _ _ (hBQ.mono_right Finset.sdiff_subset)]
    push_cast
    rw [← MaskDifference.subsetMask_sdiff_int _ _ ht.1]
    ring
  have hcallR := LightReportingAffine.meets (d := d+1) (μ := μ₂)
    (src := masks) (dst := dstR) (n := Q.card.choose h) (b := (subsetMask (B ∪ Q) : ℤ)) (c := -1)
    C.affineBody hw (by omega) (by omega) (Or.inr (Or.inl (by omega)))
    (by intro i hi; rw [hread₂ i hi,hread₁ i hi]; simpa using hmask ((missingSets Q h)[i]'(by simpa using hi)))
    (by intro i hi; rw [hrightEq i hi]; exact hmask _)
  light_call hcallR using LightQueryEnumeration.time,LightReportingAffine.time,hcount
    with retR μ₃ ⟨houtR,hkeepR⟩
  light_set (subsetMask (R \ Q) : ℕ) using hreturn,LightQueryEnumeration.time,LightReportingAffine.time
  refine ⟨by simp,?_,?_,?_,?_⟩
  · exact hstored₂.of_sameOutside hkeepR (Or.inl (by simp; omega))
  · intro i hi
    have hin : i < Q.card.choose h := by simpa only [leftMasks,SegN,List.length_map,missingSets_length] using hi
    change μ₃ (dstL+i) = _
    rw [hkeepR (dstL+i) (Or.inl (by omega)),houtL i hin,hleftEq i hin]
    simp [leftMasks]
  · intro i hi
    have hin : i < Q.card.choose h := by simpa only [rightMasks,SegN,List.length_map,missingSets_length] using hi
    change μ₃ (dstR+i) = _
    rw [houtR i hin,hrightEq i hin]
    simp [rightMasks]
  · intro i hi
    exact (hkeepR i (Or.inl (by omega))).trans
      ((hkeepL i (Or.inl (by omega))).trans (hkeep₁ i ⟨by omega,Or.inl hi⟩))

def program : Program :=
  [body 1 6,LightQueryEnumeration.body 2 5,LightQueryWeights.body 3 4,powTableBody,
    LightMaskErase.body 4,LightSubsetEnumeration.body 5,LightReportingAffine.body]

def procs : Procs program 1 6 := ⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {W h masks dstL dstR work d : ℕ}
    (A B Q R : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hAQ : Disjoint A Q) (hBQ : Disjoint B Q) (hQR : Q ⊆ R)
    (hh : h ≤ Q.card+1)
    (hmasks : masks+Q.card.choose h ≤ dstL)
    (hleft : dstL+Q.card.choose h ≤ dstR)
    (hright : dstR+Q.card.choose h ≤ work)
    (hspace : work+(2*W+2) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+3 ≤ lim.depth) :
    Meets lim program 0 d
      [W,h,subsetMask Q,subsetMask A,subsetMask B,subsetMask R,masks,dstL,dstR,work]
      μ (time W Q.card h)
      (fun r μ' =>
        r = (subsetMask (R \ Q) : ℤ) ∧
        SegN μ' masks ((missingSets Q h).map subsetMask) ∧
        SegN μ' dstL (leftMasks A Q h) ∧
        SegN μ' dstR (rightMasks B Q h) ∧ Kept μ μ' masks) :=
  meets rfl procs A B Q R hw hAQ hBQ hQR hh hmasks hleft hright hspace hword hd

theorem time_bound {W c h : ℕ} (hc : c ≤ W) :
    time W c h ≤ 1600*(W+1)^2*(c.choose h+1) := by
  have he := LightQueryEnumeration.time_bound (t := h) hc
  have hpow : 1 ≤ (W+1)^2 := by nlinarith
  unfold time LightReportingAffine.time
  nlinarith

end ThreeSum.LightBlockChildren
