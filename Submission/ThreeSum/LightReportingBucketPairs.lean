import Submission.ThreeSum.LightReportingBucketRow

/-!
# Exact original-value testing of a retained Cartesian bucket pair

Every pair of retained physical indices is tested using the original integer
arrays. The result counts exactly the pairs with `a+b=c`. An empty right
fiber skips the entire left scan, so the verified cost is linear in the
actual Cartesian pair mass plus one, including empty fibers.
-/

namespace ThreeSum.LightReportingBucketPairs

open Light Finset
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def count (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) : ℕ :=
  ∑ i ∈ range nL, LightReportingBucketRow.count (a+left (indexL i)) right indexR nR

@[simp] theorem count_zero (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR : ℕ) :
    count a left right indexL indexR nR 0 = 0 := by simp [count]

@[simp] theorem count_right_zero (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nL : ℕ) :
    count a left right indexL indexR 0 nL = 0 := by simp [count]

theorem count_succ (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) :
    count a left right indexL indexR nR (nL+1) = count a left right indexL indexR nR nL+
      LightReportingBucketRow.count (a+left (indexL nL)) right indexR nR :=
  Finset.sum_range_succ _ _

theorem count_le (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) :
    count a left right indexL indexR nR nL ≤ nL*nR := by
  unfold count
  calc
    _ ≤ ∑ _i ∈ range nL, nR :=
      Finset.sum_le_sum (fun i _ => LightReportingBucketRow.count_le _ _ _ _)
    _ = _ := by simp

theorem count_pos_iff (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ) (nR nL : ℕ) :
    0 < count a left right indexL indexR nR nL ↔
      ∃ i < nL, ∃ j < nR, right (indexR j)-left (indexL i)-a=0 := by
  rw [count,Finset.sum_pos_iff_of_nonneg (fun _ _ => Nat.zero_le _)]
  simp only [Finset.mem_range,LightReportingBucketRow.count_pos_iff]
  constructor
  · rintro ⟨i,hi,j,hj,he⟩
    exact ⟨i,hi,j,hj,by omega⟩
  · rintro ⟨i,hi,j,hj,he⟩
    exact ⟨i,hi,j,hj,by omega⟩

def roundBody (pRow : ℕ) : Stmt :=
  .set 11 (M (v 1 +' M (v 3 +' v 10))) ;;
  .set 12 (v 0 +' v 11) ;;
  .call pRow [v 12,v 2,v 4,v 6,v 8] 13 ;;
  .set 9 (v 9 +' v 13)

/-- A value, original left/right arrays, retained left/right index arrays,
selected left/right lengths, original left/right lengths. -/
def body (pRow : ℕ) : Stmt :=
  .set 9 (k 0) ;;
  .ite (k 0 <' v 6) (.for 10 (v 5) (roundBody pRow)) .skip ;;
  .set 0 (v 9)

def time (nL nR : ℕ) : ℕ := 240*nL*nR+100
def program : Program := [LightReportingBucketRow.body,body 0]

def Inv (μ : ℕ → ℤ) (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ)
    (srcL srcR indicesL indicesR nL nR NL NR i : ℕ) (σ : State) : Prop :=
  ∃ l target ret : ℤ,
    σ=⟨frame [a,(srcL : ℤ),(srcR : ℤ),(indicesL : ℤ),(indicesR : ℤ),(nL : ℤ),(nR : ℤ),
      (NL : ℤ),(NR : ℤ),(count a left right indexL indexR nR i : ℤ),(i : ℤ),l,target,ret],μ⟩

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pRow srcL srcR indicesL indicesR nL nR NL NR : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]? = some (body pRow)) (hrow : P[pRow]? = some LightReportingBucketRow.body)
    (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrcL : srcL+NL ≤ lim.space) (hsrcR : srcR+NR ≤ lim.space)
    (hindicesL : indicesL+nL ≤ lim.space) (hindicesR : indicesR+nR ≤ lim.space)
    (hindexL : ∀ i < nL, indexL i < NL) (hindexR : ∀ j < nR, indexR j < NR)
    (hreadIL : ∀ i < nL, μ (indicesL+i) = (indexL i : ℤ))
    (hreadIR : ∀ j < nR, μ (indicesR+j) = (indexR j : ℤ))
    (hreadL : ∀ i < NL, μ (srcL+i) = left i) (hreadR : ∀ j < NR, μ (srcR+j) = right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ lim.word) (hvaluesR : ∀ j < NR, |right j| ≤ lim.word)
    (ha : |a| ≤ lim.word) (htarget : ∀ i < NL, |a+left i| ≤ lim.word)
    (hcountWord : ((nL*nR : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [a,srcL,srcR,indicesL,indicesR,nL,nR,NL,NR] μ (time nL nR)
      (fun r ν => r=(count a left right indexL indexR nR nL : ℤ) ∧ ν=μ) := by
  have haBounds := abs_le.mp ha
  apply Meets.of_body hmain
  unfold body time
  light_set (0 : ℕ)
  light_if hrposZ hrzeroZ : (0 : ℤ)<(nR : ℤ)
  · have hrpos : 0<nR := by exact_mod_cast hrposZ
    have hnLcost : nL ≤ nL*nR := Nat.le_mul_of_pos_right _ hrpos
    refine Ends.pieceThen (Ends.for (lim := lim) (P := P) (d := d) (i := 10) (hi := v 5)
      (body := roundBody pRow) (T := nL*(LightReportingBucketRow.time nR+100)+30)
      (Q := Inv μ a left right indexL indexR srcL srcR indicesL indicesR nL nR NL NR nL)
      (Inv μ a left right indexL indexR srcL srcR indicesL indicesR nL nR NL NR)
      nL (LightReportingBucketRow.time nR+80) ?start ?round ?done ?bound
      (hT := by light_time [LightReportingBucketRow.time])) ?after
      (hT := by light_time [LightReportingBucketRow.time])
    case start =>
      refine ⟨0,0,0,?_⟩
      simp [update_frame_setLocal]
      exact (frame_append_zeros _ 3).symm
    case round =>
      rintro i _ hi _ ⟨oldLeft,oldTarget,oldRet,rfl⟩
      have hii := hindexL i hi
      have hreadIdx := hreadIL i hi
      have hreadVal := hreadL _ hii
      have hv := abs_le.mp (hvaluesL _ hii)
      have ht := abs_le.mp (htarget _ hii)
      have htotal := count_le a left right indexL indexR nR (i+1)
      have hmul := Nat.mul_le_mul_right nR (show i+1 ≤ nL by omega)
      have hnextWord : (count a left right indexL indexR nR (i+1) : ℤ) ≤ lim.word :=
        (Int.ofNat_le.mpr (htotal.trans hmul)).trans hcountWord
      have hnext := count_succ a left right indexL indexR nR i
      unfold roundBody
      light_set (left (indexL i)) using hreadIdx,hreadVal,LightReportingBucketRow.time
      light_set (a+left (indexL i)) using LightReportingBucketRow.time
      light_call (LightReportingBucketRow.meets (d := d+1) hrow (a+left (indexL i)) right indexR hw
        hsrcR hindicesR hindexR hreadIR hreadR hvaluesR (htarget _ hii))
        using LightReportingBucketRow.time with found ν ⟨hfound,hmem⟩
      subst ν
      light_set (count a left right indexL indexR nR (i+1) : ℕ)
        using hfound,hnext,LightReportingBucketRow.time
      exact ⟨by simp,left (indexL i),a+left (indexL i),found,by simp [update_frame_setLocal]⟩
    case done => intro σ _ hs; exact hs
    case bound => rintro i _ hi _ ⟨oldLeft,oldTarget,oldRet,rfl⟩; light_side
    case after =>
      rintro _ ⟨oldLeft,oldTarget,oldRet,rfl⟩
      have hc : (count a left right indexL indexR nR nL : ℤ) ≤ lim.word :=
        (Int.ofNat_le.mpr (count_le _ _ _ _ _ _ _)).trans hcountWord
      light_set (count a left right indexL indexR nR nL : ℕ) using LightReportingBucketRow.time
      exact ⟨rfl,rfl⟩
  · have hrzero : nR=0 := by omega
    light_set (0 : ℕ)
    simp [hrzero]

theorem program_meets {srcL srcR indicesL indicesR nL nR NL NR : ℕ} {μ : ℕ → ℤ}
    (a : ℤ) (left right : ℕ → ℤ) (indexL indexR : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrcL : srcL+NL ≤ lim.space) (hsrcR : srcR+NR ≤ lim.space)
    (hindicesL : indicesL+nL ≤ lim.space) (hindicesR : indicesR+nR ≤ lim.space)
    (hindexL : ∀ i < nL, indexL i < NL) (hindexR : ∀ j < nR, indexR j < NR)
    (hreadIL : ∀ i < nL, μ (indicesL+i) = (indexL i : ℤ))
    (hreadIR : ∀ j < nR, μ (indicesR+j) = (indexR j : ℤ))
    (hreadL : ∀ i < NL, μ (srcL+i) = left i) (hreadR : ∀ j < NR, μ (srcR+j) = right j)
    (hvaluesL : ∀ i < NL, |left i| ≤ lim.word) (hvaluesR : ∀ j < NR, |right j| ≤ lim.word)
    (ha : |a| ≤ lim.word) (htarget : ∀ i < NL, |a+left i| ≤ lim.word)
    (hcountWord : ((nL*nR : ℕ) : ℤ) ≤ lim.word) :
    Meets lim program 1 d [a,srcL,srcR,indicesL,indicesR,nL,nR,NL,NR] μ (time nL nR)
      (fun r ν => r=(count a left right indexL indexR nR nL : ℤ) ∧ ν=μ) :=
  meets rfl rfl a left right indexL indexR hw hd hsrcL hsrcR hindicesL hindicesR hindexL hindexR
    hreadIL hreadIR hreadL hreadR hvaluesL hvaluesR ha htarget hcountWord

end ThreeSum.LightReportingBucketPairs
