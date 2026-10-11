import Submission.ThreeSum.LightWeightDecode
import Submission.ThreeSum.LightLocalCoverHashHistogram
import Submission.ThreeSum.LightLocalCoverRow

/-!
# One complete local candidate: coefficients, bucket counts, and cover row

All data are constructed by fixed benchmark-language procedures. Separate
candidate histograms and coefficient rows are retained, while raw hash and
residue buffers are reusable. The preservation contract supports the outer
exhaustive candidate loop without forgetting previously completed rows.
-/

namespace ThreeSum.LightLocalCoverCandidate

open Light

set_option maxHeartbeats 2000000
set_option maxRecDepth 6000

def body (pDecode pHash pRow : ℕ) : Stmt :=
  .call pDecode [v 0,v 1,v 2,v 7,v 13] 14 ;;
  .call pHash [v 0,v 5,v 8,v 8 +' v 3,v 10,v 3,v 7,v 7 +' v 0,v 1,v 13] 14 ;;
  .call pHash [v 0,v 5,v 9,v 9 +' v 3,v 11,v 3,v 7 +' v 0,v 7,v 1,v 13] 14 ;;
  .call pRow [v 6,v 8 +' v 3,v 9 +' v 3,v 10,v 11,v 12,v 3,v 0,v 1,v 4,v 13] 14

def time (L n p index : ℕ) : ℕ := LightWeightDecode.time L index+
  2*LightHashHistogram.time L n p p+LightLocalCoverRow.time L n p+200
def word (L n p cap index : ℕ) : ℕ := LightWeightDecode.word L p index+
  LightHashHistogram.word L p p+LightPairFlags.word L n p cap
def space (work L n p : ℕ) : ℕ :=
  work+2*(n*n)+(2*L+1)+max (L+1) (Nat.log 2 (L*p+1)+2)

def entry (L n p cap : ℕ) (mask : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (w0 w1 : ℕ → ℕ) (r : ℕ) : ℕ :=
  let left := LightHashHistogram.code L p mask w0 w1
  let right := LightHashHistogram.code L p mask w1 w0
  LightSupportMark.bit (LightPairFlags.pairKey n p left right)
    (LightPairFlags.pairFlag L n cap bits left right
      (fun r => LightHistogram.count left r n) (fun r => LightHistogram.count right r n)) r (n*n)

def Preserved (μ ν : ℕ → ℤ) (work coef raw0 raw1 hist0 hist1 dst L n p : ℕ) : Prop :=
  ∀ a, a < work → Outside coef (2*L) a → Outside raw0 (2*n) a → Outside raw1 (2*n) a →
    Outside hist0 p a → Outside hist1 p a → Outside dst (p*p) a → ν a = μ a

structure Procs (P : Program) (pMain : ℕ) where
  pDecode : ℕ
  pHash : ℕ
  pRow : ℕ
  decode : LightWeightDecode.Procs P pDecode
  hash : LightHashHistogram.Procs P pHash
  row : LightLocalCoverRow.Procs P pRow
  main : P[pMain]? = some (body pDecode pHash pRow)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L n p cap index masks bitPtr coef raw0 raw1 hist0 hist1 dst work : ℕ}
    (mask w0 w1 : ℕ → ℕ) (bits : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+4 ≤ lim.depth) (hp : 0 < p) (hn : 0 < n)
    (hspace : space work L n p ≤ lim.space)
    (hmasks : masks+n ≤ coef) (hbits : bitPtr+n*L ≤ coef) (hcoef : coef+2*L ≤ raw0)
    (hraw0 : raw0+2*n ≤ raw1) (hraw1 : raw1+2*n ≤ hist0)
    (hhist0 : hist0+p ≤ hist1) (hhist1 : hist1+p ≤ dst) (hdst : dst+p*p ≤ work)
    (hword : (word L n p cap index : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hw0 : ∀ i < L, w0 i = WeightEnumeration.digit p (2*L) index (2*i))
    (hw1 : ∀ i < L, w1 i = WeightEnumeration.digit p (2*L) index (2*i+1)) :
    Meets lim P pMain d [L,p,index,n,cap,masks,bitPtr,coef,raw0,raw1,hist0,hist1,dst,work] μ
      (time L n p index)
      (fun _ μ' => LightWeightDecode.Rows μ' coef L p index ∧
        (∀ r < p,
          μ' (hist0+r) = (LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n : ℤ) ∧
          μ' (hist1+r) = (LightHistogram.count (LightHashHistogram.code L p mask w1 w0) r n : ℤ)) ∧
        (∀ r < p*p, μ' (dst+r) = (entry L n p cap mask bits w0 w1 r : ℤ)) ∧
        Preserved μ μ' work coef raw0 raw1 hist0 hist1 dst L n p) := by
  have hwork : work ≤ lim.space := by unfold space at hspace; omega
  have hdecodeSpace : work+(2*L+1) ≤ lim.space := by unfold space at hspace; omega
  have hhashSpace : LightHashHistogram.space work L p ≤ lim.space := by
    unfold space at hspace
    unfold LightHashHistogram.space
    omega
  have hrowSpace : work+2*(n*n) ≤ lim.space := by unfold space at hspace; omega
  have hbudget (x : ℕ) (hx : x ≤ word L n p cap index) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hdecodeWord := hbudget (LightWeightDecode.word L p index) (by unfold word; omega)
  have hhashWord := hbudget (LightHashHistogram.word L p p) (by unfold word; omega)
  have hrowWord := hbudget (LightPairFlags.word L n p cap) (by unfold word; omega)
  have hindexWord := hbudget index (by unfold word LightWeightDecode.word LightWeightRow.word; omega)
  have hnWord := hbudget n (by unfold word LightPairFlags.word; omega)
  have hLWord := hbudget L (by unfold word LightPairFlags.word; omega)
  have hpWord := hbudget p (by unfold word LightPairFlags.word; omega)
  have hcapWord := hbudget cap (by unfold word LightPairFlags.word; omega)
  have hb0 : ∀ i < L, w0 i ≤ p := by
    intro i hi
    rw [hw0 i hi]
    exact Nat.le_of_lt (WeightEnumeration.digit_lt hp)
  have hb1 : ∀ i < L, w1 i ≤ p := by
    intro i hi
    rw [hw1 i hi]
    exact Nat.le_of_lt (WeightEnumeration.digit_lt hp)
  apply Meets.of_body S.main
  unfold body time
  have hdcall := S.decode.meets (d := d+1) (μ := μ) (L := L) (p := p) (k := index)
    (dst := coef) (work := work) hw (by omega) (by omega) (by omega) hdecodeSpace hdecodeWord
  light_call hdcall using LightWeightDecode.time,LightWeightRow.time,LightRadixDigit.time,
    LightHashHistogram.time,LightLocalCoverRow.time
    with value₀ μ₁ ⟨hrows,_,hkeep₀⟩
  have hmask₁ : ∀ i < n, μ₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    rw [hkeep₀ _ ⟨by omega,Or.inl (by omega)⟩]
    exact hmaskRead i hi
  have hc0 : ∀ i < L, μ₁ (coef+i) = (w0 i : ℤ) := by
    intro i hi
    rw [(hrows i hi).1,hw0 i hi]
  have hc1 : ∀ i < L, μ₁ (coef+L+i) = (w1 i : ℤ) := by
    intro i hi
    rw [(hrows i hi).2,hw1 i hi]
  have hlcall := LightLocalCoverHashHistogram.meets S.hash (d := d+1) (μ := μ₁)
    (L := L) (n := n) (p := p) (U := p) (masks := masks) (raw := raw0) (codes := raw0+n)
    (hist := hist0) (src0 := coef) (src1 := coef+L) (work := work) mask w0 w1
    hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega)
    hhashWord hmask₁ hmaskLt hc0 hc1 hb0 hb1
  light_call hlcall using LightWeightDecode.time,LightWeightRow.time,LightRadixDigit.time,
    LightHashHistogram.time,LightLocalCoverRow.time
    with value₁ μ₂ ⟨hleftCodes,hleftCounts,hkeep₁,hpres₁⟩
  have hmask₂ : ∀ i < n, μ₂ (masks+i) = (mask i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hmask₁ i hi
  have hc0₂ : ∀ i < L, μ₂ (coef+i) = (w0 i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc0 i hi
  have hc1₂ : ∀ i < L, μ₂ (coef+L+i) = (w1 i : ℤ) := by
    intro i hi
    rw [hkeep₁ _ (by omega)]
    exact hc1 i hi
  have hrcall := LightLocalCoverHashHistogram.meets S.hash (d := d+1) (μ := μ₂)
    (L := L) (n := n) (p := p) (U := p) (masks := masks) (raw := raw1) (codes := raw1+n)
    (hist := hist1) (src0 := coef+L) (src1 := coef) (work := work) mask w1 w0
    hw (by omega) hp hhashSpace (by omega) (by omega) (by omega) le_rfl (by omega) (by omega)
    hhashWord hmask₂ hmaskLt hc1₂ hc0₂ hb1 hb0
  light_call hrcall using LightWeightDecode.time,LightWeightRow.time,LightRadixDigit.time,
    LightHashHistogram.time,LightLocalCoverRow.time
    with value₂ μ₃ ⟨hrightCodes,hrightCounts,hkeep₂,hpres₂⟩
  have hleftCodes₃ : ∀ i < n, μ₃ (raw0+n+i) = (LightHashHistogram.code L p mask w0 w1 i : ℤ) := by
    intro i hi
    rw [hkeep₂ _ (by omega)]
    exact hleftCodes i hi
  have hleftCounts₃ : ∀ r < p,
      μ₃ (hist0+r) = (LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n : ℤ) := by
    intro r hr
    rw [hpres₂ _ (by omega) (Or.inr (by omega)) (Or.inr (by omega)) (Or.inl (by omega))]
    exact hleftCounts r hr
  have hbits₃ : ∀ i < n, ∀ j < L, μ₃ (bitPtr+i*L+j) = (bits i j : ℤ) := by
    intro i hi j hj
    have hm := Nat.mul_le_mul_right L (show i+1 ≤ n by omega)
    have ha : bitPtr+i*L+j < coef := by nlinarith
    rw [hkeep₂ _ (by omega),hkeep₁ _ (by omega),hkeep₀ _ ⟨by omega,Or.inl ha⟩]
    exact hbitsRead i hi j hj
  have hrowcall := S.row.meets (d := d+1) (μ := μ₃) (bitPtr := bitPtr)
    (leftPtr := raw0+n) (rightPtr := raw1+n) (leftHist := hist0) (rightHist := hist1)
    (dst := dst) (n := n) (L := L) (p := p) (cap := cap) (keys := work)
    bits (LightHashHistogram.code L p mask w0 w1) (LightHashHistogram.code L p mask w1 w0)
    (fun r => LightHistogram.count (LightHashHistogram.code L p mask w0 w1) r n)
    (fun r => LightHistogram.count (LightHashHistogram.code L p mask w1 w0) r n)
    hw (by omega) hn hp (by omega) (by omega) (by omega) (by omega) (by omega) hdst hrowSpace hrowWord
    hbits₃ hbitsValue hleftCodes₃ hrightCodes
    (fun _ _ => LightResidues.residue_lt hp 1 _) (fun _ _ => LightResidues.residue_lt hp 1 _)
    hleftCounts₃ hrightCounts (fun r _ => LightHistogram.count_le _ r n)
    (fun r _ => LightHistogram.count_le _ r n)
  light_call hrowcall using LightWeightDecode.time,LightWeightRow.time,LightRadixDigit.time,
    LightHashHistogram.time,LightLocalCoverRow.time
    with value₃ μ₄ ⟨hout,hkeep₃⟩
  refine ⟨?_,?_,hout,?_⟩
  · intro i hi
    constructor
    · change μ₄ (coef+i) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩,hkeep₂ _ (by omega),hkeep₁ _ (by omega)]
      exact (hrows i hi).1
    · change μ₄ (coef+L+i) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩,hkeep₂ _ (by omega),hkeep₁ _ (by omega)]
      exact (hrows i hi).2
  · intro r hr
    constructor
    · change μ₄ (hist0+r) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩]
      exact hleftCounts₃ r hr
    · change μ₄ (hist1+r) = _
      rw [hkeep₃ _ ⟨by omega,Or.inl (by omega)⟩]
      exact hrightCounts r hr
  · intro a ha hc hr0 hr1 hh0 hh1 hd
    change μ₄ a = μ a
    rw [hkeep₃ a ⟨ha,hd⟩,hpres₂ a ha (by omega) (by omega) hh1,
      hpres₁ a ha (by omega) (by omega) hh0]
    exact hkeep₀ a ⟨ha,hc⟩

def program : Program :=
  [body 1 6 13,LightWeightDecode.body 2 3,powTableBody,LightWeightRow.body 4,
    LightRadixDigit.body 5,LightSmallDivide.body,LightHashHistogram.body 7 9 11,
    LightMaskHashes.body 2 8,LightOneHot.body 8,LightResidues.residuesBody 10,
    emodBody,LightHistogram.histogramBody 12,fillBody,LightLocalCoverRow.body 14 17,
    LightPairFlags.body 5 15 16,LightBooleanDot.body,LightTrimTest.body,LightSupportMark.body 12]

def programProcs : Procs program 0 :=
  ⟨1,6,13,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨7,2,8,9,10,11,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,
    ⟨14,5,15,16,17,12,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩

end ThreeSum.LightLocalCoverCandidate
