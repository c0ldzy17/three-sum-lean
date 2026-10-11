import Submission.ThreeSum.LightBooleanDot
import Submission.ThreeSum.LightSmallDivide
import Submission.ThreeSum.LightTrimTest

/-!
# Constructing every candidate pair's key and trimming flag

All pairs of enumerated local vertices are visited. A zero coordinate-row
inner product tests disjointness; the two actual bucket counts determine
whether the pair survives. The local exhaustive scan is intentionally
unoptimized and its entire arithmetic and lookup cost is charged.
-/

namespace ThreeSum.LightPairFlags

open Light

set_option maxHeartbeats 1500000
set_option maxRecDepth 5000

def pairKey (n p : ℕ) (left right : ℕ → ℕ) (i : ℕ) : ℕ :=
  left (i/n)*p+right (i%n)

def pairFlag (L n cap : ℕ) (bits : ℕ → ℕ → ℕ)
    (left right leftCount rightCount : ℕ → ℕ) (i : ℕ) : ℕ :=
  LightTrimTest.flag (LightBooleanDot.dot (bits (i/n)) (bits (i%n)) L)
    (leftCount (left (i/n))) (rightCount (right (i%n))) cap

def roundBody (pDivide pDot pTrim : ℕ) : Stmt :=
  .call pDivide [v 11,v 6] 12 ;;
  .set 13 (v 11 -' v 12 *' v 6) ;;
  .call pDot [v 0 +' v 12 *' v 7,v 0 +' v 13 *' v 7,v 7] 14 ;;
  .set 15 (M (v 1 +' v 12)) ;;
  .set 16 (M (v 2 +' v 13)) ;;
  .call pTrim [v 14,M (v 3 +' v 15),M (v 4 +' v 16),v 9] 17 ;;
  .store (v 5 +' v 11) (v 15 *' v 8 +' v 16) ;;
  .store (v 10 +' v 11) (v 17)

def body (pDivide pDot pTrim : ℕ) : Stmt :=
  .set 10 (v 5 +' v 6 *' v 6) ;;
  .for 11 (v 6 *' v 6) (roundBody pDivide pDot pTrim)

def roundTime (L n : ℕ) : ℕ := 20*n+LightBooleanDot.time L+LightTrimTest.time+350
def time (L n : ℕ) : ℕ := n*n*(roundTime L n+12)+30
def word (L n p cap : ℕ) : ℕ := 100*(n*n+p*p+cap+L+n+p+1)

def Inv (μ : ℕ → ℤ) (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap i : ℕ) (σ : State) : Prop :=
  ∃ (a b c e f g : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap,dst+n*n,i,a,b,c,e,f,g],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (pairKey n p left right j : ℤ)) ∧
    (∀ j < i, μ' (dst+n*n+j) = (pairFlag L n cap bits left right leftCount rightCount j : ℤ)) ∧
    SameOutside μ μ' dst (2*(n*n))

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pDivide pDot pTrim : ℕ}
    (hmain : P[pMain]? = some (body pDivide pDot pTrim))
    (hdivide : P[pDivide]? = some LightSmallDivide.body)
    (hdot : P[pDot]? = some LightBooleanDot.body)
    (htrim : P[pTrim]? = some LightTrimTest.body)
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ dst) (hleft : leftPtr+n ≤ dst) (hright : rightPtr+n ≤ dst)
    (hleftHist : leftHist+p ≤ dst) (hrightHist : rightHist+p ≤ dst)
    (hspace : dst+2*(n*n) ≤ lim.space) (hword : (word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim P pMain d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap] μ (time L n)
      (fun _ μ' =>
        (∀ i < n*n, μ' (dst+i) = (pairKey n p left right i : ℤ)) ∧
        (∀ i < n*n, μ' (dst+n*n+i) = (pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
        SameOutside μ μ' dst (2*(n*n))) := by
  have hbudget (x : ℕ) (hx : x ≤ word L n p cap) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hnWord := hbudget n (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hcapWord := hbudget cap (by unfold word; omega)
  have hLWord := hbudget L (by unfold word; omega)
  have heWord := hbudget (n*n) (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  have heWordZ : (n : ℤ)*(n : ℤ) ≤ lim.word := by exact_mod_cast heWord
  apply Meets.of_body hmain
  unfold body time
  light_set (dst+n*n : ℕ) using roundTime,word
  refine Ends.for (Inv μ bits left right leftCount rightCount
    bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap) (n*n) (roundTime L n) ?_ ?_ ?_ ?_
    (hT := by light_time [roundTime,LightBooleanDot.time,LightTrimTest.time])
  · refine ⟨0,0,0,0,0,0,μ,?_,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 6).symm)
    · intro j hj; omega
    · intro j hj; omega
  · rintro i _ hi _ ⟨a,b,c,e,f,g,μ',rfl,writtenKeys,writtenFlags,kept⟩
    have hq : i/n < n := (Nat.div_lt_iff_lt_mul hn).mpr hi
    have hr : i%n < n := Nat.mod_lt i hn
    have hqmul : i/n*n ≤ i := Nat.div_mul_le_self i n
    have hqr : i%n+i/n*n = i := by simpa only [Nat.mul_comm] using Nat.mod_add_div i n
    have hdivWord : ((i+n+2 : ℕ) : ℤ) ≤ lim.word :=
      hbudget _ (by unfold word; omega)
    have hdivTime : LightSmallDivide.time i n ≤ 20*n+40 := by unfold LightSmallDivide.time; omega
    have hqWord := hbudget (i/n) (by unfold word; omega)
    have hrWord := hbudget (i%n) (by unfold word; omega)
    have hqNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ) := by
      rw [← Int.natCast_ediv]
      exact Int.natCast_nonneg _
    have hrem : (i : ℤ)-((i/n : ℕ) : ℤ)*n = ((i%n : ℕ) : ℤ) := by exact_mod_cast (by omega : i-i/n*n=i%n)
    have hqmulZ : ((i/n : ℕ) : ℤ)*(n : ℤ) ≤ lim.word := by
      have hh : i/n*n ≤ word L n p cap := by unfold word; omega
      exact (by exact_mod_cast hh : ((i/n : ℕ) : ℤ)*(n : ℤ) ≤ (word L n p cap : ℤ)).trans hword
    have hqmulInt : (i : ℤ)/(n : ℤ)*n ≤ lim.word := by
      simpa only [Int.natCast_ediv] using hqmulZ
    have hqmulNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ)*n := by
      rw [← Int.natCast_ediv,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hremInt : (i : ℤ)-(i : ℤ)/(n : ℤ)*n = ((i%n : ℕ) : ℤ) := by
      simpa only [Int.natCast_ediv] using hrem
    unfold roundBody
    light_call (LightSmallDivide.meets (d := d+1) (a := i) (b := n) hdivide μ' hdivWord)
      using roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
      with qval μ₁ ⟨hqval,hmem₁⟩
    subst μ₁
    subst qval
    light_set (i%n : ℕ) using hremInt,roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
    have hqL : (i/n+1)*L ≤ n*L := Nat.mul_le_mul_right L (by omega)
    have hrL : (i%n+1)*L ≤ n*L := Nat.mul_le_mul_right L (by omega)
    have hqRow : bitPtr+i/n*L+L ≤ dst := by nlinarith
    have hrRow : bitPtr+i%n*L+L ≤ dst := by nlinarith
    have hqRead : ∀ j < L, μ' (bitPtr+i/n*L+j) = (bits (i/n) j : ℤ) := by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hq j hj
    have hrRead : ∀ j < L, μ' (bitPtr+i%n*L+j) = (bits (i%n) j : ℤ) := by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hbitsRead _ hr j hj
    have hqLMulWord : (((i/n)*L : ℕ) : ℤ) ≤ lim.word := by
      have hh : (i/n)*L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hrLMulWord : (((i%n)*L : ℕ) : ℤ) ≤ lim.word := by
      have hh : (i%n)*L ≤ lim.space := by omega
      exact (Int.ofNat_le.mpr hh).trans hw
    have hqLInt : (i : ℤ)/(n : ℤ)*L ≤ lim.word := by
      simpa only [Nat.cast_mul,Int.natCast_ediv] using hqLMulWord
    have hqLNonneg : (0 : ℤ) ≤ (i : ℤ)/(n : ℤ)*L := by
      rw [← Int.natCast_ediv,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hrLInt : (i : ℤ)%(n : ℤ)*L ≤ lim.word := by
      simpa only [Nat.cast_mul,Int.natCast_emod] using hrLMulWord
    have hrLNonneg : (0 : ℤ) ≤ (i : ℤ)%(n : ℤ)*L := by
      rw [← Int.natCast_emod,← Nat.cast_mul]
      exact Int.natCast_nonneg _
    have hqa : ((bitPtr : ℤ)+((i/n : ℕ) : ℤ)*L).toNat = bitPtr+i/n*L := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hra : ((bitPtr : ℤ)+((i%n : ℕ) : ℤ)*L).toNat = bitPtr+i%n*L := by
      rw [← Nat.cast_mul,← Nat.cast_add,Int.toNat_natCast]
    have hqaInt : ((bitPtr : ℤ)+(i : ℤ)/(n : ℤ)*L).toNat = bitPtr+i/n*L := by
      simpa only [Int.natCast_ediv] using hqa
    have hraInt : ((bitPtr : ℤ)+(i : ℤ)%(n : ℤ)*L).toNat = bitPtr+i%n*L := by
      simpa only [Int.natCast_emod] using hra
    have hqaBound : (bitPtr : ℤ)+(i : ℤ)/(n : ℤ)*L ≤ lim.word := by
      have hh : ((bitPtr+i/n*L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr+i/n*L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add,Nat.cast_mul,Int.natCast_ediv] using hh
    have hraBound : (bitPtr : ℤ)+(i : ℤ)%(n : ℤ)*L ≤ lim.word := by
      have hh : ((bitPtr+i%n*L : ℕ) : ℤ) ≤ lim.word := by
        exact (Int.ofNat_le.mpr (by omega : bitPtr+i%n*L ≤ lim.space)).trans hw
      simpa only [Nat.cast_add,Nat.cast_mul,Int.natCast_emod] using hh
    have hdotCall := LightBooleanDot.meets (d := d+1) (μ := μ')
      (srcA := bitPtr+i/n*L) (srcB := bitPtr+i%n*L) (n := L)
      hdot (bits (i/n)) (bits (i%n)) hw (by omega) (by omega) hqRead hrRead
      (hbitsValue _ hq) (hbitsValue _ hr) h1Word
    light_call hdotCall using hqa,hra,hqaInt,hraInt,roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
      with overlap μ₂ ⟨hoverlap,hmem₂⟩
    subst μ₂
    have hlr : μ' (leftPtr+i/n) = (left (i/n) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hleftRead _ hq)
    have hrr : μ' (rightPtr+i%n) = (right (i%n) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hrightRead _ hr)
    have hlLt := hleftLt _ hq
    have hrLt := hrightLt _ hr
    have hlAddr : ((leftPtr : ℤ)+(i : ℤ)/(n : ℤ)).toNat = leftPtr+i/n := by
      rw [← Int.natCast_ediv,← Nat.cast_add,Int.toNat_natCast]
    have hrAddr : ((rightPtr : ℤ)+(i : ℤ)%(n : ℤ)).toNat = rightPtr+i%n := by
      rw [← Int.natCast_emod,← Nat.cast_add,Int.toNat_natCast]
    light_set (left (i/n) : ℕ) using hlAddr,hlr,roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
    light_set (right (i%n) : ℕ) using hrAddr,hrr,roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
    have hlc : μ' (leftHist+left (i/n)) = (leftCount (left (i/n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hleftCount _ hlLt)
    have hrc : μ' (rightHist+right (i%n)) = (rightCount (right (i%n)) : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hrightCount _ hrLt)
    have hcL := hleftBound _ hlLt
    have hcR := hrightBound _ hrLt
    have ht := LightTrimTest.meets (d := d+1)
      (x := LightBooleanDot.dot (bits (i/n)) (bits (i%n)) L)
      (l := leftCount (left (i/n))) (r := rightCount (right (i%n))) (b := cap)
      htrim μ' h1Word (hbudget _ (by unfold word; omega))
    light_call ht using hoverlap,hlc,hrc,roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
      with flag μ₃ ⟨hflag,hmem₃⟩
    subst μ₃
    have hk : pairKey n p left right i < p*p := by
      unfold pairKey
      nlinarith
    have hkWord := hbudget (pairKey n p left right i) (by unfold word; omega)
    have hkWordZ : (left (i/n) : ℤ)*p+right (i%n) ≤ lim.word := by
      simpa only [pairKey,Nat.cast_add,Nat.cast_mul] using hkWord
    have hprodWord : ((left (i/n)*p : ℕ) : ℤ) ≤ lim.word := by
      have hh : left (i/n)*p ≤ word L n p cap := by unfold pairKey at hk; unfold word; omega
      exact (Int.ofNat_le.mpr hh).trans hword
    have hflag' : flag = (pairFlag L n cap bits left right leftCount rightCount i : ℤ) := hflag
    have hf : pairFlag L n cap bits left right leftCount rightCount i ≤ 1 := LightTrimTest.flag_le ..
    have hfZ : (pairFlag L n cap bits left right leftCount rightCount i : ℤ) ≤ lim.word := by omega
    light_store (dst+i) (pairKey n p left right i : ℕ)
      using pairKey,roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
    light_store (dst+n*n+i) (pairFlag L n cap bits left right leftCount rightCount i : ℕ)
      using hflag',roundTime,LightBooleanDot.time,LightTrimTest.time,LightSmallDivide.time
    refine ⟨by simp,(i/n : ℕ),i%n,overlap,left (i/n),right (i%n),flag,
      Function.update (Function.update μ' (dst+i) (pairKey n p left right i : ℤ))
        (dst+n*n+i) (pairFlag L n cap bits left right leftCount rightCount i : ℤ),
      by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact writtenKeys j hj
      · rw [Function.update_of_ne (by omega),Function.update_self]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact writtenFlags j hj
      · rw [Function.update_self]
    · exact (kept.update ⟨by omega,by omega⟩ _).update ⟨by omega,by omega⟩ _
  · rintro _ _ ⟨a,b,c,e,f,g,μ',rfl,writtenKeys,writtenFlags,kept⟩
    exact ⟨writtenKeys,writtenFlags,kept⟩
  · rintro i _ _ _ ⟨a,b,c,e,f,g,μ',rfl,_,_,_⟩
    light_side

def program : Program := [body 1 2 3,LightSmallDivide.body,LightBooleanDot.body,LightTrimTest.body]

theorem program_meets
    {μ : ℕ → ℤ} {bitPtr leftPtr rightPtr leftHist rightHist dst n L p cap : ℕ}
    (bits : ℕ → ℕ → ℕ) (left right leftCount rightCount : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hbits : bitPtr+n*L ≤ dst) (hleft : leftPtr+n ≤ dst) (hright : rightPtr+n ≤ dst)
    (hleftHist : leftHist+p ≤ dst) (hrightHist : rightHist+p ≤ dst)
    (hspace : dst+2*(n*n) ≤ lim.space) (hword : (word L n p cap : ℤ) ≤ lim.word)
    (hbitsRead : ∀ i < n, ∀ j < L, μ (bitPtr+i*L+j) = (bits i j : ℤ))
    (hbitsValue : ∀ i < n, ∀ j < L, bits i j ≤ 1)
    (hleftRead : ∀ i < n, μ (leftPtr+i) = (left i : ℤ))
    (hrightRead : ∀ i < n, μ (rightPtr+i) = (right i : ℤ))
    (hleftLt : ∀ i < n, left i < p) (hrightLt : ∀ i < n, right i < p)
    (hleftCount : ∀ r < p, μ (leftHist+r) = (leftCount r : ℤ))
    (hrightCount : ∀ r < p, μ (rightHist+r) = (rightCount r : ℤ))
    (hleftBound : ∀ r < p, leftCount r ≤ n) (hrightBound : ∀ r < p, rightCount r ≤ n) :
    Meets lim program 0 d [bitPtr,leftPtr,rightPtr,leftHist,rightHist,dst,n,L,p,cap] μ (time L n)
      (fun _ μ' =>
        (∀ i < n*n, μ' (dst+i) = (pairKey n p left right i : ℤ)) ∧
        (∀ i < n*n, μ' (dst+n*n+i) = (pairFlag L n cap bits left right leftCount rightCount i : ℤ)) ∧
        SameOutside μ μ' dst (2*(n*n))) :=
  meets rfl rfl rfl rfl bits left right leftCount rightCount hw hd hn hp
    hbits hleft hright hleftHist hrightHist hspace hword hbitsRead hbitsValue
    hleftRead hrightRead hleftLt hrightLt hleftCount hrightCount hleftBound hrightBound

theorem time_bound (L n : ℕ) : time L n ≤ 500*(n*n)*(L+n+1)+30 := by
  have hround : roundTime L n+12 ≤ 500*(L+n+1) := by
    unfold roundTime LightBooleanDot.time LightTrimTest.time
    omega
  have hmul := Nat.mul_le_mul_left (n*n) hround
  unfold time
  nlinarith

end ThreeSum.LightPairFlags
