import Submission.ThreeSum.TernaryBankEnumeration
import Submission.ThreeSum.LightTernaryCodes

/-! Canonical compressed addresses realize coordinate digit reads and deletions. -/

namespace ThreeSum.TernaryCodeSemantics

open Finset ThreeSum.TernaryJointType ThreeSum.TernaryAddresses
open ThreeSum.TernaryBankEnumeration ThreeSum.SubsetAddress ThreeSum.MaskErase

set_option maxHeartbeats 2000000

def low {N : ℕ} (i : Fin N) : ℕ := 2*(N-1-i.val)
def high {N : ℕ} (i : Fin N) : ℕ := low i+1
def bitPosition {N : ℕ} (p : Fin N × Fin 2) : ℕ := low p.1+p.2.val
def live {N : ℕ} (w : TritWord N) (p : Fin N × Fin 2) : Prop :=
  if p.2=0 then 0<(w p.1).val else w p.1=2

instance {N : ℕ} (w : TritWord N) (p : Fin N × Fin 2) : Decidable (live w p) := by
  unfold live
  infer_instance

def supportPairs {N : ℕ} (w : TritWord N) : Finset (Fin N × Fin 2) :=
  univ.filter (live w)

def support {N : ℕ} (w : TritWord N) : Finset ℕ :=
  (supportPairs w).image bitPosition

def address {N : ℕ} (w : TritWord N) : ℕ := code (wordList w)

theorem bitPosition_injective (N : ℕ) : Function.Injective (@bitPosition N) := by
  rintro ⟨i,b⟩ ⟨j,c⟩ he
  have hi := i.isLt
  have hj := j.isLt
  have hb := b.isLt
  have hc := c.isLt
  dsimp only [bitPosition,low] at he
  have hi' : i.val=j.val := by omega
  have hb' : b.val=c.val := by omega
  exact Prod.ext (Fin.ext hi') (Fin.ext hb')

theorem bitPosition_lt {N : ℕ} (p : Fin N × Fin 2) : bitPosition p<2*N := by
  have hi := p.1.isLt
  have hb := p.2.isLt
  unfold bitPosition low
  omega

theorem support_subset {N : ℕ} (w : TritWord N) : support w ⊆ range (2*N) := by
  intro a ha
  obtain ⟨p,hp,rfl⟩ := mem_image.mp ha
  exact mem_range.mpr (bitPosition_lt p)

theorem address_eq_sum {N : ℕ} (w : TritWord N) :
    address w=∑ i, digitCode (w i).val*4^(N-1-i.val) := by
  unfold address
  induction N with
  | zero => simp [wordList,code]
  | succ N ih =>
    have hw : wordList w=(w 0).val::wordList (fun i : Fin N => w i.succ) := by
      simp [wordList,List.ofFn_succ]
    rw [hw,code,wordList_length,ih,Fin.sum_univ_succ]
    simp only [Fin.val_zero,Fin.val_succ,Nat.add_sub_cancel,Nat.sub_zero]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    congr 2
    omega

theorem address_eq_maskOf {N : ℕ} (w : TritWord N) : address w=maskOf (support w) := by
  rw [address_eq_sum]
  unfold maskOf support
  rw [Finset.sum_image (fun a ha b hb h => bitPosition_injective N h)]
  unfold supportPairs
  rw [Finset.sum_filter]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.sum_univ_zero,add_zero]
  have hlocal (d : Fin 3) (k : ℕ) :
      digitCode d.val*4^k =
        (if 0<d.val then 2^(2*k) else 0)+(if d=2 then 2^(2*k+1) else 0) := by
    have hpow : 2^(2*k)=4^k := by rw [pow_mul]; norm_num
    fin_cases d <;> norm_num [digitCode,Fin.ext_iff,pow_succ,hpow] <;> omega
  simpa [bitPosition,low,live,Fin.ext_iff] using hlocal (w i) (N-1-i.val)

theorem mem_support_iff {N : ℕ} (w : TritWord N) (p : Fin N × Fin 2) :
    bitPosition p ∈ support w ↔ live w p := by
  constructor
  · intro h
    obtain ⟨q,hq,he⟩ := mem_image.mp h
    have heq : q=p := bitPosition_injective N he
    subst q
    simpa [supportPairs] using hq
  · intro h
    exact mem_image.mpr ⟨p,by simpa [supportPairs] using h,rfl⟩

def clampOne (d : Fin 3) : Fin 3 := if d=0 then 0 else 1

theorem live_update_zero {N : ℕ} (w : TritWord N) (i : Fin N)
    (p : Fin N × Fin 2) :
    live (Function.update w i 0) p ↔ live w p ∧ p≠(i,0) ∧ p≠(i,1) := by
  rcases p with ⟨j,b⟩
  by_cases hj : j=i
  · subst j
    fin_cases b <;> simp [live,Fin.ext_iff]
  · simp [live,Function.update_of_ne hj,hj,Prod.mk.injEq]

theorem live_update_one {N : ℕ} (w : TritWord N) (i : Fin N)
    (p : Fin N × Fin 2) :
    live (Function.update w i (clampOne (w i))) p ↔ live w p ∧ p≠(i,1) := by
  rcases p with ⟨j,b⟩
  by_cases hj : j=i
  · subst j
    generalize hd : w i=d
    fin_cases b <;> fin_cases d <;> simp [live,clampOne,hd,Fin.ext_iff]
  · simp [live,Function.update_of_ne hj,hj,Prod.mk.injEq]

theorem supportPairs_update_zero {N : ℕ} (w : TritWord N) (i : Fin N) :
    supportPairs (Function.update w i 0)=
      ((supportPairs w).erase (i,1)).erase (i,0) := by
  ext p
  simp only [supportPairs,mem_filter,mem_univ,true_and,mem_erase,live_update_zero]
  tauto

theorem supportPairs_update_one {N : ℕ} (w : TritWord N) (i : Fin N) :
    supportPairs (Function.update w i (clampOne (w i)))=(supportPairs w).erase (i,1) := by
  ext p
  simp only [supportPairs,mem_filter,mem_univ,true_and,mem_erase,live_update_one]
  tauto

theorem support_update_zero {N : ℕ} (w : TritWord N) (i : Fin N) :
    support (Function.update w i 0)=((support w).erase (high i)).erase (low i) := by
  unfold support
  rw [supportPairs_update_zero,Finset.image_erase (bitPosition_injective N),
    Finset.image_erase (bitPosition_injective N)]
  simp [bitPosition,high]

theorem support_update_one {N : ℕ} (w : TritWord N) (i : Fin N) :
    support (Function.update w i (clampOne (w i)))=(support w).erase (high i) := by
  unfold support
  rw [supportPairs_update_one,Finset.image_erase (bitPosition_injective N)]
  simp [bitPosition,high]

theorem zeroCode_eq_update {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.zeroCode (2*N) (low i) (high i) (address w) =
      address (Function.update w i 0) := by
  unfold LightTernaryCodes.zeroCode
  rw [address_eq_maskOf,eraseMask_maskOf _ (support_subset w)]
  rw [eraseMask_maskOf _ ((Finset.erase_subset _ _).trans (support_subset w))]
  rw [address_eq_maskOf,support_update_zero]

theorem oneCode_eq_update {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.oneCode (2*N) (high i) (address w) =
      address (Function.update w i (clampOne (w i))) := by
  unfold LightTernaryCodes.oneCode
  rw [address_eq_maskOf,eraseMask_maskOf _ (support_subset w),
    address_eq_maskOf,support_update_one]

theorem bit_maskOf {W : ℕ} (s : Finset ℕ) (hs : s ⊆ range W) (a : ℕ) :
    LightMaskBits.bit W (maskOf s) a=if a∈s then 1 else 0 := by
  unfold LightMaskBits.bit
  rw [eraseMask_maskOf s hs]
  by_cases ha : a∈s
  · have hn : maskOf (s.erase a)≠maskOf s := by
      intro he
      have hsEq := maskOf_injective he
      have hmem : a∈s.erase a := by rw [hsEq]; exact ha
      exact (Finset.notMem_erase a s) hmem
    simp [ha,hn]
  · simp [ha,Finset.erase_eq_of_notMem ha]

theorem low_bit {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightMaskBits.bit (2*N) (address w) (low i)=if 0<(w i).val then 1 else 0 := by
  classical
  rw [address_eq_maskOf,bit_maskOf _ (support_subset w)]
  have hmem : low i∈support w ↔ 0<(w i).val := by
    simpa [bitPosition,live] using mem_support_iff w (i,0)
  by_cases h : 0<(w i).val
  · simp [h,hmem.mpr h]
  · have hn : low i∉support w := fun hh => h (hmem.mp hh)
    simp [h,hn]

theorem high_bit {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightMaskBits.bit (2*N) (address w) (high i)=if w i=2 then 1 else 0 := by
  classical
  rw [address_eq_maskOf,bit_maskOf _ (support_subset w)]
  have hmem : high i∈support w ↔ w i=2 := by
    simpa [bitPosition,live,high] using mem_support_iff w (i,1)
  by_cases h : w i=2
  · simp [h,hmem.mpr h]
  · have hn : high i∉support w := fun hh => h (hmem.mp hh)
    simp [h,hn]

theorem digit_eq {N : ℕ} (w : TritWord N) (i : Fin N) :
    LightTernaryCodes.digit (2*N) (low i) (high i) (address w)=(w i).val := by
  unfold LightTernaryCodes.digit
  rw [low_bit,high_bit]
  generalize hd : w i=d
  fin_cases d <;> norm_num [Fin.ext_iff]

theorem low_lt {N : ℕ} (i : Fin N) : low i<2*N := by
  simpa [bitPosition] using bitPosition_lt (i,0)

theorem high_lt {N : ℕ} (i : Fin N) : high i<2*N := by
  simpa [bitPosition,high] using bitPosition_lt (i,1)

theorem address_lt {N : ℕ} (w : TritWord N) : address w<4^N := by
  simpa [address] using code_lt (wordList w) (wordList_digits w)

theorem address_lt_pow_two {N : ℕ} (w : TritWord N) : address w<2^(2*N) := by
  have hp : 2^(2*N)=4^N := by rw [pow_mul]; norm_num
  simpa [hp] using address_lt w

theorem address_injective (N : ℕ) : Function.Injective (@address N) := by
  intro w v h
  funext i
  apply Fin.ext
  have hh := congrArg (fun m => LightTernaryCodes.digit (2*N) (low i) (high i) m) h
  simpa [digit_eq] using hh

theorem oneCode_eq_update_of_pos {N : ℕ} (w : TritWord N) (i : Fin N)
    (h : 0<(w i).val) :
    LightTernaryCodes.oneCode (2*N) (high i) (address w)=
      address (Function.update w i 1) := by
  have hn : w i≠0 := by intro hz; rw [hz] at h; contradiction
  simpa [clampOne,hn] using oneCode_eq_update w i

def lowerCode {N : ℕ} (w : TritWord N) (i : Fin N) (d : Fin 3) : ℕ :=
  if d=0 then LightTernaryCodes.zeroCode (2*N) (low i) (high i) (address w)
  else if d=1 then LightTernaryCodes.oneCode (2*N) (high i) (address w)
  else address w

/-- Every metadata code actually read by a coordinate stage is the true lower word. -/
theorem lowerCode_eq_update {N : ℕ} (w : TritWord N) (i : Fin N) (d : Fin 3)
    (hd : d≤w i) : lowerCode w i d=address (Function.update w i d) := by
  fin_cases d
  · simpa [lowerCode] using zeroCode_eq_update w i
  · have hp : 0<(w i).val := by have := (show (1 : Fin 3).val≤(w i).val from hd); norm_num at this; omega
    simpa [lowerCode,Fin.ext_iff] using oneCode_eq_update_of_pos w i hp
  · have hw : w i=2 := by
      apply Fin.ext
      have ht := (w i).isLt
      have hle : (2 : Fin 3).val≤(w i).val := hd
      norm_num at hle ⊢
      omega
    have hu : Function.update w i (2 : Fin 3)=w := by
      funext j
      by_cases hj : j=i
      · subst j
        simp [hw]
      · simp [Function.update_of_ne hj]
    simp [lowerCode,Fin.ext_iff,hu]

end ThreeSum.TernaryCodeSemantics
