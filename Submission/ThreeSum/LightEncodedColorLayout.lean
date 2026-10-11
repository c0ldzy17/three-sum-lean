import Submission.ThreeSum.EncodedColorLayout

/-! # Compute and retain the selected-color array layout -/

namespace ThreeSum.LightEncodedColorLayout

open Light BandPartition EncodedColorLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 11000

def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 0 -' k 1,v 1] 3 ;;
  .set 4 (v 3 +' k 1) ;;
  .set 5 (k 3 *' v 4 *' v 4) ;;
  .set 6 (v 2 +' k 8) ;;
  .set 7 (v 6 +' v 0) ;;
  .set 8 (v 7 +' v 0 +' k 1) ;;
  .set 9 (v 8 +' v 0 +' k 1) ;;
  .set 10 (v 9 +' v 0 +' k 1) ;;
  .set 11 (v 10 +' v 0) ;;
  .set 12 (v 11 +' k 2 +' k 2 *' v 0) ;;
  .set 13 (v 12 +' v 0) ;;
  .set 14 (v 13 +' k 2 +' k 2 *' v 0) ;;
  .set 15 (v 14 +' v 0) ;;
  .set 16 (v 15 +' k 2 +' k 2 *' v 0) ;;
  .set 17 (v 16 +' v 5) ;;
  .set 18 (v 17 +' k 4 *' v 5) ;;
  .set 19 (v 18 +' k 3 *' v 1 *' v 5) ;;
  .store (v 2) (v 10) ;;
  .store (v 2 +' k 1) (v 11) ;;
  .store (v 2 +' k 2) (v 12) ;;
  .store (v 2 +' k 3) (v 13) ;;
  .store (v 2 +' k 4) (v 14) ;;
  .store (v 2 +' k 5) (v 15) ;;
  .store (v 2 +' k 6) (v 17) ;;
  .store (v 2 +' k 7) (v 18) ;;
  .set 0 (v 19)

def time (n g : ℕ) : ℕ := LightSmallDivide.time (n-1) g+1000
def word (n g : ℕ) : ℕ := n+g+ColorBandBounds.count n g+100

def headMemory (μ : ℕ → ℤ) (free n g : ℕ) : ℕ → ℤ :=
  Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update μ free (av free n))
      (free+1) (ae free n)) (free+2) (bv free n)) (free+3) (be free n))
      (free+4) (cv free n)) (free+5) (ce free n)) (free+6) (rec free n g)) (free+7) (vals free n g)

theorem headMemory_kept (μ : ℕ → ℤ) (free n g : ℕ) : Kept μ (headMemory μ free n g) free := by
  intro q hq
  unfold headMemory
  repeat rw [Function.update_of_ne (by omega)]

theorem headMemory_heads (μ : ℕ → ℤ) (free n g : ℕ) :
    Seg (headMemory μ free n g) free (normalizedHeads free n g) := by
  intro i hi
  have hi' : i < 8 := by simpa [normalizedHeads] using hi
  interval_cases i <;> simp [headMemory,normalizedHeads]

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pDivide n g free : ℕ} {μ : ℕ → ℤ}
    (hmain : P[pMain]?=some (body pDivide)) (hdiv : P[pDivide]?=some LightSmallDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hg : 0 < g)
    (hspace : normalizedEnd free n g+1 ≤ lim.space)
    (hword : (word n g : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P pMain d [n,g,free] μ (time n g)
      (fun r ν => r=(normalizedEnd free n g : ℤ) ∧ Seg ν free (normalizedHeads free n g) ∧ Kept μ ν free) := by
  have hfull : free+17+13*n+5*ColorBandBounds.count n g+3*g*ColorBandBounds.count n g+1 ≤ lim.space := by
    convert hspace using 1 <;>
      simp only [normalizedEnd,LightBandRawA.space,LightBandRawA.positionBase,LightBandRawA.ownerBase,
        LightBandRawA.capacity,vals,rec,tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors] <;> ring
  have hfullZ : (free : ℤ)+17+13*(n : ℤ)+5*(ColorBandBounds.count n g : ℤ)+
      3*(g : ℤ)*(ColorBandBounds.count n g : ℤ)+1 ≤ lim.word := by
    exact (by exact_mod_cast hfull : _ ≤ (lim.space : ℤ)).trans hw
  have hdivWord : ((n-1+g+2 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hR : (ColorBandBounds.count n g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hbandsPos : 0 < size n g := by
    simp only [size,if_neg (by omega : n ≠ 0)]
    exact Nat.zero_lt_succ _
  have hRPos : 0 < ColorBandBounds.count n g := by unfold ColorBandBounds.count; positivity
  have hthree : 3*size n g ≤ ColorBandBounds.count n g := by
    have hh := Nat.le_mul_of_pos_right (size n g) hbandsPos
    unfold ColorBandBounds.count
    nlinarith
  have hthreeZ : 3*(size n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast hthree : _ ≤ (ColorBandBounds.count n g : ℤ)).trans hR
  have hsizeEq : (n-1)/g+1=size n g := by simp only [size,if_neg (by omega : n ≠ 0)]
  have hRZ : 3*(size n g : ℤ)*(size n g : ℤ)=(ColorBandBounds.count n g : ℤ) := by
    simp only [ColorBandBounds.count,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_pow,pow_two]
    ring
  have hprod : 3*g*ColorBandBounds.count n g ≤ lim.space := by omega
  have h3g : 3*g ≤ lim.space := (Nat.le_mul_of_pos_right (3*g) hRPos).trans hprod
  have h3gZ : 3*(g : ℤ) ≤ lim.word := (by exact_mod_cast h3g : _ ≤ (lim.space : ℤ)).trans hw
  have hprodZ : 3*(g : ℤ)*(ColorBandBounds.count n g : ℤ) ≤ lim.word :=
    (by exact_mod_cast hprod : _ ≤ (lim.space : ℤ)).trans hw
  have hp0 : (0 : ℤ) ≤ 3*(g : ℤ)*(ColorBandBounds.count n g : ℤ) := by positivity
  have hvalsZ : (vals free n g : ℤ)=(free : ℤ)+17+13*(n : ℤ)+5*(ColorBandBounds.count n g : ℤ) := by
    simp only [vals,rec,tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hEndEq : (vals free n g : ℤ)+3*(g : ℤ)*(ColorBandBounds.count n g : ℤ)=
      (normalizedEnd free n g : ℤ) := by
    simp only [normalizedEnd,LightBandRawA.space,LightBandRawA.positionBase,LightBandRawA.ownerBase,
      LightBandRawA.capacity,Nat.cast_add,Nat.cast_mul]
    ring
  apply Meets.of_body hmain
  unfold body time
  light_call (LightSmallDivide.meets (d := d+1) hdiv μ hdivWord) with q μ₀ ⟨hq,hmem⟩
  subst μ₀
  light_set (size n g : ℕ) using hq,hsizeEq
  light_set (ColorBandBounds.count n g : ℕ) using hRZ
  light_set (colors free : ℕ) using colors
  light_set (class0 free n : ℕ) using class0,colors
  light_set (class1 free n : ℕ) using class1,class0,colors
  light_set (class2 free n : ℕ) using class2,class1,class0,colors
  light_set (av free n : ℕ) using av,class2,class1,class0,colors
  light_set (ae free n : ℕ) using ae,av,class2,class1,class0,colors
  light_set (bv free n : ℕ) using bv,ae,av,class2,class1,class0,colors
  light_set (be free n : ℕ) using be,bv,ae,av,class2,class1,class0,colors
  light_set (cv free n : ℕ) using cv,be,bv,ae,av,class2,class1,class0,colors
  light_set (ce free n : ℕ) using ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_set (tables free n : ℕ) using tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_set (rec free n g : ℕ) using rec,tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_set (vals free n g : ℕ) using vals,rec,tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_set (normalizedEnd free n g : ℕ) using hEndEq,vals,rec,tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_store free (av free n : ℕ) using av,class2,class1,class0,colors
  light_store (free+1) (ae free n : ℕ) using ae,av,class2,class1,class0,colors
  light_store (free+2) (bv free n : ℕ) using bv,ae,av,class2,class1,class0,colors
  light_store (free+3) (be free n : ℕ) using be,bv,ae,av,class2,class1,class0,colors
  light_store (free+4) (cv free n : ℕ) using cv,be,bv,ae,av,class2,class1,class0,colors
  light_store (free+5) (ce free n : ℕ) using ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_store (free+6) (rec free n g : ℕ) using rec,tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_store (free+7) (vals free n g : ℕ) using vals,rec,tables,ce,cv,be,bv,ae,av,class2,class1,class0,colors
  light_set (normalizedEnd free n g : ℕ)
  exact ⟨rfl,headMemory_heads μ free n g,headMemory_kept μ free n g⟩

def program : Program := [body 1,LightSmallDivide.body]

theorem program_length : program.length=2 := rfl

theorem program_meets {n g free : ℕ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n) (hg : 0 < g)
    (hspace : normalizedEnd free n g+1 ≤ lim.space)
    (hword : (word n g : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [n,g,free] μ (time n g)
      (fun r ν => r=(normalizedEnd free n g : ℤ) ∧ Seg ν free (normalizedHeads free n g) ∧ Kept μ ν free) :=
  meets rfl rfl hw hn hg hspace hword hd

end ThreeSum.LightEncodedColorLayout
