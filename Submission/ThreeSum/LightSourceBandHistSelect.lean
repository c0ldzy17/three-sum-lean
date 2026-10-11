import Submission.ThreeSum.SourceBandPairSlices

/-! # Actual constant-time retained histogram selection with empty padding -/

namespace ThreeSum.LightSourceBandHistSelect

open Light BandPartition SourceBandPairData SourceBandPairSlices

set_option maxHeartbeats 2500000
set_option maxRecDepth 12000

def finishBody : Stmt := .store (v 2) (v 3) ;; .store (v 2 +' k 1) (v 4)

def rightBody : Stmt :=
  .ite (v 1 <' M (v 0 +' k 3))
    (.set 4 (M (M (v 0 +' k 2) +' k 6 *' v 1 +' k 3))) .skip ;;
  finishBody

/-- The pair-catalog header, common band index, and two temporary cells. -/
def body : Stmt :=
  .set 3 (M (v 0 +' k 4)) ;;
  .set 4 (M (v 0 +' k 4)) ;;
  .ite (v 1 <' M (v 0 +' k 1))
    (.set 3 (M (M (v 0) +' k 6 *' v 1 +' k 3))) .skip ;;
  rightBody

variable {lim : Limits} {P : Program} {d : ℕ}

theorem finish_ends {μ : ℕ → ℤ} {pair i dst left right : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : dst+2 ≤ lim.space)
    (hl : left ≤ lim.space) (hr : right ≤ lim.space) :
    Ends lim P d finishBody ⟨frame [pair,i,dst,left,right],μ⟩ 40
      (fun σ => σ.mem dst=(left : ℤ) ∧ σ.mem (dst+1)=(right : ℤ) ∧ Kept μ σ.mem dst) := by
  unfold finishBody
  light_store dst (left : ℕ)
  light_store (dst+1) (right : ℕ)
  dsimp only
  refine ⟨?_,?_,?_⟩
  · rw [Function.update_of_ne (by omega),Function.update_self]
  · exact Function.update_self _ _ _
  · intro a ha
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]

theorem right_ends {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p m i dst left : ℕ} {shift : ℤ}
    (H : Stored μ fL fR pair NL NR g p m shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < m)
    (hb : next pair NL NR g m ≤ dst) (hs : dst+2 ≤ lim.space)
    (hwN : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word) (hl : left ≤ lim.space) :
    Ends lim P d rightBody
      ⟨frame [pair,i,dst,left,zeroBase pair NL NR g m],μ⟩ 200
      (fun σ => σ.mem dst=(left : ℤ) ∧
        σ.mem (dst+1)=(histRight pair NL NR g m i : ℤ) ∧ Kept μ σ.mem dst) := by
  obtain ⟨hbaseL,hcountL,hbaseR,hcountR,hzero,_⟩ := heads_read H
  have ho := ordered pair NL NR g m
  have hcounts := size_le NR g
  have hcountWord : (size NR g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show size NR g ≤ NL+NR+i+6 by omega)).trans hwN
  have hindexWord : (i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : i ≤ NL+NR+i+6)).trans hwN
  have h6 : (6 : ℤ) ≤ lim.word := by omega
  have hheadBound : pair+8 ≤ dst := by unfold leftBase at ho; omega
  have hzeroBound : zeroBase pair NL NR g m ≤ lim.space := by omega
  have htarget := right_end pair NL NR g m i
  have haddr2 : ((pair : ℤ)+2).toNat=pair+2 := by omega
  have haddr3 : ((pair : ℤ)+3).toNat=pair+3 := by omega
  unfold rightBody
  light_if hy hn : (i : ℤ) < (size NR g : ℤ) using hcountR,haddr3
  · have hi : i < size NR g := by omega
    have hhead := SourceBandLayout.header_end (base := rightBase pair NL g m) (m := m) hi
    have hend := SourceBandLayout.flat_end_le_work (base := rightBase pair NL g m) (m := m) hi
    change SourceBandLayout.flat (rightBase pair NL g m) NR g m i+SourceBandLayout.cap NR g ≤
      zeroBase pair NL NR g m at hend
    unfold SourceBandLayout.flat SourceBandLayout.cursor SourceBandLayout.offsets SourceBandLayout.codes at hend
    have haddr : ((rightBase pair NL g m : ℤ)+6*(i : ℤ)+3).toNat=rightBase pair NL g m+6*i+3 := by omega
    have haddrWord : (rightBase pair NL g m : ℤ)+6*(i : ℤ)+3 < lim.space := by exact_mod_cast (by omega : rightBase pair NL g m+6*i+3 < lim.space)
    have hprod : (6 : ℤ)*(i : ℤ) ≤ lim.word := by omega
    have hread := (H.right i hi).headHist
    have he : histRight pair NL NR g m i=SourceBandLayout.hist (rightBase pair NL g m) NR g m i := by
      simp only [histRight,histogramPtr,if_pos hi]
    light_set (SourceBandLayout.hist (rightBase pair NL g m) NR g m i : ℕ) using hbaseR,haddr2,haddr,hread
    rw [he]
    light_piece (finish_ends hw hs hl (by omega))
  · have hi : ¬ i < size NR g := by omega
    have he : histRight pair NL NR g m i=zeroBase pair NL NR g m := by
      simp only [histRight,histogramPtr,if_neg hi]
    rw [he]
    light_piece (finish_ends hw hs hl hzeroBound)

theorem meets {pMain : ℕ} (hmain : P[pMain]?=some body)
    {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {pair NL NR g p m i dst : ℕ} {shift : ℤ}
    (H : Stored μ fL fR pair NL NR g p m shift)
    (hw : (lim.space : ℤ) ≤ lim.word) (hm : 0 < m)
    (hb : next pair NL NR g m ≤ dst) (hs : dst+2 ≤ lim.space)
    (hwN : ((NL+NR+i+6 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [pair,i,dst] μ 400
      (fun _ ν => ν dst=(histLeft pair NL NR g m i : ℤ) ∧
        ν (dst+1)=(histRight pair NL NR g m i : ℤ) ∧ Kept μ ν dst) := by
  obtain ⟨hbaseL,hcountL,hbaseR,hcountR,hzero,_⟩ := heads_read H
  have ho := ordered pair NL NR g m
  have hcounts := size_le NL g
  have hcountWord : (size NL g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show size NL g ≤ NL+NR+i+6 by omega)).trans hwN
  have hindexWord : (i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : i ≤ NL+NR+i+6)).trans hwN
  have h6 : (6 : ℤ) ≤ lim.word := by omega
  have hheadBound : pair+8 ≤ dst := by unfold leftBase at ho; omega
  have hzeroBound : zeroBase pair NL NR g m ≤ lim.space := by omega
  have htarget := left_end pair NL NR g m i
  have haddr1 : ((pair : ℤ)+1).toNat=pair+1 := by omega
  have haddr4 : ((pair : ℤ)+4).toNat=pair+4 := by omega
  apply Meets.of_body hmain
  unfold body
  light_set (zeroBase pair NL NR g m : ℕ) using hzero,haddr4
  light_set (zeroBase pair NL NR g m : ℕ) using hzero,haddr4
  light_if hy hn : (i : ℤ) < (size NL g : ℤ) using hcountL,haddr1
  · have hi : i < size NL g := by omega
    have hhead := SourceBandLayout.header_end (base := leftBase pair) (m := m) hi
    have hend := SourceBandLayout.flat_end_le_work (base := leftBase pair) (m := m) hi
    change SourceBandLayout.flat (leftBase pair) NL g m i+SourceBandLayout.cap NL g ≤
      rightBase pair NL g m at hend
    unfold SourceBandLayout.flat SourceBandLayout.cursor SourceBandLayout.offsets SourceBandLayout.codes at hend
    have haddr : ((leftBase pair : ℤ)+6*(i : ℤ)+3).toNat=leftBase pair+6*i+3 := by omega
    have haddrWord : (leftBase pair : ℤ)+6*(i : ℤ)+3 < lim.space := by exact_mod_cast (by omega : leftBase pair+6*i+3 < lim.space)
    have hprod : (6 : ℤ)*(i : ℤ) ≤ lim.word := by omega
    have hread := (H.left i hi).headHist
    have he : histLeft pair NL NR g m i=SourceBandLayout.hist (leftBase pair) NL g m i := by
      simp only [histLeft,histogramPtr,if_pos hi]
    light_set (SourceBandLayout.hist (leftBase pair) NL g m i : ℕ) using hbaseL,haddr,hread
    rw [he]
    light_piece (right_ends H hw hm hb hs hwN (by omega))
  · have hi : ¬ i < size NL g := by omega
    have he : histLeft pair NL NR g m i=zeroBase pair NL NR g m := by
      simp only [histLeft,histogramPtr,if_neg hi]
    rw [he]
    light_piece (right_ends H hw hm hb hs hwN hzeroBound)

def program : Program := [body]

end ThreeSum.LightSourceBandHistSelect
