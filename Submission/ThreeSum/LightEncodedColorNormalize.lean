import Submission.ThreeSum.EncodedColorNormalizedData
import Submission.ThreeSum.LightEncodedColorLayout
import Submission.ThreeSum.LightColorParametersCosts

/-! # Selected-color normalization from actual parameter and color rows -/

namespace ThreeSum.LightEncodedColorNormalize

open Light Scales BandScales ColorClassLists EncodedColorLayout EncodedColorNormalizedData

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000

/-- src,n,parameter header,color row,first free address. -/
def body (pLayout pColor : ℕ) : Stmt :=
  .set 5 (M (v 2) +' k 1) ;;
  .set 6 (M (v 2 +' k 17)) ;;
  .call pLayout [v 1,v 6,v 4] 7 ;;
  .set 8 (v 4 +' k 8) ;;
  .set 9 (v 8 +' v 1) ;;
  .set 10 (v 9 +' v 1 +' k 1) ;;
  .set 11 (v 10 +' v 1 +' k 1) ;;
  .set 12 (M (v 4)) ;;
  .set 13 (M (v 4 +' k 1)) ;;
  .set 14 (M (v 4 +' k 2)) ;;
  .set 15 (M (v 4 +' k 3)) ;;
  .set 16 (M (v 4 +' k 4)) ;;
  .set 17 (M (v 4 +' k 5)) ;;
  .set 18 (M (v 4 +' k 6)) ;;
  .set 19 (M (v 4 +' k 7)) ;;
  .set 20 (v 17 +' k 2 +' k 2 *' v 1) ;;
  .set 21 (M (v 3)) ;;
  .set 22 (M (v 3 +' k 1)) ;;
  .set 23 (M (v 3 +' k 2)) ;;
  .set 24 (M (v 3 +' k 3)) ;;
  .set 25 (M (v 3 +' k 4)) ;;
  .set 26 (M (v 3 +' k 5)) ;;
  .call pColor [v 0,v 1,v 5,v 21,v 22,v 23,v 24,v 25,v 26,v 8,v 9,v 10,v 11,v 6,
    v 12,v 13,v 14,v 15,v 16,v 17,v 20,v 18,v 19] 27 ;;
  .store (v 7) (v 27) ;;
  .set 0 (v 7)

def program : Program := LightBandRawAColor.program ++ [LightEncodedColorLayout.body 9,body 44 43]

theorem program_length : program.length=46 := rfl

def time (n : ℕ) : ℕ := LightEncodedColorLayout.time n (bandSize n)+
  LightBandRawAColor.time (inputBits n+1) n (bandSize n)+1200

def space (free n : ℕ) : ℕ :=
  LightBandRawAColor.space (tables free n) (vals free n (bandSize n)) (inputBits n+1) n (bandSize n)+1

def word (n U : ℕ) : ℕ :=
  LightBandRawAColor.word (inputBits n+1) n (bandSize n) U+
    LightEncodedColorLayout.word n (bandSize n)+(inputBits n+1)+100

variable {lim : Limits} {d : ℕ}

theorem program_meets {μ : ℕ → ℤ} {src n params row free U : ℕ}
    (color : Coloring.Parameter (inputBits n+1)) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : 0 < n)
    (hsrc : src+n ≤ free) (hparams : params+19 ≤ free) (hrow : row+6 ≤ free)
    (hspace : space free n ≤ lim.space) (hword : (word n U : ℤ) ≤ lim.word)
    (hd : d+LightBandRawAColor.depth (inputBits n+1) n (bandSize n)+2 ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ))
    (hparameters : Seg μ params (LightParameterInit.values n))
    (hcolor : Seg μ row (ColorParameters.fields color)) :
    Meets lim program 45 d [src,n,params,row,free] μ (time n)
      (fun r ν => r=(normalizedEnd free n (bandSize n) : ℤ) ∧
        EncodedColorNormalizedData.Output ν free n color x ∧ Kept μ ν free) := by
  have hColorSpace : LightBandRawAColor.space (tables free n) (vals free n (bandSize n))
      (inputBits n+1) n (bandSize n) ≤ lim.space := by unfold space at hspace; omega
  have hEnd : normalizedEnd free n (bandSize n)+1 ≤ lim.space := by
    have hh : normalizedEnd free n (bandSize n) ≤
        LightBandRawAColor.space (tables free n) (vals free n (bandSize n)) (inputBits n+1) n (bandSize n) :=
      le_max_right _ _
    unfold space at hspace
    omega
  have hbaseLinear : free+17+13*n ≤ lim.space := by
    unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase
      LightBandRawA.capacity vals rec tables ce cv be bv ae av class2 class1 class0 colors at hEnd
    omega
  have hbaseLinearZ : (free : ℤ)+17+13*(n : ℤ) ≤ lim.word :=
    (by exact_mod_cast hbaseLinear : _ ≤ (lim.space : ℤ)).trans hw
  have hcap : bandSize n*ColorBandBounds.count n (bandSize n) ≤ normalizedEnd free n (bandSize n) := by
    unfold normalizedEnd LightBandRawA.space LightBandRawA.positionBase LightBandRawA.ownerBase LightBandRawA.capacity
    omega
  have hCW : (LightBandRawAColor.word (inputBits n+1) n (bandSize n) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hLW : (LightEncodedColorLayout.word n (bandSize n) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hWNat : inputBits n+1 ≤ word n U := by unfold word; omega
  have hW : ((inputBits n+1 : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hWNat).trans hword
  have hG : (bandSize n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightEncodedColorLayout.word; omega)).trans hLW
  have hFew : (4 : ℤ) ≤ lim.word := by
    have hh : (4 : ℕ) ≤ word n U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hfree := free_le_normalizedEnd free n (bandSize n)
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords⟩ := normalized_ends_before_count free n (bandSize n)
  obtain ⟨hbits,_,_,_,_,hband,_⟩ := EncodedColorParameterData.reads hparameters
  have hParam17 : ((params : ℤ)+17).toNat=params+17 := by omega
  have add1 : ((free : ℤ)+1).toNat=free+1 := by omega
  have add2 : ((free : ℤ)+2).toNat=free+2 := by omega
  have add3 : ((free : ℤ)+3).toNat=free+3 := by omega
  have add4 : ((free : ℤ)+4).toNat=free+4 := by omega
  have add5 : ((free : ℤ)+5).toNat=free+5 := by omega
  have add6 : ((free : ℤ)+6).toNat=free+6 := by omega
  have add7 : ((free : ℤ)+7).toNat=free+7 := by omega
  have hrow1 : ((row : ℤ)+1).toNat=row+1 := by omega
  have hrow2 : ((row : ℤ)+2).toNat=row+2 := by omega
  have hrow3 : ((row : ℤ)+3).toNat=row+3 := by omega
  have hrow4 : ((row : ℤ)+4).toNat=row+4 := by omega
  have hrow5 : ((row : ℤ)+5).toNat=row+5 := by omega
  apply Meets.of_body (p := 45) (by rfl : program[45]?=some (body 44 43))
  unfold body time
  light_set (inputBits n+1 : ℕ) using hbits
  light_set (bandSize n : ℕ) using hband,hParam17
  light_call (LightEncodedColorLayout.meets (d := d+1) (μ := μ) (n := n) (g := bandSize n) (free := free)
    (by rfl : program[44]?=some (LightEncodedColorLayout.body 9))
    (by rfl : program[9]?=some LightSmallDivide.body) hw hn (bandSize_pos n) hEnd hLW (by omega))
    with ptr μ₀ ⟨hptr,heads,keptLayout⟩
  have hcolor₀ := hcolor.of_kept keptLayout (by simpa only [ColorParameters.fields,List.length_cons,List.length_nil] using hrow)
  obtain ⟨hi,hj,h00,h01,h10,h11⟩ := EncodedColorParameterData.color_reads hcolor₀
  obtain ⟨readA,readAE,readB,readBE,readC,readCE,readRec,readVals⟩ := EncodedColorNormalizedData.heads_read heads
  have hiBound := color.1.1.isLt
  have hjBound := color.1.2.isLt
  have h00Bound := (color.2 (false,false)).isLt
  have h01Bound := (color.2 (false,true)).isLt
  have h10Bound := (color.2 (true,false)).isLt
  have h11Bound := (color.2 (true,true)).isLt
  light_set (colors free : ℕ) using colors
  light_set (class0 free n : ℕ) using class0,colors
  light_set (class1 free n : ℕ) using class1,class0,colors
  light_set (class2 free n : ℕ) using class2,class1,class0,colors
  light_set (av free n : ℕ) using readA
  light_set (ae free n : ℕ) using readAE,add1
  light_set (bv free n : ℕ) using readB,add2
  light_set (be free n : ℕ) using readBE,add3
  light_set (cv free n : ℕ) using readC,add4
  light_set (ce free n : ℕ) using readCE,add5
  light_set (rec free n (bandSize n) : ℕ) using readRec,add6
  light_set (vals free n (bandSize n) : ℕ) using readVals,add7
  light_set (tables free n : ℕ) using tables
  light_set (color.1.1.val : ℕ) using hi
  light_set (color.1.2.val : ℕ) using hj,hrow1
  light_set ((color.2 (false,false)).val : ℕ) using h00,hrow2
  light_set ((color.2 (false,true)).val : ℕ) using h01,hrow3
  light_set ((color.2 (true,false)).val : ℕ) using h10,hrow4
  light_set ((color.2 (true,true)).val : ℕ) using h11,hrow5
  have hread₀ := hread.of_kept keptLayout (by simpa only [List.length_ofFn] using hsrc)
  have hColor := (LightBandRawAColor.program_meets (d := d+1) (μ := μ₀)
    (colors := colors free) (dst0 := class0 free n) (dst1 := class1 free n) (dst2 := class2 free n)
    (av := av free n) (ae := ae free n) (bv := bv free n) (be := be free n) (cv := cv free n) (ce := ce free n)
    (work := tables free n) (rec := rec free n (bandSize n)) (vals := vals free n (bandSize n))
    color x hw (LightColorParametersCosts.width_sufficient n) (bandSize_pos n)
    (by unfold colors; omega) le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl hColorSpace hCW (by omega) hread₀ hbound).append [LightEncodedColorLayout.body 9,body 44 43]
  light_call hColor with rA ν₁ ⟨output,keptColor⟩
  obtain ⟨A,hsA,B,hsB,C,hsC,normalized⟩ := SourceFiniteData.Normalized.of_output output
  have ha := length_classList_le color x 0 1
  have hb := length_classList_le color x 1 1
  have hc := length_classList_le color x 2 (-1)
  have hnA := normalized.2.1.2.1.trans ha
  have hnB := normalized.2.2.1.2.1.trans hb
  have hnC := normalized.2.2.2.1.2.1.trans hc
  have hlen := incidences_length_le (hsA := hsA) (hsB := hsB) (hsC := hsC) hnA hnB hnC
  have hrA : rA=((incidences n A B C hsA hsB hsC).length : ℤ) := by
    simpa only [incidences,BandRawA.values_length] using normalized.1
  have hlenWord : ((incidences n A B C hsA hsB hsC).length : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((hlen.trans hcap).trans (by omega))).trans hw
  have hheads₁ := heads.of_kept keptColor (by simp [normalizedHeads,colors])
  light_store (normalizedEnd free n (bandSize n)) ((incidences n A B C hsA hsB hsC).length : ℕ) using hrA,hptr
  light_set (normalizedEnd free n (bandSize n) : ℕ) using hptr
  have keptCount : Kept ν₁ (Function.update ν₁ (normalizedEnd free n (bandSize n))
      ((incidences n A B C hsA hsB hsC).length : ℤ)) (normalizedEnd free n (bandSize n)) := by
    intro i hi
    rw [Function.update_of_ne (by omega)]
  have hNormalized := normalized.keep keptCount ha hb hc hav hae hbv hbe hcv hce htables hrecords le_rfl
  rw [hrA] at hNormalized
  refine ⟨rfl,⟨?_,A,hsA,B,hsB,C,hsC,?_,hNormalized⟩,?_⟩
  · exact hheads₁.of_kept keptCount (by
      simpa only [normalizedHeads,List.length_cons,List.length_nil] using hfree)
  · simp
  · intro i hi
    exact (keptCount i (by omega)).trans ((keptColor i (by unfold colors; omega)).trans (keptLayout i hi))

end ThreeSum.LightEncodedColorNormalize
