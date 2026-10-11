import Submission.ThreeSum.LightColorClasses
import Submission.ThreeSum.ColorBandBounds

/-!
# Original input to normalized color bands

This fixed program computes index colors, writes the three class arrays and
their headers, then reads those headers into the existing normalization and
owner-table program. All buffers and resource bounds depend on the original
input length, rather than on externally supplied color-class lengths.
-/

namespace ThreeSum.LightColorBands

open Light ColorClassLists

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

/-- Original array/length/width, six coloring parameters, color and class
buffers, band size, three value/endpoint pairs, and scratch. -/
def body (pClasses pBands : ℕ) : Stmt :=
  .call pClasses [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 20] 21 ;;
  .call pBands [v 10 +' k 1,M (v 10),v 11 +' k 1,M (v 11),
    v 12 +' k 1,M (v 12),v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20] 0

def time (W n g : ℕ) : ℕ := LightColorClasses.time W n+ColorBandBounds.time n g+300
def space (work W n g : ℕ) : ℕ := ColorBandBounds.space work n g+W+1
def word (W n g U : ℕ) : ℕ := 2^(W+1)+ColorBandBounds.word n g U+U
def depth (W n g : ℕ) : ℕ := W+ColorBandBounds.depth n g+5

theorem class_bounded {n W U : ℕ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (c : ℕ) (scale : ℤ) (hs : |scale| ≤ 1) (hx : ∀ i, |x i| ≤ (U : ℤ)) :
    ∀ z ∈ classList p x c scale, |z| ≤ (U : ℤ) := by
  intro z hz
  obtain ⟨i,hi,_,rfl⟩ :=
    (LightClassFilter.mem_items (value x) (LightColorIndex.color p) c scale n z).mp hz
  have hv : |value x i| ≤ (U : ℤ) := by
    simpa only [value,hi,dite_true] using hx ⟨i,hi⟩
  rw [abs_mul]
  calc
    |scale| * |value x i| ≤ 1 * (U : ℤ) :=
      mul_le_mul hs hv (abs_nonneg _) (by norm_num)
    _ = (U : ℤ) := one_mul _

structure Procs (P : Program) (pMain : ℕ) where
  pClasses : ℕ
  pBands : ℕ
  classes : LightColorClasses.Procs P pClasses
  bands : LightBandPreprocessing.Procs P pBands
  main : P[pMain]? = some (body pClasses pBands)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : ℕ}
    {μ : ℕ → ℤ} (R : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (hspace : space work W n g ≤ lim.space)
    (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d+depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work] μ (time W n g)
      (fun r ν => LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
        (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) := by
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  have len2 := length_classList_le p x 2 (-1)
  have lens := class_lengths_sum p x
  have hs : work+(W+1) ≤ lim.space := by
    unfold space ColorBandBounds.space at hspace
    omega
  have hp : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show 2^(W+1) ≤ word W n g U by
      unfold word; omega)).trans hword
  have hU : (U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show U ≤ word W n g U by
      unfold word; omega)).trans hword
  have hcDepth : d+1+W+3 ≤ lim.depth := by unfold depth at hd; omega
  have hsBand : LightBandPreprocessing.space work
      (classList p x 0 1).length (classList p x 1 1).length
      (classList p x 2 (-1)).length g ≤ lim.space := by
    have hh := ColorBandBounds.space_le (work := work) (g := g) lens
    unfold space at hspace
    omega
  have hwBand : (LightBandPreprocessing.word
      (classList p x 0 1).length (classList p x 1 1).length
      (classList p x 2 (-1)).length g U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr ((ColorBandBounds.word_le (g := g) (U := U) lens).trans
      (show ColorBandBounds.word n g U ≤ word W n g U by unfold word; omega))).trans hword
  have hdBand : d+1+LightBandPreprocessing.depth
      (classList p x 0 1).length (classList p x 1 1).length
      (classList p x 2 (-1)).length g ≤ lim.depth := by
    have hh := ColorBandBounds.depth_le (g := g) lens
    unfold depth at hd
    omega
  apply Meets.of_body R.main
  unfold body time
  light_call (R.classes.meets (d := d+1) p x hw hn hsrc hcolors (by omega) (by omega)
    (by omega) hs hp hU hcDepth hread hbound)
    using LightColorClasses.time,LightColorArray.time,LightColorIndex.time,
      LightMaskErase.time,LightClassFilter.time
    with r ν₁ hclasses
  have h0Read := hclasses.header0
  have h1Read := hclasses.header1
  have h2Read := hclasses.header2
  have hb := R.bands.meets (d := d+1) (srcA := dst0+1) (srcB := dst1+1) (srcC := dst2+1)
    (av := av) (ae := ae) (bv := bv) (be := be) (cv := cv) (ce := ce) (work := work)
    hw hg (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hsBand hwBand hdBand
    hclasses.values0 hclasses.values1 hclasses.values2
    (class_bounded p x 0 1 (by norm_num) hbound)
    (class_bounded p x 1 1 (by norm_num) hbound)
    (class_bounded p x 2 (-1) (by norm_num) hbound)
  light_call (hb.mono_time (ColorBandBounds.time_le (g := g) lens))
    using h0Read,h1Read,h2Read,LightColorClasses.time,LightColorArray.time,
      LightColorIndex.time,LightMaskErase.time,LightClassFilter.time
    with result ν₂ ⟨hout,hkeep⟩
  refine ⟨hout,?_⟩
  intro a ha
  exact (hkeep a (by omega)).trans (hclasses.kept a ha)

/-- Keep the already checked twenty-procedure band implementation at its
original indices; append the original-array constructor and its callees. -/
def program : Program := LightBandPreprocessing.program ++
  [body 21 0,LightColorClasses.body 22 26,LightColorArray.body 23 24,powTableBody,
    LightColorIndex.body 25,LightMaskErase.body 25,LightClassFilter.body]

def programProcs : Procs program 20 where
  pClasses := 21
  pBands := 0
  classes := ⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
  bands := {
    pPrepare := 1
    pEnumerate := 12
    prepare := ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
    enumerate := ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
    main := rfl }
  main := rfl

theorem program_length : program.length = 27 := rfl

theorem program_meets {src n W colors dst0 dst1 dst2 g av ae bv be cv ce work U : ℕ}
    {μ : ℕ → ℤ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (hspace : space work W n g ≤ lim.space)
    (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d+depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 20 d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work] μ (time W n g)
      (fun r ν => LightBandPreprocessing.Output ν av ae bv be cv ce work g hg
        (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) :=
  programProcs.meets p x hw hn hg hsrc hcolors h0 h1 h2 hav hae hbv hbe hcv hce
    hspace hword hd hread hbound

theorem time_bound (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+300 := by
  have h := LightColorClasses.time_bound W n
  unfold time
  omega

end ThreeSum.LightColorBands
