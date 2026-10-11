import Submission.ThreeSum.LightColorBands
import Submission.ThreeSum.LightBandRawACatalog
import Submission.ThreeSum.BandRawAOriginal

/-!
# Original input to the retained owner and A-incidence catalog

The selected index coloring, class extraction, normalization, endpoint
construction, three rectangular owner tables, four-cell owner records, and
packed A-incidence rows are all executed by this fixed program. The rows
retain physical owner identities and sorted-array coordinates. Membership
in the original color classes is retained separately by `Represents`.
-/

namespace ThreeSum.LightBandRawAColor

open Light BandPartition BandCandidateRows BandRawA ColorClassLists

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000

/-- The existing color/band arguments, followed by records and incidence
value destinations. -/
def body (pColor pCatalog : ℕ) : Stmt :=
  .call pColor [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,
    v 12,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20] 23 ;;
  .call pCatalog [v 20,v 21,v 14,v 15,v 17,v 19,v 13,v 22] 0

def catalogTime (n g : ℕ) : ℕ :=
  3000*(ColorBandBounds.count n g+3*size n g+1)*(g+1)

def time (W n g : ℕ) : ℕ := LightColorBands.time W n g+catalogTime n g+300

def space (work vals W n g : ℕ) : ℕ :=
  max (LightColorBands.space work W n g)
    (LightBandRawA.space vals (ColorBandBounds.count n g) g)

def word (W n g U : ℕ) : ℕ :=
  LightColorBands.word W n g U+
    LightBandRawACatalog.word n (size n g) (size n g) (size n g) g

def depth (W n g : ℕ) : ℕ := LightColorBands.depth W n g+5

def Output (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g)
    (originalA originalB originalC : List ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
    let rs := sortedRecords A B C g hg hsA hsB hsC
    r = ((items A.length g rs).length : ℤ) ∧
      LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
      LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
      LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
      LightBandEnumeration.Tables μ tables
        (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
        (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
        (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)) ∧
      Seg μ rec (cells rs) ∧
      Stored μ vals (LightBandRawA.ownerBase vals rs.length g)
        (LightBandRawA.positionBase vals rs.length g)
        (fun i => A.getD i 0) (items A.length g rs)

theorem tables_keep {μ ν : ℕ → ℤ} {tables bound : ℕ} {A B C : BandEnumeration.Family}
    (ht : LightBandEnumeration.Tables μ tables A B C) (hk : Kept μ ν bound)
    (hb : tables+LightBandEnumeration.count A.size B.size C.size ≤ bound) :
    LightBandEnumeration.Tables ν tables A B C := by
  unfold LightBandEnumeration.count at hb
  refine ⟨?_,?_,?_⟩
  · intro j hj k hk'
    have hindex := index_lt hj hk'
    rw [hk _ (by omega)]
    exact ht.1 j hj k hk'
  · intro i hi j hj
    have hindex := index_lt hi hj
    rw [hk _ (by omega)]
    exact ht.2.1 i hi j hj
  · intro i hi k hk'
    have hindex := index_lt hi hk'
    rw [hk _ (by omega)]
    exact ht.2.2 i hi k hk'

structure Procs (P : Program) (pMain : ℕ) where
  pColor : ℕ
  pCatalog : ℕ
  color : LightColorBands.Procs P pColor
  catalog : LightBandRawACatalog.Procs P pCatalog
  main : P[pMain]? = some (body pColor pCatalog)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets
    {pMain src n W colors dst0 dst1 dst2 g av ae bv be cv ce work rec vals U : ℕ}
    {μ : ℕ → ℤ} (R : Procs P pMain) (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (htable : work+ColorBandBounds.count n g ≤ rec)
    (hrec : rec+4*ColorBandBounds.count n g ≤ vals)
    (hspace : space work vals W n g ≤ lim.space)
    (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d+depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim P pMain d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work,rec,vals] μ (time W n g)
      (fun r ν => Output ν av ae bv be cv ce work rec vals g hg
        (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) := by
  have hcSpace := (Nat.le_max_left (LightColorBands.space work W n g)
    (LightBandRawA.space vals (ColorBandBounds.count n g) g)).trans hspace
  have hrSpace := (Nat.le_max_right (LightColorBands.space work W n g)
    (LightBandRawA.space vals (ColorBandBounds.count n g) g)).trans hspace
  have hcWord : (LightColorBands.word W n g U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show LightColorBands.word W n g U ≤ word W n g U by
      unfold word; omega)).trans hword
  have hcDepth : d+1+LightColorBands.depth W n g ≤ lim.depth := by
    unfold depth at hd; omega
  have hrDepth : d+1+3 < lim.depth := by unfold depth at hd; omega
  have len0 := length_classList_le p x 0 1
  have len1 := length_classList_le p x 1 1
  have len2 := length_classList_le p x 2 (-1)
  apply Meets.of_body R.main
  unfold body time
  light_call (R.color.meets (d := d+1) p x hw hn hg hsrc hcolors h0 h1 h2
    hav hae hbv hbe hcv hce hcSpace hcWord hcDepth hread hbound)
    with colorResult ν₁ ⟨hout,hkeepColor⟩
  obtain ⟨A,hsA,B,hsB,C,hsC,hcolorResult,hrepA,hrepB,hrepC,htables⟩ := hout
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  have hnA : A.length ≤ n := hrepA.2.1.trans len0
  have hnB : B.length ≤ n := hrepB.2.1.trans len1
  have hnC : C.length ≤ n := hrepC.2.1.trans len2
  have ha : aFamily.size ≤ size n g := size_mono hnA
  have hb : bFamily.size ≤ size n g := size_mono hnB
  have hc : cFamily.size ≤ size n g := size_mono hnC
  have hcount : LightBandEnumeration.count aFamily.size bFamily.size cFamily.size ≤
      ColorBandBounds.count n g := by
    have hh := LightBandEnumeration.count_mono ha hb hc
    have heq : LightBandEnumeration.count (size n g) (size n g) (size n g) =
        ColorBandBounds.count n g := by unfold LightBandEnumeration.count ColorBandBounds.count; ring
    rwa [heq] at hh
  have hcatSpace : LightBandRawACatalog.space vals aFamily.size bFamily.size cFamily.size g ≤
      lim.space := by
    have hm := Nat.mul_le_mul_left g hcount
    unfold LightBandRawACatalog.space LightBandRawA.space LightBandRawA.positionBase
      LightBandRawA.ownerBase LightBandRawA.capacity at hrSpace ⊢
    omega
  have hcatWord : (LightBandRawACatalog.word A.length aFamily.size bFamily.size cFamily.size g : ℤ) ≤
      lim.word := by
    have hh := LightBandEnumeration.count_mono ha hb hc
    apply (Int.ofNat_le.mpr (show LightBandRawACatalog.word A.length aFamily.size bFamily.size
        cFamily.size g ≤ word W n g U by
      unfold word LightBandRawACatalog.word LightBandCandidates.word LightBandRawA.word
      omega)).trans hword
  have hcatTime : LightBandRawACatalog.time aFamily.size bFamily.size cFamily.size g ≤
      catalogTime n g := by
    apply (LightBandRawACatalog.time_bound _ _ _ _).trans
    unfold catalogTime
    exact Nat.mul_le_mul_right (g+1) (Nat.mul_le_mul_left 3000 (by omega))
  have hsource : ∀ j < A.length, ν₁ (av+j)=A.getD j 0 := by
    intro j hj
    exact hrepA.1.getD hj 0
  have hcat := R.catalog.meets (d := d+1) (tables := work) (rec := rec) (src := av)
    (headerA := ae) (headerB := be) (headerC := ce) (vals := vals)
    aFamily bFamily cFamily rfl hw hrDepth hg (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) hcatSpace hcatWord
    hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2 htables hsource
  light_call (hcat.mono_time hcatTime)
    with result ν₂ ⟨hresult,hrecords,hstored,hkeepCatalog⟩
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hresult,
    hrepA.keep hkeepCatalog (by omega) (by omega),
    hrepB.keep hkeepCatalog (by omega) (by omega),
    hrepC.keep hkeepCatalog (by omega) (by omega),
    tables_keep (A := aFamily) (B := bFamily) (C := cFamily)
      htables hkeepCatalog (by omega),hrecords,?_⟩,?_⟩
  · simpa only [sortedRecords,records_length] using hstored
  · intro a ha'
    change ν₂ a=μ a
    exact (hkeepCatalog a (by omega)).trans (hkeepColor a ha')

/-- The verified color/band prefix retains its original procedure indices. -/
def program : Program := LightColorBands.program ++
  [LightBandRawACatalog.body 28 38,
    LightBandCandidates.body 29 32 35,
    LightBandCandidatesTable.body 30,LightBandCandidatesRow.body 31,LightBandCandidatesCell.body .bc,
    LightBandCandidatesTable.body 33,LightBandCandidatesRow.body 34,LightBandCandidatesCell.body .ab,
    LightBandCandidatesTable.body 36,LightBandCandidatesRow.body 37,LightBandCandidatesCell.body .ac,
    LightBandRawA.body 39,LightBandRawAStep.body 40,LightBandRawARow.body 41 42,copyBody,fillBody,
    body 20 27]

def programProcs : Procs program 43 where
  pColor := 20
  pCatalog := 27
  color := {
    pClasses := 21
    pBands := 0
    classes := ⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
    bands := {
      pPrepare := 1
      pEnumerate := 12
      prepare := ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
      enumerate := ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
      main := rfl }
    main := rfl }
  catalog := {
    pCandidates := 28
    pRaw := 38
    candidates := ⟨29,32,35,30,33,36,31,34,37,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
    raw := ⟨39,40,41,42,rfl,rfl,rfl,rfl,rfl⟩
    main := rfl }
  main := rfl

theorem program_length : program.length=44 := rfl

theorem program_meets
    {src n W colors dst0 dst1 dst2 g av ae bv be cv ce work rec vals U : ℕ}
    {μ : ℕ → ℤ} (p : Coloring.Parameter W) (x : Fin n → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W) (hg : 0 < g)
    (hsrc : src+n ≤ colors) (hcolors : colors+n ≤ dst0)
    (h0 : dst0+n+1 ≤ dst1) (h1 : dst1+n+1 ≤ dst2) (h2 : dst2+n+1 ≤ av)
    (hav : av+n ≤ ae) (hae : ae+2+2*n ≤ bv)
    (hbv : bv+n ≤ be) (hbe : be+2+2*n ≤ cv)
    (hcv : cv+n ≤ ce) (hce : ce+2+2*n ≤ work)
    (htable : work+ColorBandBounds.count n g ≤ rec)
    (hrec : rec+4*ColorBandBounds.count n g ≤ vals)
    (hspace : space work vals W n g ≤ lim.space)
    (hword : (word W n g U : ℤ) ≤ lim.word) (hd : d+depth W n g ≤ lim.depth)
    (hread : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i| ≤ (U : ℤ)) :
    Meets lim program 43 d [src,n,W,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      colors,dst0,dst1,dst2,g,av,ae,bv,be,cv,ce,work,rec,vals] μ (time W n g)
      (fun r ν => Output ν av ae bv be cv ce work rec vals g hg
        (classList p x 0 1) (classList p x 1 1) (classList p x 2 (-1)) r ∧
          Kept μ ν colors) :=
  programProcs.meets p x hw hn hg hsrc hcolors h0 h1 h2 hav hae hbv hbe hcv hce htable
    hrec hspace hword hd hread hbound

theorem time_bound (W n g : ℕ) :
    time W n g ≤ 1200*(W+1)*(n+1)+ColorBandBounds.time n g+catalogTime n g+600 := by
  have h := LightColorBands.time_bound W n g
  unfold time
  omega

end ThreeSum.LightBandRawAColor
