import Submission.ThreeSum.LightHeaderBands

/-!
# Closed normalization and band listing for three supplied color classes

The three class arrays are sorted and deduplicated separately. Their actual
length/count headers then drive the actual owner-table enumerator. The program
has twenty fixed procedures. No sorting function, lookup function, or band
enumerator is supplied by the caller.
-/

namespace ThreeSum.LightBandPreprocessing

open Light ThreeSum.BandPartition

set_option maxHeartbeats 1800000
set_option maxRecDepth 5000

variable {lim : Limits} {P : Program}

def Represents (μ : ℕ → ℤ) (values endpoints g : ℕ) (hg : 0 < g)
    (original L : List ℤ) (hs : L.Pairwise (· < ·)) : Prop :=
  Seg μ values L ∧ L.length ≤ original.length ∧ (∀ z, z ∈ L ↔ z ∈ original) ∧
    LightHeaderBands.At μ endpoints L.length
      (family (fun i => L.getD i 0) L.length g hg (LightSortedBands.getD_strict hs))

def Output (μ : ℕ → ℤ) (av ae bv be cv ce dst g : ℕ) (hg : 0 < g)
    (originalA originalB originalC : List ℤ) (r : ℤ) : Prop :=
  ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
    (B : List ℤ) (hsB : B.Pairwise (· < ·))
    (C : List ℤ) (hsC : C.Pairwise (· < ·)),
      r = (LightBandEnumeration.count (size A.length g) (size B.length g) (size C.length g) : ℤ) ∧
      Represents μ av ae g hg originalA A hsA ∧
      Represents μ bv be g hg originalB B hsB ∧
      Represents μ cv ce g hg originalC C hsC ∧
      LightBandEnumeration.Tables μ dst
        (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
        (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
        (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC))

theorem Represents.keep {μ μ' : ℕ → ℤ} {values endpoints g bound : ℕ} {hg : 0 < g}
    {original L : List ℤ} {hs : L.Pairwise (· < ·)}
    (h : Represents μ values endpoints g hg original L hs) (hk : Kept μ μ' bound)
    (hv : values+original.length ≤ bound) (he : endpoints+2+2*original.length ≤ bound) :
    Represents μ' values endpoints g hg original L hs := by
  obtain ⟨hseg,hn,hmem,hlen,hcount,hAt⟩ := h
  have hm := size_le L.length g
  refine ⟨?_,hn,hmem,?_,?_,?_⟩
  · intro i hi
    rw [hk (values+i) (by omega)]
    exact hseg i hi
  · rw [hk endpoints (by omega)]
    exact hlen
  · rw [hk (endpoints+1) (by omega)]
    exact hcount
  · exact hAt.keep hk (by change endpoints+2+size L.length g ≤ bound; omega)
      (by change endpoints+2+L.length+size L.length g ≤ bound; omega)

/-- Arguments: source/length pairs for A, B, C; band size; value/header
output pairs for A, B, C; common scratch and table output address. -/
def body (pPrepare pEnumerate : ℕ) : Stmt :=
  .call pPrepare [v 0,v 1,v 6,v 7,v 8,v 13] 14 ;;
  .call pPrepare [v 2,v 3,v 6,v 9,v 10,v 13] 14 ;;
  .call pPrepare [v 4,v 5,v 6,v 11,v 12,v 13] 14 ;;
  .call pEnumerate [v 8,v 10,v 12,v 13] 0

def time (a b c g : ℕ) : ℕ :=
  LightSortedBands.time a+LightSortedBands.time b+LightSortedBands.time c+
    LightHeaderBands.time (size a g) (size b g) (size c g)+300

def space (work a b c g : ℕ) : ℕ :=
  work+(a+b+c)+LightBandEnumeration.count (size a g) (size b g) (size c g)+
    LightBandEnumeration.width (size a g) (size b g) (size c g)+1

def word (a b c g U : ℕ) : ℕ :=
  a+b+c+g+2+LightBandEnumeration.word (size a g) (size b g) (size c g) U

def depth (a b c g : ℕ) : ℕ :=
  a+b+c+Nat.clog 2 (a+b+c)+
    LightBandEnumeration.width (size a g) (size b g) (size c g)+10

structure Procs (P : Program) (pMain : ℕ) where
  pPrepare : ℕ
  pEnumerate : ℕ
  prepare : LightSortedBands.Procs P pPrepare
  enumerate : LightHeaderBands.Procs P pEnumerate
  main : P[pMain]? = some (body pPrepare pEnumerate)

theorem Procs.meets {pMain srcA srcB srcC av ae bv be cv ce work g U d : ℕ}
    {μ : ℕ → ℤ} {originalA originalB originalC : List ℤ} (R : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA+originalA.length ≤ srcB) (hsrcBC : srcB+originalB.length ≤ srcC)
    (hsrcCv : srcC+originalC.length ≤ av)
    (hav : av+originalA.length ≤ ae) (hae : ae+2+2*originalA.length ≤ bv)
    (hbv : bv+originalB.length ≤ be) (hbe : be+2+2*originalB.length ≤ cv)
    (hcv : cv+originalC.length ≤ ce) (hce : ce+2+2*originalC.length ≤ work)
    (hspace : space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d+depth originalA.length originalB.length originalC.length g ≤ lim.depth)
    (hAread : Seg μ srcA originalA) (hBread : Seg μ srcB originalB) (hCread : Seg μ srcC originalC)
    (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ)) (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [srcA,originalA.length,srcB,originalB.length,srcC,originalC.length,g,av,ae,bv,be,cv,ce,work]
      μ (time originalA.length originalB.length originalC.length g)
      (fun r μ' => Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧
        Kept μ μ' srcA) := by
  have hspace' : work+(originalA.length+originalB.length+originalC.length)+
      LightBandEnumeration.count (size originalA.length g) (size originalB.length g) (size originalC.length g)+
      LightBandEnumeration.width (size originalA.length g) (size originalB.length g) (size originalC.length g)+1 ≤
      lim.space := hspace
  have hnormSpaceA : LightSortedBands.space work originalA.length ≤ lim.space := by
    unfold LightSortedBands.space; omega
  have hnormSpaceB : LightSortedBands.space work originalB.length ≤ lim.space := by
    unfold LightSortedBands.space; omega
  have hnormSpaceC : LightSortedBands.space work originalC.length ≤ lim.space := by
    unfold LightSortedBands.space; omega
  have hnormWord (n : ℕ) (hn : n ≤ originalA.length+originalB.length+originalC.length) :
      ((n+g+2 : ℕ) : ℤ) ≤ lim.word := by
    have hh : n+g+2 ≤ word originalA.length originalB.length originalC.length g U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hnormDepth (n : ℕ) (hn : n ≤ originalA.length+originalB.length+originalC.length) :
      (d+1)+n+Nat.clog 2 n+3 ≤ lim.depth := by
    have hlog := Nat.clog_mono_right 2 hn
    unfold depth at hd
    omega
  have hgWord : ((g+2 : ℕ) : ℤ) ≤ lim.word := by simpa using hnormWord 0 (by omega)
  have hdSmall : d+4 ≤ lim.depth := by unfold depth at hd; omega
  apply Meets.of_body R.main
  unfold body time
  light_call (R.prepare.meets (d := d+1) (src := srcA) (values := av) (endpoints := ae) (work := work)
    hw hg (by omega) hav (by omega) hnormSpaceA (hnormWord _ (by omega))
    (hnormDepth _ (by omega)) hAread)
    using LightSortedBands.time,LightNormalize.time,sortTime,LightNormalize.dedupTime
    with aCount μ₁ ⟨haCount,hPreparedA,hkeep₁⟩
  have hBread₁ : Seg μ₁ srcB originalB := by
    intro i hi
    rw [hkeep₁ (srcB+i) (by omega) (by omega) (by omega) (by omega)]
    exact hBread i hi
  have hCread₁ : Seg μ₁ srcC originalC := by
    intro i hi
    rw [hkeep₁ (srcC+i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread i hi
  light_call (R.prepare.meets (d := d+1) (src := srcB) (values := bv) (endpoints := be) (work := work)
    hw hg (by omega) hbv (by omega) hnormSpaceB (hnormWord _ (by omega))
    (hnormDepth _ (by omega)) hBread₁)
    using LightSortedBands.time,LightNormalize.time,sortTime,LightNormalize.dedupTime
    with bCount μ₂ ⟨hbCount,hPreparedB,hkeep₂⟩
  have hPreparedA₂ : LightSortedBands.Prepared μ₂ av ae g originalA := by
    apply hPreparedA.transfer
    intro a ha
    apply hkeep₂ a <;> rcases ha with ha | ha <;> omega
  have hCread₂ : Seg μ₂ srcC originalC := by
    intro i hi
    rw [hkeep₂ (srcC+i) (by omega) (by omega) (by omega) (by omega)]
    exact hCread₁ i hi
  light_call (R.prepare.meets (d := d+1) (src := srcC) (values := cv) (endpoints := ce) (work := work)
    hw hg (by omega) hcv hce hnormSpaceC (hnormWord _ (by omega))
    (hnormDepth _ (by omega)) hCread₂)
    using LightSortedBands.time,LightNormalize.time,sortTime,LightNormalize.dedupTime
    with cCount μ₃ ⟨hcCount,hPreparedC,hkeep₃⟩
  have hPreparedA₃ : LightSortedBands.Prepared μ₃ av ae g originalA := by
    apply hPreparedA₂.transfer
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  have hPreparedB₃ : LightSortedBands.Prepared μ₃ bv be g originalB := by
    apply hPreparedB.transfer
    intro a ha
    apply hkeep₃ a <;> rcases ha with ha | ha <;> omega
  obtain ⟨A,hsA,hASeg,hALen,hAMem,hAHeader,hACount,hAAt⟩ := hPreparedA₃.family hg
  obtain ⟨B,hsB,hBSeg,hBLen,hBMem,hBHeader,hBCount,hBAt⟩ := hPreparedB₃.family hg
  obtain ⟨C,hsC,hCSeg,hCLen,hCMem,hCHeader,hCCount,hCAt⟩ := hPreparedC.family hg
  let aFamily := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let bFamily := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let cFamily := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  have hsa : aFamily.size ≤ size originalA.length g := size_mono hALen
  have hsb : bFamily.size ≤ size originalB.length g := size_mono hBLen
  have hsc : cFamily.size ≤ size originalC.length g := size_mono hCLen
  have hsan : aFamily.size ≤ originalA.length := hsa.trans (size_le _ _)
  have hsbn : bFamily.size ≤ originalB.length := hsb.trans (size_le _ _)
  have hscn : cFamily.size ≤ originalC.length := hsc.trans (size_le _ _)
  have hcountBound := LightBandEnumeration.count_mono hsa hsb hsc
  have hwidthBound := LightBandEnumeration.width_mono hsa hsb hsc
  have henumSpace : LightBandEnumeration.space work aFamily.size bFamily.size cFamily.size ≤ lim.space := by
    unfold LightBandEnumeration.space
    omega
  have henumWord : (LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U : ℤ) ≤ lim.word := by
    have hh : LightBandEnumeration.word aFamily.size bFamily.size cFamily.size U ≤
        word originalA.length originalB.length originalC.length g U := by
      unfold word LightBandEnumeration.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have henumDepth : (d+1)+LightBandEnumeration.width aFamily.size bFamily.size cFamily.size+5 ≤ lim.depth := by
    unfold depth at hd
    omega
  have henumTime : LightHeaderBands.time aFamily.size bFamily.size cFamily.size ≤
      LightHeaderBands.time (size originalA.length g) (size originalB.length g) (size originalC.length g) :=
    Nat.add_le_add_right (LightBandEnumeration.time_mono hsa hsb hsc) 100
  have hrepA : Represents μ₃ av ae g hg originalA A hsA :=
    ⟨hASeg,hALen,hAMem,hAHeader,hACount,hAAt⟩
  have hrepB : Represents μ₃ bv be g hg originalB B hsB :=
    ⟨hBSeg,hBLen,hBMem,hBHeader,hBCount,hBAt⟩
  have hrepC : Represents μ₃ cv ce g hg originalC C hsC :=
    ⟨hCSeg,hCLen,hCMem,hCHeader,hCCount,hCAt⟩
  light_call ((R.enumerate.meets (d := d+1) aFamily bFamily cFamily hw
    (by omega) (by omega) (by omega) henumSpace henumWord henumDepth
    hrepA.2.2.2 hrepB.2.2.2 hrepC.2.2.2
    (LightSortedBands.family_bounded hg hsA hAMem hAU)
    (LightSortedBands.family_bounded hg hsB hBMem hBU)
    (LightSortedBands.family_bounded hg hsC hCMem hCU)).mono_time henumTime)
    using LightSortedBands.time,LightNormalize.time,sortTime,LightNormalize.dedupTime
    with result μ₄ ⟨hresult,htable,hkeep₄⟩
  refine ⟨⟨A,hsA,B,hsB,C,hsC,hresult,
    hrepA.keep hkeep₄ (by omega) (by omega),
    hrepB.keep hkeep₄ (by omega) (by omega),
    hrepC.keep hkeep₄ (by omega) hce,htable⟩,?_⟩
  intro a ha
  change μ₄ a = μ a
  rw [hkeep₄ a (by omega),hkeep₃ a (by omega) (by omega) (by omega) (by omega),
    hkeep₂ a (by omega) (by omega) (by omega) (by omega),
    hkeep₁ a (by omega) (by omega) (by omega) (by omega)]

def program : Program :=
  [body 1 12,
    LightSortedBands.body 2 8,LightNormalize.body 3 7,
    sortBody 3 4 5 6,halfBody,mergeBody,copyBody,LightNormalize.dedupBody 7,
    LightBandPartition.body 9 10 11,LightSmallDivide.body,
    LightBandPartition.lowerBody,LightBandPartition.upperBody,
    LightHeaderBands.body 13,LightBandEnumeration.body 14 15 16,clog2Body,powTableBody,
    LightBandTable.body 17,LightBandTable.rowBody 18,LightBandLookup.body 19,LightBandLookup.searchBody 19]

def program_procs : Procs program 0 where
  pPrepare := 1
  pEnumerate := 12
  prepare := ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
  enumerate := ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
  main := rfl

theorem program_meets {srcA srcB srcC av ae bv be cv ce work g U d : ℕ}
    {μ : ℕ → ℤ} {originalA originalB originalC : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrcAB : srcA+originalA.length ≤ srcB) (hsrcBC : srcB+originalB.length ≤ srcC)
    (hsrcCv : srcC+originalC.length ≤ av)
    (hav : av+originalA.length ≤ ae) (hae : ae+2+2*originalA.length ≤ bv)
    (hbv : bv+originalB.length ≤ be) (hbe : be+2+2*originalB.length ≤ cv)
    (hcv : cv+originalC.length ≤ ce) (hce : ce+2+2*originalC.length ≤ work)
    (hspace : space work originalA.length originalB.length originalC.length g ≤ lim.space)
    (hword : (word originalA.length originalB.length originalC.length g U : ℤ) ≤ lim.word)
    (hd : d+depth originalA.length originalB.length originalC.length g ≤ lim.depth)
    (hAread : Seg μ srcA originalA) (hBread : Seg μ srcB originalB) (hCread : Seg μ srcC originalC)
    (hAU : ∀ z ∈ originalA, |z| ≤ (U : ℤ)) (hBU : ∀ z ∈ originalB, |z| ≤ (U : ℤ))
    (hCU : ∀ z ∈ originalC, |z| ≤ (U : ℤ)) :
    Meets lim program 0 d
      [srcA,originalA.length,srcB,originalB.length,srcC,originalC.length,g,av,ae,bv,be,cv,ce,work]
      μ (time originalA.length originalB.length originalC.length g)
      (fun r μ' => Output μ' av ae bv be cv ce work g hg originalA originalB originalC r ∧
        Kept μ μ' srcA) :=
  program_procs.meets hw hg hsrcAB hsrcBC hsrcCv hav hae hbv hbe hcv hce hspace hword hd
    hAread hBread hCread hAU hBU hCU

end ThreeSum.LightBandPreprocessing
