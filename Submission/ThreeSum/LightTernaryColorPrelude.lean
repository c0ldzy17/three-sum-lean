import Submission.ThreeSum.LightColorBands
import Submission.ThreeSum.LightColorParametersCosts
import Submission.ThreeSum.LightColorScanHost

/-! Original positions to three normalized color classes, with one band per
class. The returned header and all buffer locations are produced by code. -/
namespace ThreeSum.LightTernaryColorPrelude
open Light ColorClassLists LightColorParametersCosts
set_option maxHeartbeats 7000000
set_option maxRecDepth 20000

def class0 (free n : ℕ) := free+n
def class1 (free n : ℕ) := class0 free n+n+1
def class2 (free n : ℕ) := class1 free n+n+1
def av (free n : ℕ) := class2 free n+n+1
def ae (free n : ℕ) := av free n+n
def bv (free n : ℕ) := ae free n+2+2*n
def be (free n : ℕ) := bv free n+n
def cv (free n : ℕ) := be free n+2+2*n
def ce (free n : ℕ) := cv free n+n
def work (free n : ℕ) := ce free n+2+2*n

def body (pColor : ℕ) : Stmt :=
  .set 5 (M (v 2) +' k 1) ;;
  .set 6 (v 4 +' v 1) ;;
  .set 7 (v 6 +' v 1 +' k 1) ;;
  .set 8 (v 7 +' v 1 +' k 1) ;;
  .set 9 (v 8 +' v 1 +' k 1) ;;
  .set 10 (v 9 +' v 1) ;;
  .set 11 (v 10 +' k 2 +' k 2 *' v 1) ;;
  .set 12 (v 11 +' v 1) ;;
  .set 13 (v 12 +' k 2 +' k 2 *' v 1) ;;
  .set 14 (v 13 +' v 1) ;;
  .set 15 (v 14 +' k 2 +' k 2 *' v 1) ;;
  .call pColor [v 0,v 1,v 5,M (v 3),M (v 3 +' k 1),M (v 3 +' k 2),
    M (v 3 +' k 3),M (v 3 +' k 4),M (v 3 +' k 5),v 4,v 6,v 7,v 8,v 1,
    v 9,v 10,v 11,v 12,v 13,v 14,v 15] 16 ;;
  .set 17 (M (v 10)) ;;
  .set 18 (M (v 12)) ;;
  .set 19 (M (v 14)) ;;
  .store (v 4) (v 9) ;;
  .store (v 4 +' k 1) (v 17) ;;
  .store (v 4 +' k 2) (v 11) ;;
  .store (v 4 +' k 3) (v 18) ;;
  .store (v 4 +' k 4) (v 13) ;;
  .store (v 4 +' k 5) (v 19) ;;
  .store (v 4 +' k 6) (v 15) ;;
  .set 0 (v 4)

def time (n : ℕ) := LightColorBands.time (width n) n n+500
def word (n U : ℕ) := LightColorBands.word (width n) n n U+width n+100
def space (free n : ℕ) := LightColorBands.space (work free n) (width n) n n
def depth (n : ℕ) := LightColorBands.depth (width n) n n+1

def header (free n : ℕ) (A B C : List ℤ) : List ℤ :=
  [av free n,A.length,bv free n,B.length,cv free n,C.length,work free n]

structure Normalized (μ : ℕ→ ℤ) (base n : ℕ) (original L : List ℤ) : Prop where
  seg : Seg μ base L
  sorted : L.Pairwise (· < ·)
  length : L.length≤ n
  mem : ∀ z, z∈L↔z∈original

def Output {n : ℕ} (μ ν : ℕ→ ℤ) (free : ℕ) (p : Coloring.Parameter (width n))
    (x : Fin n→ ℤ) (r : ℤ) : Prop :=
  r=(free:ℤ) ∧ Kept μ ν free ∧ ∃ A B C : List ℤ,
    Seg ν free (header free n A B C) ∧
    Normalized ν (av free n) n (classList p x 0 1) A ∧
    Normalized ν (bv free n) n (classList p x 1 1) B ∧
    Normalized ν (cv free n) n (classList p x 2 (-1)) C

theorem one_band {n : ℕ} (hn : 0<n) :
    BandPartition.size n n=1 ∧ ColorBandBounds.count n n=3 ∧ ColorBandBounds.width n n=2 := by
  have hs : BandPartition.size n n=1 := by
    simp [BandPartition.size,show n≠ 0 by omega,Nat.div_eq_of_lt (by omega : n-1<n)]
  refine ⟨hs,?_,?_⟩
  · simp [ColorBandBounds.count,hs]
  · simp only [ColorBandBounds.width,LightBandEnumeration.width,hs]
    decide

variable {lim : Limits} {P : Program}

theorem meets {pMain pColor src n params row free U d : ℕ}
    (hmain : P[pMain]?=some (body pColor)) (R : LightColorBands.Procs P pColor)
    (μ : ℕ→ ℤ) (p : Coloring.Parameter (width n)) (x : Fin n→ ℤ)
    (hn : 0<n) (hsrc : src+n≤ free) (hparams : params+19≤ free) (hrow : row+6≤ free)
    (hw : (lim.space:ℤ)≤ lim.word) (hspace : space free n≤ lim.space)
    (hword : (word n U:ℤ)≤ lim.word) (hd : d+depth n≤ lim.depth)
    (hbits : μ params=(Scales.inputBits n:ℤ))
    (hfields : Seg μ row (ColorParameters.fields p))
    (hinput : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i|≤ (U:ℤ)) :
    Meets lim P pMain d [src,n,params,row,free] μ (time n)
      (fun r ν=>Output μ ν free p x r) := by
  have hW : (width n:ℤ)≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hbandWord : (LightColorBands.word (width n) n n U:ℤ)≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hWork : work free n≤ lim.space := by
    unfold space LightColorBands.space ColorBandBounds.space at hspace; omega
  have hfree : free≤ work free n := by unfold work ce cv be bv ae av class2 class1 class0; omega
  have hsp : free≤ lim.space := hfree.trans hWork
  have hptr (a : ℕ) (ha : a≤ work free n) : (a:ℤ)≤ lim.word :=
    (Int.ofNat_le.mpr (ha.trans hWork)).trans hw
  have hfW:= hptr free hfree
  have hc0:= hptr (class0 free n) (by unfold work ce cv be bv ae av class2 class1 class0; omega)
  have hc1:= hptr (class1 free n) (by unfold work ce cv be bv ae av class2 class1; omega)
  have hc2:= hptr (class2 free n) (by unfold work ce cv be bv ae av class2; omega)
  have hav:= hptr (av free n) (by unfold work ce cv be bv ae; omega)
  have hae:= hptr (ae free n) (by unfold work ce cv be bv; omega)
  have hbv:= hptr (bv free n) (by unfold work ce cv be; omega)
  have hbe:= hptr (be free n) (by unfold work ce cv; omega)
  have hcv:= hptr (cv free n) (by unfold work ce; omega)
  have hce:= hptr (ce free n) (by unfold work; omega)
  have hwk:= hptr (work free n) le_rfl
  have hc0Add:=hc0
  dsimp only [class0] at hc0Add
  push_cast at hc0Add
  have hc1Add:=hc1
  dsimp only [class1] at hc1Add
  push_cast at hc1Add
  have hc2Add:=hc2
  dsimp only [class2] at hc2Add
  push_cast at hc2Add
  have havAdd:=hav
  dsimp only [av] at havAdd
  push_cast at havAdd
  have haeAdd:=hae
  dsimp only [ae] at haeAdd
  push_cast at haeAdd
  have hbvAdd:=hbv
  dsimp only [bv] at hbvAdd
  push_cast at hbvAdd
  have hbeAdd:=hbe
  dsimp only [be] at hbeAdd
  push_cast at hbeAdd
  have hcvAdd:=hcv
  dsimp only [cv] at hcvAdd
  push_cast at hcvAdd
  have hceAdd:=hce
  dsimp only [ce] at hceAdd
  push_cast at hceAdd
  have hwkAdd:=hwk
  dsimp only [work] at hwkAdd
  push_cast at hwkAdd
  have hnword : (n:ℤ)≤ lim.word := by
    have hh : n≤ work free n := by unfold work ce cv be bv ae av class2 class1 class0; omega
    exact hptr n hh
  have hrowEnd : row+6≤ lim.space := hrow.trans hsp
  have hparamsSpace : params<lim.space := by omega
  have hf0:= hfields 0 (by simp [ColorParameters.fields])
  have hf1:= hfields 1 (by simp [ColorParameters.fields])
  have hf2:= hfields 2 (by simp [ColorParameters.fields])
  have hf3:= hfields 3 (by simp [ColorParameters.fields])
  have hf4:= hfields 4 (by simp [ColorParameters.fields])
  have hf5:= hfields 5 (by simp [ColorParameters.fields])
  simp only [ColorParameters.fields,List.getElem_cons_zero,List.getElem_cons_succ,add_zero] at hf0 hf1 hf2 hf3 hf4 hf5
  have hrow1 : ((row:ℤ)+1).toNat=row+1 :=by omega
  have hrow2 : ((row:ℤ)+2).toNat=row+2 :=by omega
  have hrow3 : ((row:ℤ)+3).toNat=row+3 :=by omega
  have hrow4 : ((row:ℤ)+4).toNat=row+4 :=by omega
  have hrow5 : ((row:ℤ)+5).toNat=row+5 :=by omega
  have hCall:= R.meets (d:= d+1) (src:= src) (colors:= free)
    (dst0:= class0 free n) (dst1:= class1 free n) (dst2:= class2 free n)
    (g:= n) (av:= av free n) (ae:= ae free n) (bv:= bv free n) (be:= be free n)
    (cv:= cv free n) (ce:= ce free n) (work:= work free n)
    p x hw (width_sufficient n) hn hsrc le_rfl le_rfl le_rfl le_rfl le_rfl le_rfl
    le_rfl le_rfl le_rfl le_rfl hspace hbandWord (by unfold depth at hd; omega) hinput hbound
  have hD : d+1≤lim.depth :=by unfold depth LightColorBands.depth at hd; omega
  have hbitsCast : (Scales.inputBits n:ℤ)+1=(width n:ℤ) :=by simp [width]
  apply Meets.of_body hmain
  unfold body time
  light_set (width n:ℕ) using hbits,hbitsCast,LightColorBands.time
  light_set (class0 free n:ℕ) using class0,LightColorBands.time
  light_set (class1 free n:ℕ) using class1,LightColorBands.time
  light_set (class2 free n:ℕ) using class2,LightColorBands.time
  light_set (av free n:ℕ) using av,LightColorBands.time
  light_set (ae free n:ℕ) using ae,LightColorBands.time
  light_set (bv free n:ℕ) using bv,LightColorBands.time
  light_set (be free n:ℕ) using be,LightColorBands.time
  light_set (cv free n:ℕ) using cv,LightColorBands.time
  light_set (ce free n:ℕ) using ce,LightColorBands.time
  light_set (work free n:ℕ) using work,LightColorBands.time
  light_call hCall using hf0,hf1,hf2,hf3,hf4,hf5,hrow1,hrow2,hrow3,hrow4,hrow5,LightColorBands.time
    with result ν ⟨hout,hkeep⟩
  obtain ⟨A,hsA,B,hsB,C,hsC,hr,hA,hB,hC,htables⟩:= hout
  have hAL : A.length≤ n := hA.2.1.trans (length_classList_le p x 0 1)
  have hBL : B.length≤ n := hB.2.1.trans (length_classList_le p x 1 1)
  have hCL : C.length≤ n := hC.2.1.trans (length_classList_le p x 2 (-1))
  have hAH:= hA.2.2.2.1
  have hBH:= hB.2.2.2.1
  have hCH:= hC.2.2.2.1
  have hAWord : (A.length:ℤ)≤ lim.word := (Int.ofNat_le.mpr hAL).trans hnword
  have hBWord : (B.length:ℤ)≤ lim.word := (Int.ofNat_le.mpr hBL).trans hnword
  have hCWord : (C.length:ℤ)≤ lim.word := (Int.ofNat_le.mpr hCL).trans hnword
  have hheaderAv : free+7≤ av free n := by unfold av class2 class1 class0; omega
  have hheaderSpace : free+7≤lim.space :=by
    unfold work ce cv be bv ae av class2 class1 class0 at hWork
    omega
  have hAeSpace : free+7≤ae free n :=by unfold ae; omega
  have hBeSpace : free+7≤be free n :=by unfold be bv ae; omega
  have hCeSpace : free+7≤ce free n :=by unfold ce cv be bv ae; omega
  have hAeReadSpace : ae free n<lim.space :=by
    have hh:=hWork; unfold work ce cv be bv at hh; omega
  have hBeReadSpace : be free n<lim.space :=by
    have hh:=hWork; unfold work ce cv at hh; omega
  have hCeReadSpace : ce free n<lim.space :=by
    have hh:=hWork; unfold work at hh; omega
  have hAeNe (k : ℕ) (hk : k<7) : ae free n≠free+k :=by omega
  have hBeNe (k : ℕ) (hk : k<7) : be free n≠free+k :=by omega
  have hCeNe (k : ℕ) (hk : k<7) : ce free n≠free+k :=by omega
  light_set (A.length:ℕ) using hAH,LightColorBands.time
  light_set (B.length:ℕ) using hBH,LightColorBands.time
  light_set (C.length:ℕ) using hCH,LightColorBands.time
  light_store free (av free n) using LightColorBands.time
  light_store (free+1) A.length using LightColorBands.time
  light_store (free+2) (bv free n) using LightColorBands.time
  light_store (free+3) B.length using LightColorBands.time
  light_store (free+4) (cv free n) using LightColorBands.time
  light_store (free+5) C.length using LightColorBands.time
  light_store (free+6) (work free n) using LightColorBands.time
  light_set (free:ℕ) using LightColorBands.time
  refine ⟨rfl,?_,A,B,C,?_,?_,?_,?_⟩
  · light_keep
  · simp [header,seg_cons,Nat.add_assoc]
  all_goals
    refine ⟨?_,by assumption,by assumption,?_⟩
    · intro i hi
      first
      | simpa only [Function.update_of_ne (by omega : av free n+i≠ free+6),
          Function.update_of_ne (by omega : av free n+i≠ free+5),Function.update_of_ne (by omega : av free n+i≠ free+4),
          Function.update_of_ne (by omega : av free n+i≠ free+3),Function.update_of_ne (by omega : av free n+i≠ free+2),
          Function.update_of_ne (by omega : av free n+i≠ free+1),Function.update_of_ne (by omega : av free n+i≠ free)] using hA.1 i hi
      | have hsep : free+7≤ bv free n := by unfold bv ae; omega
        simpa only [Function.update_of_ne (by omega : bv free n+i≠ free+6),
          Function.update_of_ne (by omega : bv free n+i≠ free+5),Function.update_of_ne (by omega : bv free n+i≠ free+4),
          Function.update_of_ne (by omega : bv free n+i≠ free+3),Function.update_of_ne (by omega : bv free n+i≠ free+2),
          Function.update_of_ne (by omega : bv free n+i≠ free+1),Function.update_of_ne (by omega : bv free n+i≠ free)] using hB.1 i hi
      | have hsep : free+7≤ cv free n := by unfold cv be bv ae; omega
        simpa only [Function.update_of_ne (by omega : cv free n+i≠ free+6),
          Function.update_of_ne (by omega : cv free n+i≠ free+5),Function.update_of_ne (by omega : cv free n+i≠ free+4),
          Function.update_of_ne (by omega : cv free n+i≠ free+3),Function.update_of_ne (by omega : cv free n+i≠ free+2),
          Function.update_of_ne (by omega : cv free n+i≠ free+1),Function.update_of_ne (by omega : cv free n+i≠ free)] using hC.1 i hi
    · first | exact hA.2.2.1 | exact hB.2.2.1 | exact hC.2.2.1

def program : Program := LightColorBands.program++[body 20]
@[simp] theorem program_length : program.length=28 :=rfl
def library : LightColorBands.Procs program 20 where
  pClasses:= 21
  pBands:= 0
  classes:= ⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
  bands:= {
    pPrepare:= 1
    pEnumerate:= 12
    prepare:= ⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
    enumerate:= ⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
    main:= rfl }
  main:= rfl

theorem program_meets {src n params row free U d : ℕ}
    (μ : ℕ→ ℤ) (p : Coloring.Parameter (width n)) (x : Fin n→ ℤ)
    (hn : 0<n) (hsrc : src+n≤ free) (hparams : params+19≤ free) (hrow : row+6≤ free)
    (hw : (lim.space:ℤ)≤ lim.word) (hspace : space free n≤ lim.space)
    (hword : (word n U:ℤ)≤ lim.word) (hd : d+depth n≤ lim.depth)
    (hbits : μ params=(Scales.inputBits n:ℤ))
    (hfields : Seg μ row (ColorParameters.fields p))
    (hinput : Seg μ src (List.ofFn x)) (hbound : ∀ i, |x i|≤ (U:ℤ)) :
    Meets lim program 27 d [src,n,params,row,free] μ (time n) (fun r ν=>Output μ ν free p x r) :=
  meets rfl library μ p x hn hsrc hparams hrow hw hspace hword hd hbits hfields hinput hbound

theorem Normalized.nodup {μ : ℕ→ℤ} {base n : ℕ} {original L : List ℤ}
    (H : Normalized μ base n original L) : L.Nodup :=
  List.nodup_iff_pairwise_ne.mpr (H.sorted.imp (fun h=>ne_of_lt h))

theorem Normalized.keep {μ ν : ℕ→ℤ} {base n cut : ℕ} {original L : List ℤ}
    (H : Normalized μ base n original L) (hk : Kept μ ν cut) (hb : base+n≤cut) :
    Normalized ν base n original L :=
  {H with seg:=fun i hi=>(hk (base+i) (by have hh:=H.length; omega)).trans (H.seg i hi)}

theorem Normalized.bounded {μ : ℕ→ℤ} {base n U : ℕ} {original L : List ℤ}
    (H : Normalized μ base n original L) (hb : ∀ z∈original, |z|≤(U:ℤ)) :
    ∀ z∈L, |z|≤(U:ℤ) :=fun z hz=>hb z ((H.mem z).mp hz)

theorem header_reads {μ : ℕ→ℤ} {free n : ℕ} {A B C : List ℤ}
    (H : Seg μ free (header free n A B C)) :
    μ free=(av free n:ℤ) ∧ μ (free+1)=(A.length:ℤ) ∧
    μ (free+2)=(bv free n:ℤ) ∧ μ (free+3)=(B.length:ℤ) ∧
    μ (free+4)=(cv free n:ℤ) ∧ μ (free+5)=(C.length:ℤ) ∧
    μ (free+6)=(work free n:ℤ) :=by
  have h0:=H 0 (by simp [header])
  have h1:=H 1 (by simp [header])
  have h2:=H 2 (by simp [header])
  have h3:=H 3 (by simp [header])
  have h4:=H 4 (by simp [header])
  have h5:=H 5 (by simp [header])
  have h6:=H 6 (by simp [header])
  exact ⟨by simpa [header] using h0,by simpa [header] using h1,
    by simpa [header] using h2,by simpa [header] using h3,by simpa [header] using h4,
    by simpa [header] using h5,by simpa [header] using h6⟩

def witness (A B C : List ℤ) : Prop :=∃ a∈A, ∃ b∈B, ∃ c∈C, c-b=a

theorem witness_iff {n : ℕ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : Normalized μ ab n (classList p x 0 1) A)
    (hB : Normalized μ bb n (classList p x 1 1) B)
    (hC : Normalized μ cb n (classList p x 2 (-1)) C) :
    witness A B C↔ColorClassLists.witness p x :=by
  unfold witness ColorClassLists.witness
  constructor
  · rintro ⟨a,ha,b,hb,c,hc,he⟩
    exact ⟨a,(hA.mem a).mp ha,b,(hB.mem b).mp hb,c,(hC.mem c).mp hc,by omega⟩
  · rintro ⟨a,ha,b,hb,c,hc,he⟩
    exact ⟨a,(hA.mem a).mpr ha,b,(hB.mem b).mpr hb,c,(hC.mem c).mpr hc,by omega⟩

/-- Any witness in the physically normalized arrays comes from three
different original positions, even when original input values repeat. -/
theorem witness_positions {n : ℕ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : Normalized μ ab n (classList p x 0 1) A)
    (hB : Normalized μ bb n (classList p x 1 1) B)
    (hC : Normalized μ cb n (classList p x 2 (-1)) C)
    {a b c : ℤ} (ha : a∈A) (hb : b∈B) (hc : c∈C) (he : c-b=a) :
    ∃ i j k : Fin n, i≠j ∧ i≠k ∧ j≠k ∧ x i=a ∧ x j=b ∧ -x k=c ∧ x i+x j+x k=0 :=by
  have ha':=(ColorClassLists.mem_classList p x (0:Fin 3) a).mp ((hA.mem a).mp ha)
  have hb':=(ColorClassLists.mem_classList p x (1:Fin 3) b).mp ((hB.mem b).mp hb)
  have hc':=(ColorClassLists.mem_negClassList p x c).mp ((hC.mem c).mp hc)
  obtain ⟨i,hi,hxi⟩:=(Coloring.mem_values x (indexColor p) 0 a).mp ha'
  obtain ⟨j,hj,hxj⟩:=(Coloring.mem_values x (indexColor p) 1 b).mp hb'
  obtain ⟨k,hk,hxk⟩:=(Coloring.mem_negValues x (indexColor p) c).mp hc'
  refine ⟨i,j,k,?_,?_,?_,hxi,hxj,hxk,?_⟩
  · intro hh; subst j; simp_all
  · intro hh; subst k; simp_all
  · intro hh; subst k; simp_all
  · omega

theorem witness_sound {n : ℕ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    {μ : ℕ→ℤ} {ab bb cb : ℕ} {A B C : List ℤ}
    (hA : Normalized μ ab n (classList p x 0 1) A)
    (hB : Normalized μ bb n (classList p x 1 1) B)
    (hC : Normalized μ cb n (classList p x 2 (-1)) C)
    (H : witness A B C) : Coloring.DistinctZeroSum x :=by
  obtain ⟨a,ha,b,hb,c,hc,he⟩:=H
  obtain ⟨i,j,k,hij,hik,hjk,_,_,_,hsum⟩:=witness_positions hA hB hC ha hb hc he
  exact ⟨i,j,k,hij,hik,hjk,hsum⟩

end ThreeSum.LightTernaryColorPrelude
