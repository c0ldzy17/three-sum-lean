import Submission.ThreeSum.TernaryColorPreparationLayout

/-! Execution of the complete color preparation library. All procedure
receipts below are obtained from the included concrete kernels. -/
namespace ThreeSum.LightTernaryColorPreparationProof
open Light LightTernaryColorPreparation
open LightColorParametersCosts
set_option maxHeartbeats 12000000
set_option maxRecDepth 24000

private def colorLibrary (radix : ℕ) : LightColorBands.Procs (program radix) 20 where
  pClasses:=21
  pBands:=0
  classes:=⟨22,23,24,25,26,rfl,rfl,rfl,rfl,rfl,rfl⟩
  bands:={
    pPrepare:=1
    pEnumerate:=12
    prepare:=⟨2,8,9,10,11,⟨3,4,5,6,7,⟨rfl,rfl,rfl,rfl⟩,rfl,rfl⟩,rfl,rfl,rfl,rfl,rfl⟩
    enumerate:=⟨13,⟨14,15,16,17,18,19,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩,rfl⟩
    main:=rfl }
  main:=rfl

private def leftProcs (radix : ℕ) :
    LightTernarySignedMatrix.Procs (program radix) 28 false :=
  ⟨29,⟨30,31,rfl,rfl,rfl⟩,rfl⟩
private def rightProcs (radix : ℕ) :
    LightTernarySignedMatrix.Procs (program radix) 32 true :=
  ⟨33,⟨34,35,rfl,rfl,rfl⟩,rfl⟩
private def requesterProcs (radix : ℕ) :
    LightTernaryRequesterMatrix.Procs (program radix) 49 where
  inner:=48
  requester:=42
  mainBody:=rfl
  innerBody:=rfl
  requesterProcs:={
    pRow:=43,pApply:=46,pLinear:=47,
    row:=⟨44,45,rfl,rfl,rfl⟩,
    correction:=rfl,linear:=rfl,main:=rfl }

private def patch (base : ℕ) (loc : ℕ→ℤ) : (ℕ→ℤ)→ℕ→List ℕ→(ℕ→ℤ)
  | μ,_,[]=>μ
  | μ,offset,r::rs=>patch base loc (Function.update μ (base+offset) (loc r)) (offset+1) rs

private theorem stores_ends {lim : Limits} {P : Program} {d base offset : ℕ}
    (rs : List ℕ) (loc μ : ℕ→ℤ) (hbase : loc 18=(base:ℤ))
    (hw : (lim.space:ℤ)≤lim.word) (hs : base+offset+rs.length≤lim.space)
    (hfit : ∀r∈rs, |loc r|≤lim.word) :
    Ends lim P d (stores offset rs) ⟨loc,μ⟩ (10*rs.length)
      (fun σ=>σ.loc=loc ∧ σ.mem=patch base loc μ offset rs) :=by
  induction rs generalizing μ offset with
  | nil=>exact Ends.skip ⟨rfl,rfl⟩
  | cons r rs ih=>
    have hr:=hfit r (by simp)
    have hr' : |loc r|≤lim.word :=hr
    have ha : base+offset<lim.space :=by simp only [List.length_cons] at hs; omega
    have haZ : (base:ℤ)+(offset:ℤ)≤lim.word :=by
      exact_mod_cast (Int.ofNat_le.mpr ha.le).trans hw
    have ha0 : 0≤(base:ℤ)+(offset:ℤ) :=by positivity
    have haa : lim.Addr ((base:ℤ)+(offset:ℤ)) :=by constructor; positivity; exact_mod_cast ha
    simp only [stores,List.length_cons]
    refine Ends.seq 10 (10*rs.length) ?_ (by omega)
    refine Ends.storeLast ?_ (hs:=by light_side [hbase]) (hT:=by light_time)
    have hcast : ((base:ℤ)+(offset:ℤ)).toNat=base+offset :=by omega
    simpa only [v,k,Expr.val,Op.eval,hbase,hcast,patch] using
      ih (offset:=offset+1) (Function.update μ (base+offset) (loc r)) (by simp only [List.length_cons] at hs; omega)
        (fun r hr=>hfit r (by simp [hr]))

private theorem patch_outside (base offset : ℕ) (loc μ : ℕ→ℤ) (rs : List ℕ) :
    SameOutside μ (patch base loc μ offset rs) (base+offset) rs.length :=by
  induction rs generalizing μ offset with
  | nil=>exact SameOutside.refl
  | cons r rs ih=>
    intro a ha
    have hh:=ih (offset+1) (Function.update μ (base+offset) (loc r)) a
      (by simp only [List.length_cons] at ha; omega)
    exact hh.trans (Function.update_of_ne (by simp only [List.length_cons] at ha; omega) _ _)

private theorem patch_read (base offset : ℕ) (loc μ : ℕ→ℤ) (rs : List ℕ) :
    Seg (patch base loc μ offset rs) (base+offset) (rs.map loc) :=by
  induction rs generalizing μ offset with
  | nil=>intro i hi; simp at hi
  | cons r rs ih=>
    apply seg_cons.mpr
    constructor
    · have hh:=patch_outside base (offset+1) loc (Function.update μ (base+offset) (loc r)) rs
      have h:=hh (base+offset) (Or.inl (by omega))
      simpa [patch] using h
    · simpa only [patch,Nat.add_assoc] using ih (offset+1) (Function.update μ (base+offset) (loc r))

/-- Boundaries for the genuine kernel programs; there are no execution
callbacks in the color-preparation contract. -/
structure Bounds (lim : Limits) (radix n U J depth : ℕ) : Prop where
  hw : (lim.space:ℤ)≤lim.word
  colorWord : (LightTernaryColorPrelude.word n U:ℤ)≤lim.word
  matrixWord : (LightTernarySignedMatrix.word U radix J:ℤ)≤lim.word
  carryWord : (LightTernaryCarryCodes.word J (2^J):ℤ)≤lim.word
  colorDepth : depth+1+LightTernaryColorPrelude.depth n≤lim.depth
  kernelDepth : depth+7<lim.depth


def header (free n U R J q menu : ℕ) (A B C : List ℤ) : List ℤ :=
  let W:=width n
  [LightTernaryColorPrelude.av free n,A.length,
    LightTernaryColorPrelude.bv free n,B.length,
    LightTernaryColorPrelude.cv free n,C.length,
    bMatrix free n W,cMatrix free n W B.length J,
    oMatrix free n W A.length B.length C.length J,A.length*2^J,
    positions free n W A.length B.length C.length J,
    carry free n W A.length B.length C.length J,
    work free n W A.length B.length C.length J,
    arenaFree free n W A.length B.length C.length J U,U,R,J,q,menu]

structure Matrices (ν : ℕ→ℤ) (free n U J radix : ℕ) (A B C : List ℤ) : Prop where
  left : LightTernarySignedMatrix.Rows ν (bMatrix free n (width n)) B.length J
    (fun i=>TernarySignedReduction.leftRaw U radix J (B.getD i 0))
  right : LightTernarySignedMatrix.Rows ν (cMatrix free n (width n) B.length J) C.length J
    (fun i=>TernarySignedReduction.rightRaw U radix J (C.getD i 0))
  carries : LightTernaryCarryCodes.Table ν
    (carry free n (width n) A.length B.length C.length J) J (2^J)
  requesters : LightTernaryRequesterMatrix.Entries ν
    (positions free n (width n) A.length B.length C.length J)
    (oMatrix free n (width n) A.length B.length C.length J)
    J (2^J) (A.length*2^J) U radix (fun i=>A.getD i 0)

def buildTime (a b c J U : ℕ) :=
  LightNatPower.time J+LightTernarySignedMatrix.time b J U+
    LightTernarySignedMatrix.time c J U+LightTernaryCarryCodes.time J+
    LightTernaryRequesterMatrix.time a (2^J) J U+5000

def time (n J U : ℕ) :=LightTernaryColorPrelude.time n+buildTime n n n J U+5000

private theorem normalized_read {μ : ℕ→ℤ} {base n : ℕ} {original L : List ℤ}
    (H : LightTernaryColorPrelude.Normalized μ base n original L) :
    ∀i<L.length, μ (base+i)=L.getD i 0 :=by
  intro i hi
  simpa only [List.getD_eq_getElem _ _ hi] using H.seg i hi

private theorem list_abs {L : List ℤ} {U : ℕ} (H : ∀z∈L, |z|≤(U:ℤ)) :
    ∀i<L.length, |L.getD i 0|≤(U:ℤ) :=by
  intro i hi
  rw [List.getD_eq_getElem _ _ hi]
  exact H _ (List.getElem_mem hi)

private theorem rows_keep {μ ν : ℕ→ℤ} {dst n J cut : ℕ}
    {f : ℕ→TernarySignedReduction.Coordinate J→ℤ}
    (H : LightTernarySignedMatrix.Rows μ dst n J f) (K : Kept μ ν cut)
    (hs : dst+n*(J+2)≤cut) : LightTernarySignedMatrix.Rows ν dst n J f :=by
  intro i hi
  apply LightTernarySignedMatrix.row_keep (H i hi) K
  have hh:=Nat.mul_le_mul_right (J+2) (show i+1≤n by omega)
  rw [Nat.add_mul] at hh; simp only [one_mul] at hh; omega

private theorem table_keep {μ ν : ℕ→ℤ} {dst J Q cut : ℕ}
    (H : LightTernaryCarryCodes.Table μ dst J Q) (K : Kept μ ν cut)
    (hs : dst+Q*(J+1)≤cut) : LightTernaryCarryCodes.Table ν dst J Q :=by
  intro q hq
  have hh:=Nat.mul_le_mul_right (J+1) (show q+1≤Q by omega)
  rw [Nat.add_mul] at hh; simp only [one_mul] at hh
  refine ⟨(K _ (by omega)).trans (H q hq).1,?_⟩
  intro j hj
  exact (K _ (by omega)).trans ((H q hq).2 j hj)

private theorem matrices_outside {μ ν : ℕ→ℤ} {free n U J radix : ℕ} {A B C : List ℤ}
    (H : Matrices μ free n U J radix A B C)
    (K : SameOutside μ ν (headerAt free n (width n)) 19) :
    Matrices ν free n U J radix A B C :=by
  have kb (a : ℕ) (ha : bMatrix free n (width n)≤a) : ν a=μ a :=
    K a (Or.inr (by dsimp [bMatrix] at ha; omega))
  refine ⟨?_,?_,?_,?_⟩
  · intro i hi
    rcases H.left i hi with ⟨hd,h0,h1⟩
    refine ⟨fun j=>(kb _ (by omega)).trans (hd j),
      (kb _ (by omega)).trans h0,(kb _ (by omega)).trans h1⟩
  · intro i hi
    rcases H.right i hi with ⟨hd,h0,h1⟩
    have hc : bMatrix free n (width n)≤cMatrix free n (width n) B.length J :=by unfold cMatrix; omega
    refine ⟨fun j=>(kb _ (by omega)).trans (hd j),
      (kb _ (by omega)).trans h0,(kb _ (by omega)).trans h1⟩
  · intro q hq
    rcases H.carries q hq with ⟨h0,hd⟩
    have hc : bMatrix free n (width n)≤carry free n (width n) A.length B.length C.length J :=by unfold carry cMatrix; omega
    refine ⟨(kb _ (by omega)).trans h0,fun j hj=>(kb _ (by have:=Nat.zero_le (2^J); omega)).trans (hd j hj)⟩
  · intro r hr
    rcases H.requesters r hr with ⟨⟨hd,h0,h1⟩,hp⟩
    have hp0 : bMatrix free n (width n)≤positions free n (width n) A.length B.length C.length J :=by unfold positions carry cMatrix; omega
    have hm0 : positions free n (width n) A.length B.length C.length J≤oMatrix free n (width n) A.length B.length C.length J :=by unfold oMatrix; omega
    refine ⟨⟨fun j=>(kb _ (by omega)).trans (hd j),
      (kb _ (by omega)).trans h0,(kb _ (by omega)).trans h1⟩,
      (kb _ (by omega)).trans hp⟩

structure Built (μ ν : ℕ→ℤ) (free n U R J q menu radix : ℕ) (A B C : List ℤ) : Prop where
  kept : Kept μ ν (headerAt free n (width n))
  header : Seg ν (headerAt free n (width n)) (header free n U R J q menu A B C)
  matrices : Matrices ν free n U J radix A B C

/-- The nonempty branch executes both signed source matrices, the full carry
menu and every original-position requester, then writes its runtime header. -/
theorem build_ends {lim : Limits} {radix n U R J q menu depth src params row free : ℕ}
    (μ : ℕ→ℤ) (A B C : List ℤ) (hb : 1<radix)
    (bounds : Bounds lim radix n U J depth)
    (hparams : params+19≤free) (hparams9 : 9≤params)
    (hspace : arenaFree free n (width n) A.length B.length C.length J U≤lim.space)
    (hR : (R:ℤ)≤lim.word) (hq : (q:ℤ)≤lim.word) (hmenu : (menu:ℤ)≤lim.word)
    (hUread : μ (params-9)=(U:ℤ)) (hRread : μ (params-8)=(R:ℤ))
    (hJread : μ (params-7)=(J:ℤ)) (hqread : μ (params-5)=(q:ℤ))
    (hmenuread : μ (params-3)=(menu:ℤ)) (hbits : μ params=(Scales.inputBits n:ℤ))
    (hAread : ∀i<A.length, μ (LightTernaryColorPrelude.av free n+i)=A.getD i 0)
    (hBread : ∀i<B.length, μ (LightTernaryColorPrelude.bv free n+i)=B.getD i 0)
    (hCread : ∀i<C.length, μ (LightTernaryColorPrelude.cv free n+i)=C.getD i 0)
    (hA : ∀z∈A, |z|≤(U:ℤ)) (hB : ∀z∈B, |z|≤(U:ℤ)) (hC : ∀z∈C, |z|≤(U:ℤ))
    (ha : A.length≤n) (hbLen : B.length≤n) (hc : C.length≤n) :
    Ends lim (program radix) depth (buildBody radix)
      ⟨frame [src,n,params,row,free,free,LightTernaryColorPrelude.av free n,A.length,
        LightTernaryColorPrelude.bv free n,B.length,LightTernaryColorPrelude.cv free n,C.length],μ⟩
      (buildTime A.length B.length C.length J U)
      (fun σ=>σ.loc 0=(headerAt free n (width n):ℤ) ∧
        Built μ σ.mem free n U R J q menu radix A B C) :=by
  let W:=width n
  let H:=headerAt free n W
  let LB:=bMatrix free n W
  let LC:=cMatrix free n W B.length J
  let CC:=carry free n W A.length B.length C.length J
  let PP:=positions free n W A.length B.length C.length J
  let OO:=oMatrix free n W A.length B.length C.length J
  let WW:=work free n W A.length B.length C.length J
  let EE:=arenaFree free n W A.length B.length C.length J U
  have hE : EE≤lim.space :=hspace
  have hD : depth+1≤lim.depth :=by have:=bounds.kernelDepth; omega
  have horder : free≤H ∧ H+19=LB ∧ LB+B.length*(J+2)=LC ∧
      LC+C.length*(J+2)=CC ∧ CC+2^J*(J+1)=PP ∧ PP+A.length*2^J=OO ∧
      OO+A.length*2^J*(J+2)=WW ∧ WW≤EE :=by
    dsimp [H,LB,LC,CC,PP,OO,WW,EE,headerAt,bMatrix,cMatrix,carry,positions,oMatrix,work,arenaFree]
    omega
  have hav : LightTernaryColorPrelude.av free n+n≤H :=by
    dsimp [H,headerAt]
    unfold LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
      LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0
    omega
  have hbv : LightTernaryColorPrelude.bv free n+n≤H :=by
    dsimp [H,headerAt]
    unfold LightTernaryColorPrelude.bv LightTernaryColorPrelude.ae LightTernaryColorPrelude.av
      LightTernaryColorPrelude.class2 LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0
    omega
  have hcv : LightTernaryColorPrelude.cv free n+n≤H :=by
    dsimp [H,headerAt]
    unfold LightTernaryColorPrelude.cv LightTernaryColorPrelude.be LightTernaryColorPrelude.bv
      LightTernaryColorPrelude.ae LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
      LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0
    omega
  have hdiv:=TernaryColorPreparationLayout.division_space free n W A.length B.length C.length J U
  have hmatrixSpace : LightTernarySignedMatrix.space WW U≤lim.space :=hdiv.1.trans hspace
  have hcarrySpace : LightTernaryCarryCodes.space WW (2^J)≤lim.space :=hdiv.2.trans hspace
  have hp (a : ℕ) (h : a≤EE) : (a:ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (h.trans hE)).trans bounds.hw
  have hH:=hp H (by omega)
  have hLB:=hp LB (by omega)
  have hLC:=hp LC (by omega)
  have hCC:=hp CC (by omega)
  have hPP:=hp PP (by omega)
  have hOO:=hp OO (by omega)
  have hWW:=hp WW (by omega)
  have hEE:=hp EE le_rfl
  have hn:=hp n (by dsimp [H,headerAt] at horder; omega)
  have hW:=hp W (by dsimp [H,headerAt] at horder; omega)
  have hQ : ((2^J:ℕ):ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold LightTernaryCarryCodes.word LightOutputDecodeDigits.word; omega)).trans bounds.carryWord
  have hJ : (J:ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold LightTernarySignedMatrix.word LightTernarySignedRow.word LightOutputDecodeDigits.word; omega)).trans bounds.matrixWord
  have hU : (U:ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold LightTernarySignedMatrix.word LightTernarySignedRow.word LightOutputDecodeDigits.word; omega)).trans bounds.matrixWord
  have hradix : (radix:ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (by unfold LightTernarySignedMatrix.word LightTernarySignedRow.word LightOutputDecodeDigits.word; omega)).trans bounds.matrixWord
  have h2 : (2:ℤ)≤lim.word :=by
    have hh:=hp 2 (by dsimp [EE,arenaFree]; omega)
    exact hh
  have hpow (i : ℕ) (hi : i≤J) : ((2^i:ℕ):ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hQ
  have hmetadata (c : ℕ) (hc : c≤9) : ((params:ℤ)-(c:ℤ)).toNat=params-c :=by omega
  have hadd9 : ((params:ℤ)-9).toNat=params-9 :=by omega
  have hadd8 : ((params:ℤ)-8).toNat=params-8 :=by omega
  have hadd7 : ((params:ℤ)-7).toNat=params-7 :=by omega
  have hadd5 : ((params:ℤ)-5).toNat=params-5 :=by omega
  have hadd3 : ((params:ℤ)-3).toNat=params-3 :=by omega
  have hmetadataSpace (c : ℕ) (hc : c≤9) : params-c<lim.space :=by omega
  have hWread : μ params+1=(W:ℤ) :=by simp [hbits,W,width]
  have hQ0 : (0:ℤ)≤(2:ℤ)^J :=by positivity
  have hAL : (A.length:ℤ)≤lim.word :=(Int.ofNat_le.mpr ha).trans hn
  have hBL : (B.length:ℤ)≤lim.word :=(Int.ofNat_le.mpr hbLen).trans hn
  have hCL : (C.length:ℤ)≤lim.word :=(Int.ofNat_le.mpr hc).trans hn
  have hreq:=hp (A.length*2^J) (by omega)
  have hcalcH : (free:ℤ)+100*((n:ℤ)+(W:ℤ)+1)≤lim.word :=by
    simpa [H,headerAt] using hH
  have hcalcLC : (LB:ℤ)+(B.length:ℤ)*((J:ℤ)+2)≤lim.word :=by
    simpa [LC,cMatrix,LB] using hLC
  have hcalcCC : (LC:ℤ)+(C.length:ℤ)*((J:ℤ)+2)≤lim.word :=by simpa [CC,carry,LC] using hCC
  have hcalcPP : (CC:ℤ)+(2:ℤ)^J*((J:ℤ)+1)≤lim.word :=by simpa [PP,positions,CC] using hPP
  have hcalcOO : (PP:ℤ)+(A.length:ℤ)*(2:ℤ)^J≤lim.word :=by simpa [OO,oMatrix,PP] using hOO
  have hcalcWW : (OO:ℤ)+((A.length:ℤ)*(2:ℤ)^J)*((J:ℤ)+2)≤lim.word :=by simpa [WW,work,OO,Nat.cast_mul,Nat.cast_add,Nat.cast_pow] using hWW
  have hcalcEE : (WW:ℤ)+100*((U:ℤ)+(2:ℤ)^J+(J:ℤ)+1)≤lim.word :=by simpa [EE,arenaFree,WW] using hEE
  have hprodB0 : (0:ℤ)≤(B.length:ℤ)*((J:ℤ)+2) :=by positivity
  have hprodC0 : (0:ℤ)≤(C.length:ℤ)*((J:ℤ)+2) :=by positivity
  have hprodQ0 : (0:ℤ)≤(2:ℤ)^J*((J:ℤ)+1) :=by positivity
  have hprodA0 : (0:ℤ)≤(A.length:ℤ)*(2:ℤ)^J :=by positivity
  have hprodAQ0 : (0:ℤ)≤((A.length:ℤ)*(2:ℤ)^J)*((J:ℤ)+2) :=by positivity
  unfold buildBody buildTime
  light_set (U:ℕ) using hUread,hadd9,hmetadataSpace
  light_set (R:ℕ) using hRread,hadd8,hmetadataSpace
  light_set (J:ℕ) using hJread,hadd7,hmetadataSpace
  light_set (q:ℕ) using hqread,hadd5,hmetadataSpace
  light_set (menu:ℕ) using hmenuread,hadd3,hmetadataSpace
  light_set (W:ℕ) using hbits,hWread
  light_set (H:ℕ) using H,headerAt
  light_set (LB:ℕ) using LB,bMatrix,H
  light_set (LC:ℕ) using LC,cMatrix,LB
  light_call (LightNatPower.meets (d:=depth+1) (show (program radix)[37]?=some LightNatPower.body from rfl) μ hJ hpow)
    with powResult νp ⟨hPow,hmem⟩
  subst νp
  light_set (A.length*2^J:ℕ) using hPow
  light_set (CC:ℕ) using CC,carry,LC
  light_set (PP:ℕ) using hPow,PP,positions,CC
  light_set (OO:ℕ) using OO,oMatrix,PP
  light_set (WW:ℕ) using WW,work,OO
  light_set (EE:ℕ) using EE,arenaFree,WW,hPow
  have hleft:= (leftProcs radix).left_meets (d:=depth+1) (μ:=μ)
    (src:=LightTernaryColorPrelude.bv free n) (n:=B.length) (U:=U) (J:=J)
    (radix:=radix) (dst:=LB) (work:=WW) (fun i=>B.getD i 0)
    bounds.hw (by have:=bounds.kernelDepth; omega) hb.le (by omega) (by omega)
    hmatrixSpace bounds.matrixWord hBread (list_abs hB)
  light_call hleft using hPow with lret μL ⟨hLeft,kLeft⟩
  have hCread' : ∀i<C.length, μL (LightTernaryColorPrelude.cv free n+i)=C.getD i 0 :=by
    intro i hi; rw [kLeft _ (by omega),hCread i hi]
  have hright:= (rightProcs radix).right_meets (d:=depth+1) (μ:=μL)
    (src:=LightTernaryColorPrelude.cv free n) (n:=C.length) (U:=U) (J:=J)
    (radix:=radix) (dst:=LC) (work:=WW) (fun i=>C.getD i 0)
    bounds.hw (by have:=bounds.kernelDepth; omega) hb.le (by omega) (by omega)
    hmatrixSpace bounds.matrixWord hCread' (list_abs hC)
  light_call hright using hPow with rret μR ⟨hRight,kRight⟩
  have hcarry:=LightTernaryCarryCodes.meets (P:=program radix) (d:=depth+1) (μ:=μR)
    (pMain:=36) (pPower:=37) (pTable:=38) (pRow:=39) (pDecode:=40) (pDivide:=41)
    (J:=J) (dst:=CC) (work:=WW) rfl rfl rfl rfl rfl rfl bounds.hw
    (by have:=bounds.kernelDepth; omega) (by omega) hcarrySpace bounds.carryWord
  light_call hcarry using hPow with cret μT ⟨hCarryResult,hCarries,kCarry⟩
  have hAread' : ∀i<A.length, μT (LightTernaryColorPrelude.av free n+i)=A.getD i 0 :=by
    intro i hi
    rw [kCarry _ (by omega),kRight _ (by omega),kLeft _ (by omega),hAread i hi]
  have hrequest:= (requesterProcs radix).meets (depth:=depth+1)
    (src:=LightTernaryColorPrelude.av free n) (n:=A.length) (U:=U) (J:=J) (radix:=radix)
    (carry:=CC) (Q:=2^J) (positions:=PP) (matrix:=OO) (work:=WW)
    μT (fun i=>A.getD i 0) bounds.hw (by have:=bounds.kernelDepth; omega)
    hb (pow_pos (by decide) _) (by omega) (by omega) (by omega) (by omega)
    hmatrixSpace bounds.matrixWord hAread' (list_abs hA) hCarries
  light_call hrequest using hPow with oret μO ⟨hEntries,kRequest⟩
  have kAll : Kept μ μO LB :=by
    intro a ha
    rw [kRequest _ (by omega),kCarry _ (by omega),kRight _ (by omega),kLeft _ ha]
  have mat : Matrices μO free n U J radix A B C :=by
    refine ⟨?_,?_,?_,hEntries⟩
    · exact rows_keep (n:=B.length) (J:=J) (dst:=LB) (rows_keep (n:=B.length) (J:=J) (dst:=LB) (rows_keep (n:=B.length) (J:=J) (dst:=LB) hLeft kRight (by omega)) kCarry (by omega)) kRequest (by omega)
    · exact rows_keep (n:=C.length) (J:=J) (dst:=LC) (rows_keep (n:=C.length) (J:=J) (dst:=LC) hRight kCarry (by omega)) kRequest (by omega)
    · exact table_keep (J:=J) (Q:=2^J) (dst:=CC) hCarries kRequest (by omega)
  let loc:=frame [src,n,params,row,free,free,LightTernaryColorPrelude.av free n,A.length,
    LightTernaryColorPrelude.bv free n,B.length,LightTernaryColorPrelude.cv free n,C.length,
    U,R,J,q,menu,W,H,LB,LC,OO,powResult,A.length*2^J,PP,CC,WW,EE,oret]
  have havWord:=hp (LightTernaryColorPrelude.av free n) (by omega)
  have hbvWord:=hp (LightTernaryColorPrelude.bv free n) (by omega)
  have hcvWord:=hp (LightTernaryColorPrelude.cv free n) (by omega)
  have hloc : loc 18=(H:ℤ) :=by simp [loc]
  have hfits : ∀r∈fields, |loc r|≤lim.word :=by
    intro r hr
    simp only [fields,List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals simp only [loc,frame,List.getD_cons_zero,List.getD_cons_succ,Int.natCast_nonneg,abs_of_nonneg]
    all_goals try rw [abs_of_nonneg (by positivity)]
    all_goals first | assumption | simpa only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hreq | omega
  simp only [setLocal] at ⊢
  change Ends _ _ _ _ ⟨loc,μO⟩ _ _
  refine Ends.pieceThen (stores_ends fields loc μO hloc bounds.hw (by simpa [fields] using (show H+19≤lim.space by omega)) hfits) ?_
    (hT:=by norm_num [fields]; light_time)
  rintro ⟨loc',ν⟩ ⟨hloc',hν⟩
  dsimp only at hloc' hν
  subst loc'; subst ν
  light_set (H:ℕ) using loc,fields
  refine ⟨rfl,?_,?_,?_⟩
  · intro a ha
    have h:=patch_outside H 0 loc μO fields a (Or.inl (by simpa using ha))
    exact h.trans (kAll a (by change a<H at ha; omega))
  · have h:=patch_read H 0 loc μO fields
    simpa [fields,loc,header,W,H,LB,LC,OO,PP,CC,WW,EE] using h
  · exact matrices_outside mat (by simpa [fields] using patch_outside H 0 loc μO fields)


def space (free n J U : ℕ) :=arenaFree free n (width n) n n n J U

theorem arenaFree_mono (free n W J U a b c : ℕ) (ha : a≤n) (hb : b≤n) (hc : c≤n) :
    arenaFree free n W a b c J U≤arenaFree free n W n n n J U :=by
  have hb':=Nat.mul_le_mul_right (J+2) hb
  have hc':=Nat.mul_le_mul_right (J+2) hc
  have ha':=Nat.mul_le_mul_right (2^J) ha
  have ha'':=Nat.mul_le_mul_right (J+2) ha'
  unfold arenaFree work oMatrix positions carry cMatrix bMatrix
  omega

theorem buildTime_mono (n J U a b c : ℕ) (ha : a≤n) (hb : b≤n) (hc : c≤n) :
    buildTime a b c J U≤buildTime n n n J U :=by
  have hb':=Nat.mul_le_mul_right (LightTernarySignedRow.time J (3*U)+200) hb
  have hc':=Nat.mul_le_mul_right (LightTernarySignedRow.time J (3*U)+200) hc
  have ha':=Nat.mul_le_mul_right (LightTernaryRequesterMatrix.innerTime (2^J) J U+200) ha
  unfold buildTime LightTernarySignedMatrix.time LightTernaryRequesterMatrix.time
  omega

/-- A zero return certifies an empty normalized color class. A positive
return points to all nineteen initialized fields and all executed raw rows. -/
def Output {n : ℕ} (μ ν : ℕ→ℤ) (free U R J q menu radix : ℕ)
    (p : Coloring.Parameter (width n)) (x : Fin n→ℤ) (ret : ℤ) : Prop :=
  Kept μ ν free ∧ ∃A B C : List ℤ,
    LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.av free n) n
      (ColorClassLists.classList p x 0 1) A ∧
    LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.bv free n) n
      (ColorClassLists.classList p x 1 1) B ∧
    LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.cv free n) n
      (ColorClassLists.classList p x 2 (-1)) C ∧
    ((ret=0 ∧ (A=[] ∨ B=[] ∨ C=[])) ∨
      (ret=(headerAt free n (width n):ℤ) ∧ A≠[] ∧ B≠[] ∧ C≠[] ∧
        Seg ν (headerAt free n (width n)) (header free n U R J q menu A B C) ∧
        Matrices ν free n U J radix A B C))

private theorem class_abs {n : ℕ} (p : Coloring.Parameter (width n)) (x : Fin n→ℤ)
    {U : ℕ} (hx : ∀i, |x i|≤(U:ℤ)) :
    (∀z∈ColorClassLists.classList p x 0 1, |z|≤(U:ℤ)) ∧
    (∀z∈ColorClassLists.classList p x 1 1, |z|≤(U:ℤ)) ∧
    (∀z∈ColorClassLists.classList p x 2 (-1), |z|≤(U:ℤ)) :=by
  refine ⟨?_,?_,?_⟩
  · intro z hz
    have hz':=(ColorClassLists.mem_classList p x 0 z).mp hz
    rw [Coloring.mem_values] at hz'
    rcases hz' with ⟨i,_,rfl⟩
    exact hx i
  · intro z hz
    have hz':=(ColorClassLists.mem_classList p x 1 z).mp hz
    rw [Coloring.mem_values] at hz'
    rcases hz' with ⟨i,_,rfl⟩
    exact hx i
  · intro z hz
    have hz':=(ColorClassLists.mem_negClassList p x z).mp hz
    rw [Coloring.mem_negValues] at hz'
    rcases hz' with ⟨i,_,rfl⟩
    simpa only [abs_neg] using hx i

/-- Closed execution of the color-preparation entry point. The assumptions
are scalar/array bounds and actual input memory, never a kernel receipt. -/
theorem meets {lim : Limits} {radix src n params row free U R J q menu depth : ℕ}
    (μ : ℕ→ℤ) (p : Coloring.Parameter (width n)) (x : Fin n→ℤ)
    (hn : 0<n) (hb : 1<radix) (bounds : Bounds lim radix n U J depth)
    (hsrc : src+n≤free) (hparams : params+19≤free) (hparams9 : 9≤params)
    (hrow : row+6≤free) (hspace : space free n J U≤lim.space)
    (hR : (R:ℤ)≤lim.word) (hq : (q:ℤ)≤lim.word) (hmenu : (menu:ℤ)≤lim.word)
    (hUread : μ (params-9)=(U:ℤ)) (hRread : μ (params-8)=(R:ℤ))
    (hJread : μ (params-7)=(J:ℤ)) (hqread : μ (params-5)=(q:ℤ))
    (hmenuread : μ (params-3)=(menu:ℤ)) (hbits : μ params=(Scales.inputBits n:ℤ))
    (hfields : Seg μ row (ColorParameters.fields p))
    (hinput : Seg μ src (List.ofFn x)) (hbound : ∀i, |x i|≤(U:ℤ)) :
    Meets lim (program radix) 50 depth [src,n,params,row,free] μ (time n J U)
      (fun ret ν=>Output μ ν free U R J q menu radix p x ret) :=by
  have hw : (lim.space:ℤ)≤lim.word :=bounds.hw
  have hHspace : headerAt free n (width n)≤lim.space :=by
    have hh:=hspace
    unfold space arenaFree work oMatrix positions carry cMatrix bMatrix at hh
    omega
  have hfree : free≤lim.space :=by unfold headerAt at hHspace; omega
  have hcolspace : LightTernaryColorPrelude.space free n≤lim.space :=
    (TernaryColorPreparationLayout.color_end hn le_rfl).trans hHspace
  have hC:=LightTernaryColorPrelude.meets (d:=depth+1)
    (show (program radix)[27]?=some (LightTernaryColorPrelude.body 20) from rfl)
    (colorLibrary radix) μ p x hn hsrc hparams hrow bounds.hw hcolspace
    bounds.colorWord bounds.colorDepth hbits hfields hinput hbound
  have hp (a : ℕ) (ha : a≤lim.space) : (a:ℤ)≤lim.word :=
    (Int.ofNat_le.mpr ha).trans bounds.hw
  have hnword : (n:ℤ)≤lim.word :=hp n (by unfold headerAt at hHspace; omega)
  have hfword : (free:ℤ)≤lim.word :=hp free hfree
  have hsrcword : (src:ℤ)≤lim.word :=hp src (by omega)
  have hparword : (params:ℤ)≤lim.word :=hp params (by omega)
  have hrword : (row:ℤ)≤lim.word :=hp row (by omega)
  have hD : depth+1≤lim.depth :=by have:=bounds.kernelDepth; omega
  apply Meets.of_body (show (program radix)[50]?=some (body radix) from rfl)
  unfold body time
  light_call hC with colorResult ν ⟨hret,hkeep,A,B,C,hheader,hA,hB,hC⟩
  subst colorResult
  obtain ⟨ha0,ha1,ha2,ha3,ha4,ha5,ha6⟩:=LightTernaryColorPrelude.header_reads hheader
  have hAS:=hA.length
  have hBS:=hB.length
  have hCS:=hC.length
  have hAW : (A.length:ℤ)≤lim.word :=(Int.ofNat_le.mpr hAS).trans hnword
  have hBW : (B.length:ℤ)≤lim.word :=(Int.ofNat_le.mpr hBS).trans hnword
  have hCW : (C.length:ℤ)≤lim.word :=(Int.ofNat_le.mpr hCS).trans hnword
  have hav : LightTernaryColorPrelude.av free n+n≤headerAt free n (width n) :=by
    unfold LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
      LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0 headerAt
    omega
  have hbv : LightTernaryColorPrelude.bv free n+n≤headerAt free n (width n) :=by
    unfold LightTernaryColorPrelude.bv LightTernaryColorPrelude.ae LightTernaryColorPrelude.av
      LightTernaryColorPrelude.class2 LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0 headerAt
    omega
  have hcv : LightTernaryColorPrelude.cv free n+n≤headerAt free n (width n) :=by
    unfold LightTernaryColorPrelude.cv LightTernaryColorPrelude.be LightTernaryColorPrelude.bv
      LightTernaryColorPrelude.ae LightTernaryColorPrelude.av LightTernaryColorPrelude.class2
      LightTernaryColorPrelude.class1 LightTernaryColorPrelude.class0 headerAt
    omega
  have havWord:=hp (LightTernaryColorPrelude.av free n) (by omega)
  have hbvWord:=hp (LightTernaryColorPrelude.bv free n) (by omega)
  have hcvWord:=hp (LightTernaryColorPrelude.cv free n) (by omega)
  have hheadspace : free+6≤lim.space :=by unfold headerAt at hHspace; omega
  have hadd (i : ℕ) : ((free:ℤ)+(i:ℤ)).toNat=free+i :=by omega
  have hadd1 : ((free:ℤ)+1).toNat=free+1 :=by omega
  have hadd2 : ((free:ℤ)+2).toNat=free+2 :=by omega
  have hadd3 : ((free:ℤ)+3).toNat=free+3 :=by omega
  have hadd4 : ((free:ℤ)+4).toNat=free+4 :=by omega
  have hadd5 : ((free:ℤ)+5).toNat=free+5 :=by omega
  light_set (LightTernaryColorPrelude.av free n:ℕ) using ha0
  light_set (A.length:ℕ) using ha0,ha1,ha2,ha3,ha4,ha5,hadd1,hadd2,hadd3,hadd4,hadd5
  light_set (LightTernaryColorPrelude.bv free n:ℕ) using ha0,ha1,ha2,ha3,ha4,ha5,hadd1,hadd2,hadd3,hadd4,hadd5
  light_set (B.length:ℕ) using ha0,ha1,ha2,ha3,ha4,ha5,hadd1,hadd2,hadd3,hadd4,hadd5
  light_set (LightTernaryColorPrelude.cv free n:ℕ) using ha0,ha1,ha2,ha3,ha4,ha5,hadd1,hadd2,hadd3,hadd4,hadd5
  light_set (C.length:ℕ) using ha0,ha1,ha2,ha3,ha4,ha5,hadd1,hadd2,hadd3,hadd4,hadd5
  light_if hAz hAn : (A.length:ℤ)=0
  · have he : A=[] :=by exact List.eq_nil_of_length_eq_zero (by exact_mod_cast hAz)
    light_set (0:ℕ)
    exact ⟨hkeep,A,B,C,hA,hB,hC,Or.inl ⟨rfl,Or.inl he⟩⟩
  · light_if hBz hBn : (B.length:ℤ)=0
    · have he : B=[] :=by exact List.eq_nil_of_length_eq_zero (by exact_mod_cast hBz)
      light_set (0:ℕ)
      exact ⟨hkeep,A,B,C,hA,hB,hC,Or.inl ⟨rfl,Or.inr (Or.inl he)⟩⟩
    · light_if hCz hCn : (C.length:ℤ)=0
      · have he : C=[] :=by exact List.eq_nil_of_length_eq_zero (by exact_mod_cast hCz)
        light_set (0:ℕ)
        exact ⟨hkeep,A,B,C,hA,hB,hC,Or.inl ⟨rfl,Or.inr (Or.inr he)⟩⟩
      · have hkmeta (c : ℕ) : ν (params-c)=μ (params-c) :=hkeep _ (by omega)
        obtain ⟨hxA,hxB,hxC⟩:=class_abs p x hbound
        have hBuild:=build_ends (src:=src) (params:=params) (row:=row) (free:=free) (depth:=depth) ν A B C hb bounds hparams hparams9
          ((arenaFree_mono free n (width n) J U A.length B.length C.length hAS hBS hCS).trans hspace)
          hR hq hmenu (by rw [hkmeta,hUread]) (by rw [hkmeta,hRread])
          (by rw [hkmeta,hJread]) (by rw [hkmeta,hqread]) (by rw [hkmeta,hmenuread])
          (by rw [hkeep _ (by omega),hbits])
          (normalized_read hA) (normalized_read hB) (normalized_read hC)
          (hA.bounded hxA) (hB.bounded hxB) (hC.bounded hxC) hAS hBS hCS
        have hbt:=buildTime_mono n J U A.length B.length C.length hAS hBS hCS
        simp only [setLocal] at ⊢
        refine Ends.pieceThen hBuild ?_ (hT:=by light_time)
        rintro σ ⟨hs,hbuilt⟩
        apply Ends.skip
        refine ⟨?_,A,B,C,hA.keep hbuilt.kept hav,hB.keep hbuilt.kept hbv,hC.keep hbuilt.kept hcv,Or.inr ?_⟩
        · intro a ha
          exact (hbuilt.kept a (by unfold headerAt; omega)).trans (hkeep a ha)
        · exact ⟨hs,(fun he=>hAn (by simp [he])),(fun he=>hBn (by simp [he])),
            (fun he=>hCn (by simp [he])),hbuilt.header,hbuilt.matrices⟩

@[simp] theorem header_length (free n U R J q menu : ℕ) (A B C : List ℤ) :
    (header free n U R J q menu A B C).length=19 :=rfl

/-- Skipping a zero-returned color is sound on the original input. -/
theorem Output.zero_no_witness {n free U R J q menu radix : ℕ}
    {μ ν : ℕ→ℤ} {p : Coloring.Parameter (width n)} {x : Fin n→ℤ}
    (H : Output μ ν free U R J q menu radix p x 0) :
    ¬ColorClassLists.witness p x :=by
  rcases H with ⟨_,A,B,C,hA,hB,hC,hcase⟩
  intro hw
  have hw':= (LightTernaryColorPrelude.witness_iff hA hB hC).mpr hw
  rcases hcase with ⟨_,he⟩|⟨hret,_⟩
  · rcases hw' with ⟨a,ha,b,hb,c,hc,_⟩
    rcases he with rfl|rfl|rfl <;> simp_all
  · have hn : 0<headerAt free n (width n) :=by unfold headerAt; omega
    exact (by exact_mod_cast hn : (0:ℤ)<(headerAt free n (width n):ℤ)).ne hret

end ThreeSum.LightTernaryColorPreparationProof
