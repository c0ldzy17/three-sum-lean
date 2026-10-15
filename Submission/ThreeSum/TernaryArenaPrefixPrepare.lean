import Submission.ThreeSum.TernaryPrefixSeedHeader
import Submission.ThreeSum.TernaryArenaSourceSetup
import Submission.ThreeSum.TernaryArenaSeedCandidate

noncomputable section
namespace ThreeSum.TernaryArenaPrefixPrepare
open Light TernaryLocalParameters TernaryJointType TernaryArenaLayout TernaryArenaSourceSetup
open LightTernaryPrefixStep
set_option maxHeartbeats 1000000
set_option maxRecDepth 24000

def inputs (p m F j J n U0 a b scale : ℕ) (I : Input)
    (Q : TernaryGoodOutputCatalog.Output m) : Inputs where
  m:=m
  F:=F
  p:=p
  seed:=addr I.free I.capacity 3
  template:=addr I.free I.capacity 0
  liveHeader:=addr I.free I.capacity 1
  prefixFree:=addr I.free I.capacity 13
  alpha2:=fixedAlpha m 2
  alphaRank:=alphaRank m
  localQ:=TernaryCodeSemantics.address Q.val
  radix:=4^(fixedLength m)
  J:=J
  a:=a
  b:=b
  scale:=scale
  j:=j
  power:=p^j
  Fbase:=addr I.free I.capacity 50
  Gbase:=addr I.free I.capacity 51
  xB:=p^j
  xC:=p^j
  xP:=a^j
  tB:=9^j*(n*n)
  tC:=9^j*(n*n)
  tP:=U0*(b*scale)^j

/-- Every value here is an arithmetic magnitude, with no absolute pointer. -/
def scalars (X : Inputs) : List ℕ :=
  [X.j+1,X.m,X.p,X.power,X.alpha2,X.alphaRank,X.localQ,X.radix,X.J,
   LightTernaryPrefixSetup.N X.m (X.j+1),LightTernaryPrefixSetup.T X.m (X.j+1),
   2*LightTernaryPrefixSetup.N X.m (X.j+1),X.F^(X.j+1),LightTernaryPrefixSetup.nb X.m (X.j+1),
   X.power*X.p,X.alpha2*(X.j+1),2^(X.alpha2*(X.j+1)),X.alphaRank*(X.j+1),
   (LightTernaryPrefixSetup.N X.m (X.j+1)+1)*LightTernaryPrefixSetup.nb X.m (X.j+1),
   LightTernaryPrefixSetup.N X.m (X.j+1)*LightTernaryPrefixSetup.nb X.m (X.j+1),
   2*(X.alphaRank*(X.j+1)),2*(X.alphaRank*(X.j+1))-LightTernaryPrefixSetup.T X.m (X.j+1)-1,
   LightTernaryRepeatWord.value X.localQ X.radix (X.j+1),
   X.xB*X.p,X.xC*X.p,X.xP*X.a,X.tB*9,X.tC*9,X.tP*X.b*X.scale,X.tP*X.b,9]

def footprint (X : Inputs) : ℕ :=4^(LightTernaryPrefixSetup.N X.m (X.j+1))+2*LightTernaryPrefixSetup.N X.m (X.j+1)+9

def envelope (X : Inputs) : ℕ :=
  106+LightTernaryPrefixSetup.word X.m (X.j+1) X.F+footprint X+(scalars X).sum

/-- A single polynomial arena capacity bounds all actual header arithmetic;
free can be arbitrarily large subject only to the original memory limit. -/
theorem ready {lim : Limits} {p m F j J n U0 a b scale depth : ℕ}
    (I : Input) (Q : TernaryGoodOutputCatalog.Output m) (μ : ℕ→ℤ)
    (hm : 0<m) (hw : (lim.space:ℤ)≤lim.word)
    (hcap : envelope (inputs p m F j J n U0 a b scale I Q)≤I.capacity)
    (hspace : finish I.free I.capacity≤lim.space)
    (hdepth : depth+LightTernaryPrefixSetup.N m (j+1)+5≤lim.depth)
    (hF : μ (addr I.free I.capacity 0+99)=(addr I.free I.capacity 50:ℤ))
    (hG : μ (addr I.free I.capacity 0+100)=(addr I.free I.capacity 51:ℤ))
    (hbudget : Seg μ (addr I.free I.capacity 3+41)
      (LightTernaryBudgetStep.oldValues (p^j) (p^j) (a^j) (9^j*(n*n)) (9^j*(n*n)) (U0*(b*scale)^j))) :
    PrepareReady (inputs p m F j J n U0 a b scale I Q) lim depth μ :=by
  let X:=inputs p m F j J n U0 a b scale I Q
  have h106 : 106≤I.capacity:=by unfold envelope at hcap;omega
  have hfp : footprint X≤I.capacity:=by change envelope X≤I.capacity at hcap;unfold envelope at hcap;omega
  have hpw : LightTernaryPrefixSetup.word m (j+1) F≤I.capacity:=by change envelope X≤I.capacity at hcap;unfold envelope at hcap;exact Nat.le_trans (by dsimp [X,inputs];omega) hcap
  have hsum : (scalars X).sum≤I.capacity:=by change envelope X≤I.capacity at hcap;unfold envelope at hcap;omega
  have hcspace : I.capacity≤lim.space:=by unfold finish addr slots at hspace;omega
  have hnum (z : ℕ) (hz : z∈scalars X) : z≤I.capacity:=
    (List.single_le_sum (fun x _=>Nat.zero_le x) z hz).trans hsum
  have hnumW (z : ℕ) (hz : z∈scalars X) : (z:ℤ)≤lim.word:=
    (Int.ofNat_le.mpr ((hnum z hz).trans hcspace)).trans hw
  have hscalarLength : (scalars X).length=31:=rfl
  have hnumIndex (i : ℕ) (hi : i<31) : (scalars X)[i]'(by omega)≤I.capacity:=
    hnum _ (List.getElem_mem (by omega))
  have hwordIndex (i : ℕ) (hi : i<31) : (((scalars X)[i]'(by omega)):ℤ)≤lim.word:=
    (Int.ofNat_le.mpr ((hnumIndex i hi).trans hcspace)).trans hw
  have hfitIndex (i : ℕ) (hi : i<31) : |(((scalars X)[i]'(by omega)):ℤ)|≤lim.word:=by
    simpa only [Int.natCast_nonneg,abs_of_nonneg] using hwordIndex i hi
  have hPointer (z : ℕ) (hz : z≤lim.space) : |(z:ℤ)|≤lim.word:=by
    simpa only [Int.natCast_nonneg,abs_of_nonneg] using (Int.ofNat_le.mpr hz).trans hw
  have hEnd : LightTernaryPrefixSetup.endAt X.prefixFree X.m (X.j+1)≤lim.space :=by
    change addr I.free I.capacity 13+4^(LightTernaryPrefixSetup.N m (j+1))+(2*LightTernaryPrefixSetup.N m (j+1)+1)+8≤lim.space
    have hh:=region_space (free:=I.free) (slot:=13) (by decide : 13<slots) hfp hspace
    dsimp only [footprint,X,inputs] at hh
    omega
  have hTail : LightTernaryPrefixSetup.N X.m (X.j+1)*LightTernaryPrefixSetup.nb X.m (X.j+1)≤I.capacity:=
    hnumIndex 19 (by decide)
  have hFtail : X.Fbase+LightTernaryPrefixSetup.N X.m (X.j+1)*LightTernaryPrefixSetup.nb X.m (X.j+1)≤lim.space:=
    region_space (by decide : 50<slots) hTail hspace
  have hGtail : X.Gbase+LightTernaryPrefixSetup.N X.m (X.j+1)*LightTernaryPrefixSetup.nb X.m (X.j+1)≤lim.space:=
    region_space (by decide : 51<slots) hTail hspace
  have hbank : X.prefixFree≤lim.space:=by dsimp [LightTernaryPrefixSetup.endAt,LightTernaryPrefixSetup.headerAt,LightTernaryPrefixSetup.workAt] at hEnd;generalize 4^(LightTernaryPrefixSetup.N X.m (X.j+1))=mask at hEnd;omega
  have hwork : LightTernaryPrefixSetup.workAt X.prefixFree X.m (X.j+1)≤lim.space:=by dsimp [LightTernaryPrefixSetup.endAt,LightTernaryPrefixSetup.headerAt] at hEnd;generalize 4^(LightTernaryPrefixSetup.N X.m (X.j+1))=mask at hEnd;omega
  have hhdr : LightTernaryPrefixSetup.headerAt X.prefixFree X.m (X.j+1)≤lim.space:=by dsimp [LightTernaryPrefixSetup.endAt] at hEnd;generalize 4^(LightTernaryPrefixSetup.N X.m (X.j+1))=mask at hEnd;omega
  have htemplate : X.template≤lim.space:=by exact (before (free:=I.free) (C:=I.capacity) (by decide : 0<13) (show 0≤I.capacity by omega)).trans hbank
  have hhost : X.liveHeader≤lim.space:=by exact (before (free:=I.free) (C:=I.capacity) (by decide : 1<13) (show 0≤I.capacity by omega)).trans hbank
  refine {
    spaceWord:=hw
    prefixSpace:=hEnd
    prefixWord:=(Int.ofNat_le.mpr (hpw.trans hcspace)).trans hw
    depthBound:=hdepth
    jWord:=hwordIndex 0 (by decide)
    templateEnd:=before (by decide : 0<1) h106
    headerEnd:=before (by decide : 1<3) h106
    seedEnd:=before (by decide : 3<13) (by omega)
    Fread:=hF
    Gread:=hG
    cutoff:=?_
    Nword:=?_
    scalarWords:=?_
    factorWords:=?_
    queryWords:=?_
    budgetRead:=hbudget
    budgetWords:=?_
    midWord:=hwordIndex 29 (by decide)
    nineWord:=hwordIndex 30 (by decide) }
  · change LightTernaryPrefixSetup.T m (j+1)+1≤2*(alphaRank m*(j+1))
    change 20384999*((j+1)*m)+1≤2*((8908424*m+2*(978249*m))*(j+1))
    have hpos : 1≤(j+1)*m:=by nlinarith
    nlinarith
  · change (LightTernaryPrefixSetup.N X.m (X.j+1):ℤ)+1≤lim.word
    have hh:=hwordIndex 11 (by decide)
    change ((2*LightTernaryPrefixSetup.N X.m (X.j+1):ℕ):ℤ)≤lim.word at hh
    have hN : 1≤LightTernaryPrefixSetup.N X.m (X.j+1):=by dsimp [X,inputs,LightTernaryPrefixSetup.N];nlinarith
    omega
  · intro x hx
    simp only [LightTernaryPrefixHeader.args,LightTernaryPrefixHeader.locals,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with h|h
    · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hPointer _ htemplate
      · exact hPointer _ hhost
      · exact hPointer _ hhdr
      · exact hfitIndex 0 (by decide)
      · exact hfitIndex 1 (by decide)
      · exact hfitIndex 2 (by decide)
      · exact hfitIndex 3 (by decide)
      · exact hfitIndex 4 (by decide)
      · exact hfitIndex 5 (by decide)
      · exact hfitIndex 6 (by decide)
      · exact hfitIndex 7 (by decide)
      · exact hfitIndex 8 (by decide)
    · rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hfitIndex 9 (by decide)
      · exact hfitIndex 10 (by decide)
      · exact hfitIndex 11 (by decide)
      · exact hfitIndex 12 (by decide)
      · exact hfitIndex 13 (by decide)
      · exact hPointer _ hbank
      · exact hPointer _ hwork
      · exact hfitIndex 14 (by decide)
      · exact hfitIndex 15 (by decide)
      · exact hfitIndex 16 (by decide)
      · exact hfitIndex 17 (by decide)
      · exact hfitIndex 18 (by decide)
      · exact hfitIndex 19 (by decide)
      · exact hfitIndex 20 (by decide)
      · exact hfitIndex 21 (by decide)
      · exact hfitIndex 22 (by decide)
      · exact hPointer _ hFtail
      · exact hPointer _ hGtail
  · intro i hi
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide : 0<2) hi)).trans
      (hwordIndex 16 (by decide))
  · intro i hi
    have hradix : 1≤X.radix:=by dsimp [X,inputs];exact Nat.one_le_pow _ _ (by decide)
    have hm : Monotone (LightTernaryRepeatWord.value X.localQ X.radix):=monotone_nat_of_le_succ (fun i=>by
      simp only [LightTernaryRepeatWord.value]
      nlinarith)
    have hh:=hm hi
    exact (Int.ofNat_le.mpr hh).trans (hwordIndex 22 (by decide))
  · intro x hx
    simp only [LightTernaryBudgetStep.nextValues,List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl
    · exact hwordIndex 23 (by decide)
    · exact hwordIndex 24 (by decide)
    · exact hwordIndex 25 (by decide)
    · exact hwordIndex 26 (by decide)
    · exact hwordIndex 27 (by decide)
    · exact hwordIndex 28 (by decide)

theorem next_config (p m F j J n U0 a b scale : ℕ) (I : Input)
    (A : TernaryArenaSeedCandidate.Inputs) (Q : TernaryGoodOutputCatalog.Output m)
    (hJ : J=A.J) :
    TernaryPrefixSeedHeader.nextConfig (TernaryArenaSeedCandidate.config p j I A 0)
      (inputs p m F j J n U0 a b scale I Q)=TernaryArenaSeedCandidate.config p (j+1) I A 0 :=by
  cases hJ
  rfl

/-- The actual ten preparation writes give the exact positive-prefix seed
header, including the incremented budget denominators and thresholds. -/
theorem prepared_seed {p m F j n U0 a b scale seedCount newSpan : ℕ} (I : Input)
    (A : TernaryArenaSeedCandidate.Inputs) (Q : TernaryGoodOutputCatalog.Output m)
    {μ ν : ℕ→ℤ}
    (H : Prepared (inputs p m F j A.J n U0 a b scale I Q) μ ν)
    (hcap : 106≤I.capacity)
    (hseed : Seg μ (addr I.free I.capacity 3)
      (LightTernaryPrefixFinish.header (TernaryArenaSeedCandidate.config p j I A 0)
        seedCount (p^j) (p^j) (a^j) (9^j*n^2) (9^j*n^2) (U0*(b*scale)^j) newSpan)) :
    Seg ν (addr I.free I.capacity 3)
      (LightTernaryPrefixFinish.header (TernaryArenaSeedCandidate.config p (j+1) I A 0)
        seedCount (p^(j+1)) (p^(j+1)) (a^(j+1)) (9^(j+1)*n^2) (9^(j+1)*n^2)
        (U0*(b*scale)^(j+1)) newSpan) :=by
  have hh:=TernaryPrefixSeedHeader.prepared_header H hseed
    (before (free:=I.free) (C:=I.capacity) (by decide : 3<13) (show 48≤I.capacity by omega))
    (before (free:=I.free) (C:=I.capacity) (by decide : 1<3) hcap)
  rw [next_config p m F j A.J n U0 a b scale I A Q rfl] at hh
  convert hh using 1 <;> simp only [inputs,pow_succ,Nat.pow_two] <;> congr 1 <;> ring

end ThreeSum.TernaryArenaPrefixPrepare
