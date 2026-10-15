import Submission.ThreeSum.LightTernaryNearSourceWords

/-! Two actual homogeneous reconstructions followed by their actual pointwise product. -/
noncomputable section
namespace ThreeSum.LightTernaryNearPair

open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.TernaryCodeSemantics

set_option maxHeartbeats 6000000
set_option maxRecDepth 12000

structure Config where
  a : ℕ
  powers : ℕ
  bank : ℕ
  nb : ℕ
  bv : ℕ
  L : ℕ
  T : ℕ
  activeBase : ℕ
  ws : ℕ
  rankBase : ℕ
  vals : ℕ
  h : ℕ
  pcount : ℕ
  fr : ℕ
  U : ℕ
  V : ℕ

def args (N rows : ℕ) (c : Config) : List ℤ :=
  [N,c.a,rows,c.powers,c.bank,c.nb,c.bv,c.L,c.T,c.activeBase,c.ws,c.rankBase,c.vals,c.h,2*N,c.pcount,c.fr]

def time (N rows : ℕ) (c : Config) : ℕ := LightTernaryNearSource.time N c.L rows (2*N-c.T) c.V

structure Ready (lim : Limits) {N : ℕ} (rows : ℕ) (c : Config) (μ : ℕ → ℤ)
    (Q : TritWord N) (bankWords nearWords : ℕ → TritWord N) (source : TritWord N → ℤ) : Prop where
  homogeneous : ∀ A, source A≠0 → rank A=c.h
  division : ∀ current, c.T<current → current≤2*N → Light.Emod.Pre lim (current-c.h) c.V c.fr
  hw : (lim.space : ℤ)≤lim.word
  ha : c.a+rows≤c.ws
  hb : c.bank+c.nb≤c.ws
  hp : c.powers+(2*N+1)≤c.ws
  hactiveSpace : c.activeBase+N≤c.ws
  hbankVals : c.bv+c.nb≤c.ws
  hmetadataRanks : c.ws+2*N*rows+N≤c.rankBase
  hrankVals : c.rankBase+rows≤c.vals
  hvals : c.vals+rows≤c.fr
  hfr : c.fr≤lim.space
  hcount : c.vals+rows≤c.pcount
  hspace : c.pcount≤lim.space
  hword : ((c.nb+rows+2^(2*N+1)+2*N+32 : ℕ) : ℤ)≤lim.word
  hcontrols : ((c.T+N+32 : ℕ) : ℤ)≤lim.word
  hmemoWord : ((N+rows+2*N+c.h+20 : ℕ) : ℤ)≤lim.word
  hread : ∀ j<rows, μ (c.a+j)=(address (nearWords j) : ℤ)
  hbankRead : ∀ j<c.nb, μ (c.bank+j)=(address (bankWords j) : ℤ)
  hactiveRead : ∀ i<N, μ (c.activeBase+i)=1
  hbankSorted : ∀ j k, j<k → k<c.nb → address (bankWords j)<address (bankWords k)
  hnearSorted : ∀ j k, j<k → k<rows → address (nearWords j)<address (nearWords k)
  hpowers : Powers μ c.powers (2*N)
  hL : c.L≤2*N
  hnb : c.nb<2^c.L
  hnn : rows<2^c.L
  hnbpos : 0<c.nb
  hbankPresent : ∀ W, rank W≤c.T → ∃ j<c.nb, bankWords j=W
  hnearPresent : ∀ W, Below W Q → c.T<rank W → ∃ j<rows, nearWords j=W
  hnearRows : ∀ j<rows, Below (nearWords j) Q ∧ c.T<rank (nearWords j)
  hT : c.T≤2*N
  hh : c.h≤c.T
  hbankValues : ∀ j<c.nb, μ (c.bv+j)=binomialZeta source (bankWords j)
  hvalue : ∀ R, |binomialZeta source R|≤c.U
  hV : 2*(N+1)*c.U≤c.V

/-- All actual inputs (including source values) lie below this cutoff. -/
def ReadBefore (N rows : ℕ) (c : Config) (cut : ℕ) : Prop :=
  c.a+rows≤cut ∧ c.bank+c.nb≤cut ∧ c.powers+(2*N+1)≤cut ∧
    c.activeBase+N≤cut ∧ c.bv+c.nb≤cut

theorem Ready.transfer {lim : Limits} {N rows cut : ℕ} {c : Config} {μ ν : ℕ → ℤ}
    {Q : TritWord N} {bankWords nearWords : ℕ → TritWord N} {source : TritWord N → ℤ}
    (R : Ready lim rows c μ Q bankWords nearWords source) (H : Kept μ ν cut)
    (B : ReadBefore N rows c cut) : Ready lim rows c ν Q bankWords nearWords source := by
  refine {R with hread := ?_,hbankRead := ?_,hactiveRead := ?_,hpowers := ?_,hbankValues := ?_}
  · intro j hj; rw [H _ (by rcases B with ⟨h,_,_,_,_⟩; omega)]; exact R.hread j hj
  · intro j hj; rw [H _ (by rcases B with ⟨_,h,_,_,_⟩; omega)]; exact R.hbankRead j hj
  · intro i hi; rw [H _ (by rcases B with ⟨_,_,_,h,_⟩; omega)]; exact R.hactiveRead i hi
  · intro i hi; rw [H _ (by rcases B with ⟨_,_,h,_,_⟩; omega)]; exact R.hpowers i hi
  · intro j hj; rw [H _ (by rcases B with ⟨_,_,_,_,h⟩; omega)]; exact R.hbankValues j hj

structure Entries where
  source : ℕ
  ranks : ℕ
  metadata : ℕ
  memo : ℕ
  column : ℕ
  cell : ℕ
  digit : ℕ
  zero : ℕ
  erase : ℕ
  rank : ℕ
  search : ℕ
  scan : ℕ
  fill : ℕ
  row : ℕ
  sum : ℕ
  divide : ℕ
  natural : ℕ
  product : ℕ

structure Library (P : Program) (e : Entries) : Prop where
  source : P[e.source]?=some (LightTernaryNearSource.body e.ranks e.metadata e.memo)
  ranks : P[e.ranks]?=some (LightTernaryRankTable.body e.rank)
  metadata : P[e.metadata]?=some (LightTernaryEulerMetadata.body e.column)
  memo : P[e.memo]?=some (LightTernaryEulerMemo.body e.scan)
  column : P[e.column]?=some (LightTernaryPredecessorTable.body e.cell e.digit)
  cell : P[e.cell]?=some (LightTernaryPredecessor.body e.digit e.zero e.erase e.rank e.search)
  digit : P[e.digit]?=some (LightTernaryCodes.digitBody e.erase)
  zero : P[e.zero]?=some (LightTernaryCodes.zeroBody e.erase)
  erase : P[e.erase]?=some (LightMaskErase.body e.erase)
  rank : P[e.rank]?=some (LightTernaryRank.body e.digit)
  search : P[e.search]?=some (LightBandLookup.searchBody e.search)
  scan : P[e.scan]?=some (LightTernaryEulerScan.body e.fill)
  fill : P[e.fill]?=some (LightTernaryEulerRow.fillBody e.row)
  row : P[e.row]?=some (LightTernaryEulerRow.body e.sum e.divide)
  sum : P[e.sum]?=some LightTernaryWeightedSum.body
  divide : P[e.divide]?=some (LightTernaryDivide.body e.natural)
  natural : P[e.natural]?=some LightOutputDecodeDivide.body
  product : P[e.product]?=some LightTernaryProduct.body

theorem Ready.meets {lim : Limits} {P : Program} {e : Entries} (lib : Library P e)
    {N rows d : ℕ} {c : Config} {μ : ℕ → ℤ} {Q : TritWord N}
    {bankWords nearWords : ℕ → TritWord N} {source : TritWord N → ℤ}
    (R : Ready lim rows c μ Q bankWords nearWords source) (hd : d+2*N+7≤lim.depth) :
    Meets lim P e.source d (args N rows c) μ (time N rows c)
      (fun r ν => r=0 ∧ Kept μ ν c.ws ∧ ∀ j<rows, ν (c.vals+j)=binomialZeta source (nearWords j)) := by
  exact LightTernaryNearSourceWords.meets lib.source lib.ranks lib.metadata lib.memo lib.column lib.cell
    lib.digit lib.zero lib.erase lib.rank lib.search lib.scan lib.fill lib.row lib.sum lib.divide lib.natural
    μ Q bankWords nearWords source R.homogeneous R.division R.hw R.ha R.hb R.hp R.hactiveSpace R.hbankVals
    R.hmetadataRanks R.hrankVals R.hvals R.hfr R.hcount R.hspace R.hword R.hcontrols R.hmemoWord R.hread
    R.hbankRead R.hactiveRead R.hbankSorted R.hnearSorted R.hpowers R.hL R.hnb R.hnn R.hnbpos
    R.hbankPresent R.hnearPresent R.hnearRows R.hT R.hh R.hbankValues R.hvalue R.hV hd

def body (pSource pProduct : ℕ) : Stmt :=
  .call pSource [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 35 ;;
  .call pSource [v 17,v 18,v 19,v 20,v 21,v 22,v 23,v 24,v 25,v 26,v 27,v 28,v 29,v 30,v 31,v 32,v 33] 35 ;;
  .call pProduct [v 12,v 29,v 34,v 2] 35 ;;
  .set 0 (k 0)

def pairTime (N rows : ℕ) (f g : Config) : ℕ := time N rows f+time N rows g+LightTernaryProduct.time rows+1000

theorem meets {lim : Limits} {P : Program} {e : Entries} {pMain N rows out d : ℕ}
    (hmain : P[pMain]?=some (body e.source e.product)) (lib : Library P e)
    (f g : Config) (μ : ℕ → ℤ) (Q : TritWord N) (bankWords nearWords : ℕ → TritWord N)
    (F G : TritWord N → ℤ)
    (Rf : Ready lim rows f μ Q bankWords nearWords F) (Rg : Ready lim rows g μ Q bankWords nearWords G)
    (hGRead : ReadBefore N rows g f.ws)
    (hFbeforeG : f.vals+rows≤g.ws)
    (hFout : f.vals+rows≤out) (hGout : g.vals+rows≤out)
    (hOutSpace : out+rows≤lim.space) (hOutKeep : f.ws≤out)
    (hvalue : (f.U : ℤ)*(g.U : ℤ)≤lim.word)
    (hd : d+2*N+8≤lim.depth) :
    Meets lim P pMain d (args N rows f++args N rows g++[(out : ℤ)]) μ (pairTime N rows f g)
      (fun r ν => r=0 ∧ Kept μ ν f.ws ∧ ∀ j<rows,
        ν (out+j)=binomialZeta F (nearWords j)*binomialZeta G (nearWords j)) := by
  have hw := Rf.hw
  have hfmeta := Rf.hmetadataRanks
  have hfrank := Rf.hrankVals
  have hFws : f.ws≤f.vals := by omega
  have hcF := Rf.meets lib (d := d+1) (by omega)
  apply Meets.of_body hmain
  unfold body pairTime
  light_call hcF using args,time,LightTernaryNearSource.time,LightTernaryProduct.time
    with rf ν ⟨hrf,hkeepF,hF⟩
  have RG := Rg.transfer hkeepF hGRead
  have hcG := RG.meets lib (d := d+1) (by omega)
  light_call hcG using args,time,LightTernaryNearSource.time,LightTernaryProduct.time
    with rg ξ ⟨hrg,hkeepG,hG⟩
  have hfRead : ∀ j<rows, ξ (f.vals+j)=binomialZeta F (nearWords j) := by
    intro j hj; rw [hkeepG _ (by omega),hF j hj]
  have hp := LightTernaryProduct.meets (d := d+1) lib.product ξ Rf.hw
    (by omega) (by omega) hOutSpace (Or.inr (Or.inl hFout)) (Or.inr (Or.inl hGout))
    (fun j hj => by rw [hfRead j hj]; exact Rf.hvalue _) (fun j hj => by rw [hG j hj]; exact Rg.hvalue _)
    hvalue
  light_call hp using args,time,LightTernaryNearSource.time,LightTernaryProduct.time
    with rp η ⟨hProducts,hOutside⟩
  light_set 0 using args,time,LightTernaryNearSource.time,LightTernaryProduct.time
  refine ⟨rfl,?_,?_⟩
  · intro x hx
    change η x=μ x
    rw [hOutside x (Or.inl (by omega)),hkeepG x (by omega),hkeepF x hx]
  · intro j hj
    change η (out+j)=_
    rw [hProducts j hj,hfRead j hj,hG j hj]

/-- Both actual reconstructions and the product retain the near-row Gibbs
exponent; all additional work is polynomial in the word dimension. -/
theorem pairTime_bound (N rows : ℕ) (f g : Config) :
    pairTime N rows f g≤23000*
      (N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3)^3*(rows+1) := by
  let K := N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3
  have hK : 1≤K := by omega
  have hf := LightTernaryNearSource.time_bound (N := N) (L := f.L) (rows := rows)
    (stages := 2*N-f.T) (V := f.V) (by omega)
  have hg := LightTernaryNearSource.time_bound (N := N) (L := g.L) (rows := rows)
    (stages := 2*N-g.T) (V := g.V) (by omega)
  have hfK : time N rows f≤11000*K^3*(rows+1) := by
    calc
      _≤11000*(N+f.L+Nat.log 2 (f.V+1)+3)^3*(rows+1) := hf
      _≤11000*K^3*(rows+1) := by gcongr; omega
  have hgK : time N rows g≤11000*K^3*(rows+1) := by
    calc
      _≤11000*(N+g.L+Nat.log 2 (g.V+1)+3)^3*(rows+1) := hg
      _≤11000*K^3*(rows+1) := by gcongr; omega
  have hkpow : 1≤K^3 := one_le_pow₀ hK
  have hsmall : LightTernaryProduct.time rows+1000≤1000*K^3*(rows+1) := by
    unfold LightTernaryProduct.time
    have hKthree : 3≤K := by omega
    have hpow : 3≤K^3 := hKthree.trans (le_self_pow (by omega) (by decide))
    nlinarith
  unfold pairTime
  change _≤23000*K^3*(rows+1)
  nlinarith only [hfK,hgK,hsmall]

/-- Closed nineteen-procedure implementation. -/
def entries : Entries := ⟨0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17⟩
def program : Program := [
  LightTernaryNearSource.body 1 2 3,LightTernaryRankTable.body 9,
  LightTernaryEulerMetadata.body 4,LightTernaryEulerMemo.body 11,
  LightTernaryPredecessorTable.body 5 6,LightTernaryPredecessor.body 6 7 8 9 10,
  LightTernaryCodes.digitBody 8,LightTernaryCodes.zeroBody 8,LightMaskErase.body 8,
  LightTernaryRank.body 6,LightBandLookup.searchBody 10,LightTernaryEulerScan.body 12,
  LightTernaryEulerRow.fillBody 13,LightTernaryEulerRow.body 14 15,LightTernaryWeightedSum.body,
  LightTernaryDivide.body 16,LightOutputDecodeDivide.body,LightTernaryProduct.body,body 0 17]

@[simp] theorem program_length : program.length=19 := rfl

theorem program_library : Library program entries := by constructor <;> rfl
@[simp] theorem program_main : program[18]?=some (body entries.source entries.product) := rfl

def program_meets {lim : Limits} {N rows out d : ℕ} :=
  meets (lim := lim) (N := N) (rows := rows) (out := out) (d := d) program_main program_library

end ThreeSum.LightTernaryNearPair
