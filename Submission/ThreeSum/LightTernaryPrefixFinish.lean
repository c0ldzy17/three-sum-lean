import Submission.ThreeSum.LightTernaryFullController
import Submission.ThreeSum.TernaryPrefixProgramLibrary

noncomputable section
namespace ThreeSum.LightTernaryPrefixFinish
open Light LightTernarySeedScoreFactory LightTernaryControllerFactory
open LightTernaryPrefixLoop
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

/-- The literal suffix of entry 180 following the actual preparation call. -/
def body : Stmt :=
  .call 166 seedArgs 26 ;;
  .call 176 [M (v 3 +' k 9),M (v 3 +' k 8),M (v 3 +' k 10),
    M (v 3 +' k 13),M (v 3 +' k 12),M (v 3 +' k 14),
    M (v 3 +' k 17),M (v 3 +' k 16),M (v 3 +' k 18)] 26 ;;
  .call 177 [M (v 3 +' k 47),M (v 3 +' k 3),v 19 *' v 11] 26 ;;
  .set 0 (v 19)

theorem step_eq : stepBody = (
    .call 184 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,v 16] 19 ;; body) :=rfl

def header (C : Config) (n dB dC dP tB tC tP newSpan : ℕ) : List ℤ :=
  LightTernarySeedController.args (withSeed C 0).argv n dB dC dP tB tC tP newSpan

@[simp] theorem header_length (C : Config) (n dB dC dP tB tC tP newSpan : ℕ) :
    (header C n dB dC dP tB tC tP newSpan).length=48 :=by
  simp [header,LightTernarySeedController.args,Config.argv,LightTernarySeedScore.args]

structure Layout (C : Config) (lim : Limits) (seed rows newSpan : ℕ) : Prop where
  seedEnd : seed+48≤C.Bold
  BC : C.Bold+C.nB≤C.Cold
  CO : C.Cold+C.nC≤C.Oold
  OB : C.Oold+C.nO≤C.Bnew
  OC : C.Oold+C.nO≤C.Cnew
  OO : C.Oold+C.nO≤C.Onew
  Bspace : C.Bnew+C.nB≤lim.space
  Cspace : C.Cnew+C.nC≤lim.space
  Ospace : C.Onew+C.nO≤lim.space
  keysSpan : C.Oold+C.nO≤C.catalog
  spanApart : C.catalog+rows*C.J≤newSpan
  spanSpace : newSpan+rows*C.J≤lim.space

/-- All outputs refer to the actual replayed candidate memory. -/
def Committed (C : Config) (rows newSpan : ℕ) (ξ ν : ℕ→ℤ) : Prop :=
  Kept ξ ν C.Bold ∧
  (∀i<C.nB, ν (C.Bold+i)=ξ (C.Bnew+i)) ∧
  (∀i<C.nC, ν (C.Cold+i)=ξ (C.Cnew+i)) ∧
  (∀i<C.nO, ν (C.Oold+i)=ξ (C.Onew+i)) ∧
  (∀k<rows, ∀i<C.J, ν (C.catalog+C.J*k+i)=ξ (newSpan+C.J*k+i)) ∧
  (∀x, (x<C.Bold ∨ C.Oold+C.nO≤x)→(x<C.catalog ∨ C.catalog+rows*C.J≤x)→ν x=ξ x)

private theorem commit_meets {lim : Limits} {P : Program} {d : ℕ}
    (hcopy : P[175]?=some copyBody)
    (hmain : P[176]?=some (ReportingHostRelocation.relocate 175 LightTernaryCommitKeys.body))
    (C : Config) (μ : ℕ→ℤ) (hw : (lim.space:ℤ)≤lim.word)
    (hBC : C.Bold+C.nB≤C.Cold) (hCO : C.Cold+C.nC≤C.Oold)
    (hOB : C.Oold+C.nO≤C.Bnew) (hOC : C.Oold+C.nO≤C.Cnew) (hOO : C.Oold+C.nO≤C.Onew)
    (hB : C.Bnew+C.nB≤lim.space) (hC : C.Cnew+C.nC≤lim.space) (hO : C.Onew+C.nO≤lim.space)
    (hd : d<lim.depth) :
    Meets lim P 176 d [C.Bnew,C.Bold,C.nB,C.Cnew,C.Cold,C.nC,C.Onew,C.Oold,C.nO] μ
      (LightTernaryCommitKeys.time C.nB C.nC C.nO)
      (fun r ν=>r=0 ∧ Kept μ ν C.Bold ∧
        (∀i<C.nB,ν (C.Bold+i)=μ (C.Bnew+i)) ∧
        (∀i<C.nC,ν (C.Cold+i)=μ (C.Cnew+i)) ∧
        (∀i<C.nO,ν (C.Oold+i)=μ (C.Onew+i)) ∧
        (∀x,C.Oold+C.nO≤x→ν x=μ x)) :=by
  have hBold : C.Bold+C.nB≤lim.space :=by omega
  have hCold : C.Cold+C.nC≤lim.space :=by omega
  have hOold : C.Oold+C.nO≤lim.space :=by omega
  apply Meets.of_body hmain
  simp only [LightTernaryCommitKeys.body,ReportingHostRelocation.relocate]
  unfold LightTernaryCommitKeys.time
  light_call (copy_meets (d:=d+1) (μ:=μ) hcopy hw hB hBold (Or.inr (by omega))) with rb μb ⟨hb,kb⟩
  light_call (copy_meets (d:=d+1) (μ:=μb) hcopy hw hC hCold (Or.inr (by omega))) with rc μc ⟨hc,kc⟩
  light_call (copy_meets (d:=d+1) (μ:=μc) hcopy hw hO hOold (Or.inr (by omega))) with ro ν ⟨ho,ko⟩
  light_set (0:ℕ)
  refine ⟨by simp,?_,?_,?_,?_,?_⟩
  · intro x hx; change ν x=μ x; rw [ko x (by omega),kc x (by omega),kb x (by omega)]
  · intro i hi; change ν (C.Bold+i)=μ (C.Bnew+i); rw [ko _ (by omega),kc _ (by omega),hb i hi]
  · intro i hi; change ν (C.Cold+i)=μ (C.Cnew+i); rw [ko _ (by omega),hc i hi,kb _ (by omega)]
  · intro i hi; change ν (C.Oold+i)=μ (C.Onew+i); rw [ho i hi,kc _ (by omega),kb _ (by omega)]
  · intro x hx; change ν x=μ x; rw [ko x (by omega),kc x (by omega),kb x (by omega)]

private theorem seed_arguments {lim : Limits} {loc μ : ℕ→ℤ} {seed : ℕ} {values : List ℤ}
    (hloc : loc 3=(seed:ℤ)) (hs : seed+48≤lim.space) (hw : (lim.space:ℤ)≤lim.word)
    (hlen : values.length=48) (hseg : Seg μ seed values) :
    (∀e∈seedArgs,e.Safe lim ⟨loc,μ⟩) ∧ seedArgs.map (·.val ⟨loc,μ⟩)=values :=by
  constructor
  · intro e he
    obtain ⟨i,hi,rfl⟩:=List.mem_map.mp he
    have hi' : i<48:=List.mem_range.mp hi
    simp only [M,v,k,Expr.Safe,Expr.val,Op.eval,hloc,Limits.Addr,true_and,abs_of_nonneg (by positivity : (0:ℤ)≤(seed:ℤ)+(i:ℤ))]
    constructor
    · constructor <;> omega
    · constructor <;> omega
  · calc
      seedArgs.map (·.val ⟨loc,μ⟩)=readSeg μ seed 48 :=by
        simp [seedArgs,readSeg,List.map_map,Expr.val,Op.eval,hloc]
      _=values :=by simpa only [hlen] using hseg.eq_readSeg.symm

private theorem local_read (l : List ℤ) (x : ℕ) (z : ℤ) (y : ℕ) :
    ((setLocal l x z)[y]?).getD 0=if y=x then z else (l[y]?).getD 0 :=by
  simpa only [frame,List.getD_eq_getElem?_getD] using frame_setLocal l x z y

def time (C : Config) (n seedTime rows : ℕ) : ℕ :=
  LightTernarySeedController.time n seedTime (LightSpanCatalogStep.time C.J C.p C.catalogRows)+
    LightTernaryCommitKeys.time C.nB C.nC C.nO+copyTime (rows*C.J)+5000

/-- Actual controller, actual key commits, and actual span commit. All
requirements are pure memory/layout certificates. -/
theorem ends {C : Config} [Fact C.p.Prime] {D : Family C} {lim : Limits}
    {depth K R S n U dB dC dP tB tC tP newSpan seedTime seed rows : ℕ}
    {raws : List ℤ} {words maps : List ℕ} (l : List ℤ) (μ : ℕ→ℤ)
    (H : FullPlan C D lim (depth+1) K R S n U dB dC dP tB tC tP newSpan seedTime raws words maps μ)
    (A : Layout C lim seed rows newSpan)
    (hseed : l.getD 3 0=(seed:ℤ)) (hJ : l.getD 11 0=(C.J:ℤ)) (hrows : l.getD 19 0=(rows:ℤ))
    (hheader : Seg μ seed (header C n dB dC dP tB tC tP newSpan))
    (hfinal : ∀ν,H.finalState ν→Seg ν seed (header C n dB dC dP tB tC tP newSpan)) :
    Ends lim (program C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr) depth body
      ⟨frame l,μ⟩ (time C n seedTime rows)
      (fun σ=>σ.loc 0=(rows:ℤ) ∧ ∃ξ,H.finalState ξ ∧ Committed C rows newSpan ξ σ.mem ∧
        Seg σ.mem seed (header C n dB dC dP tB tC tP newSpan)) :=by
  let P:=program C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr
  have lib:=program_library C.p R S K raws words maps D.xl D.yl D.zl D.xr D.yr D.zr
  simp only [List.getD_eq_getElem?_getD] at hseed hJ hrows
  have hw:=H.spaceWord
  have hd : depth<lim.depth:=by have:=H.depthBound;omega
  have hseedSpace : seed+48≤lim.space:=by have:=A.seedEnd;have:=A.BC;have:=A.CO;have:=A.OO;have:=A.Ospace;omega
  have hcontrol:=H.run.append tail
  rw [←program_eq_controller_append] at hcontrol
  have hargs:=seed_arguments (loc:=frame l) (by exact hseed) hseedSpace hw
    (header_length C n dB dC dP tB tC tP newSpan) hheader
  have hcost : (seedArgs.map Expr.cost).sum=192 :=by decide
  unfold body time
  refine Ends.callToThen hcontrol ?_ hargs hd (by light_time [hcost])
  rintro chosen ξ ⟨hchosen,hξ⟩
  have hξheader:=hfinal ξ hξ
  have haddr (i : ℕ) : ((seed:ℤ)+(i:ℤ)).toNat=seed+i :=by omega
  have hξread (i : ℕ) (hi : i<48) :=hξheader.getD (by simpa using hi) 0
  have hξ3 : ξ ((seed:ℤ)+3).toNat=(C.catalog:ℤ) :=by
    rw [show ((seed:ℤ)+3).toNat=seed+3 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=3) (by simp) 0
  have hξ8 : ξ ((seed:ℤ)+8).toNat=(C.Bold:ℤ) :=by
    rw [show ((seed:ℤ)+8).toNat=seed+8 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=8) (by simp) 0
  have hξ9 : ξ ((seed:ℤ)+9).toNat=(C.Bnew:ℤ) :=by
    rw [show ((seed:ℤ)+9).toNat=seed+9 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=9) (by simp) 0
  have hξ10 : ξ ((seed:ℤ)+10).toNat=(C.nB:ℤ) :=by
    rw [show ((seed:ℤ)+10).toNat=seed+10 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=10) (by simp) 0
  have hξ12 : ξ ((seed:ℤ)+12).toNat=(C.Cold:ℤ) :=by
    rw [show ((seed:ℤ)+12).toNat=seed+12 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=12) (by simp) 0
  have hξ13 : ξ ((seed:ℤ)+13).toNat=(C.Cnew:ℤ) :=by
    rw [show ((seed:ℤ)+13).toNat=seed+13 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=13) (by simp) 0
  have hξ14 : ξ ((seed:ℤ)+14).toNat=(C.nC:ℤ) :=by
    rw [show ((seed:ℤ)+14).toNat=seed+14 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=14) (by simp) 0
  have hξ16 : ξ ((seed:ℤ)+16).toNat=(C.Oold:ℤ) :=by
    rw [show ((seed:ℤ)+16).toNat=seed+16 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=16) (by simp) 0
  have hξ17 : ξ ((seed:ℤ)+17).toNat=(C.Onew:ℤ) :=by
    rw [show ((seed:ℤ)+17).toNat=seed+17 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=17) (by simp) 0
  have hξ18 : ξ ((seed:ℤ)+18).toNat=(C.nO:ℤ) :=by
    rw [show ((seed:ℤ)+18).toNat=seed+18 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=18) (by simp) 0
  have hξ47 : ξ ((seed:ℤ)+47).toNat=(newSpan:ℤ) :=by
    rw [show ((seed:ℤ)+47).toNat=seed+47 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hξheader.getD (i:=47) (by simp) 0
  have hc:=commit_meets lib.commitCopy lib.commitMain C ξ hw A.BC A.CO A.OB A.OC A.OO A.Bspace A.Cspace A.Ospace (by have:=H.depthBound;omega)
  light_call hc using header,LightTernarySeedController.args,Config.argv,withSeed,
    LightTernarySeedScore.args,hseed,hξ3,hξ8,hξ9,hξ10,hξ12,hξ13,hξ14,hξ16,hξ17,hξ18,hξ47,local_read,hcost,LightTernaryCommitKeys.time,copyTime with z η ⟨hz,hkeep,hB,hC,hO,hupper⟩
  have hηheader : Seg η seed (header C n dB dC dP tB tC tP newSpan) :=by
    intro i hi
    rw [hkeep _ (by have:=A.seedEnd;have:=header_length C n dB dC dP tB tC tP newSpan;omega)]
    exact hξheader i hi
  have hηread (i : ℕ) (hi : i<48) :=hηheader.getD (by simpa using hi) 0
  have hη3 : η ((seed:ℤ)+3).toNat=(C.catalog:ℤ) :=by
    rw [show ((seed:ℤ)+3).toNat=seed+3 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hηheader.getD (i:=3) (by simp) 0
  have hη47 : η ((seed:ℤ)+47).toNat=(newSpan:ℤ) :=by
    rw [show ((seed:ℤ)+47).toNat=seed+47 by omega]
    simpa [header,LightTernarySeedController.args,Config.argv,withSeed,LightTernarySeedScore.args] using hηheader.getD (i:=47) (by simp) 0
  have hs:=copy_meets (d:=depth+1) (μ:=η) lib.spanCopy hw A.spanSpace
    (show C.catalog+rows*C.J≤lim.space by have:=A.spanApart;have:=A.spanSpace;omega) (Or.inr A.spanApart)
  have hmul : ((rows*C.J:ℕ):ℤ)≤lim.word :=(Int.ofNat_le.mpr (show rows*C.J≤lim.space by have:=A.spanSpace;omega)).trans hw
  light_call hs using header,LightTernarySeedController.args,Config.argv,withSeed,
    LightTernarySeedScore.args,hseed,hη3,hη47,hJ,hrows,local_read,Nat.cast_mul,hcost,LightTernaryCommitKeys.time,copyTime with zs ν ⟨hspan,houtside⟩
  light_set (rows:ℕ) using hrows,local_read,hcost,LightTernaryCommitKeys.time,copyTime
  dsimp only
  refine ⟨by simp [frame,List.getD_eq_getElem?_getD,local_read],ξ,hξ,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · intro x hx; exact (houtside x (by have:=A.BC;have:=A.CO;have:=A.keysSpan;omega)).trans (hkeep x hx)
    · intro i hi; rw [houtside _ (by have:=A.BC;have:=A.CO;have:=A.keysSpan;omega),hB i hi]
    · intro i hi; rw [houtside _ (by have:=A.CO;have:=A.keysSpan;omega),hC i hi]
    · intro i hi; rw [houtside _ (by have:=A.keysSpan;omega),hO i hi]
    · intro k hk i hi
      have hp:=Nat.mul_le_mul_left C.J (show k+1≤rows by omega)
      have hi' : C.J*k+i<rows*C.J:=by nlinarith [Nat.mul_comm C.J rows]
      rw [show C.catalog+C.J*k+i=C.catalog+(C.J*k+i) by omega,hspan _ hi']
      simpa only [Nat.add_assoc] using hupper (newSpan+(C.J*k+i)) (by have:=A.keysSpan;have:=A.spanApart;omega)
    · intro x hx hs
      rw [houtside x hs]
      rcases hx with hlow|hhigh
      · exact hkeep x hlow
      · exact hupper x hhigh
  · intro i hi
    rw [houtside _ (by have:=A.seedEnd;have:=A.BC;have:=A.CO;have:=A.keysSpan; have:=header_length C n dB dC dP tB tC tP newSpan;omega)]
    exact hηheader i hi

end ThreeSum.LightTernaryPrefixFinish
