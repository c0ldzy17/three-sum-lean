import Submission.ThreeSum.LightTernaryColoredSolver
import Submission.ThreeSum.LightTernaryColorPreparationProof
import Submission.ThreeSum.TernaryArenaHeaderAgreement

noncomputable section
namespace ThreeSum.LightTernaryColoredInitializationProof
open Light TernaryArenaLayout LightTernaryColoredSolver
attribute [local simp] frame_setLocal
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

@[local simp] private theorem read_setLocal (xs : List ℤ) (x y : ℕ) (z : ℤ) :
    (setLocal xs x z)[y]?.getD 0=if y=x then z else xs[y]?.getD 0 :=
  frame_setLocal xs x z y

/-- The literal initialization prefix of the nonempty driver branch. -/
def initChunk (p R F : ℕ) (tail : Stmt) : Stmt :=
  .set 6 (H 13) ;;
  .call 52 (arenaArgs p R F) 15 ;;
  .set 7 (M (v 6 +' k 1) -' M (v 6)) ;;
  .set 8 (A 2) ;; .set 9 (A 3) ;; .set 10 (A 1) ;; .set 11 (A 13) ;;
  .call 54 [v 1,H 16,H 9,v 8,v 8 +' k 48] 15 ;; tail

theorem body_eq (pPost m F p alpha2 alphaRank localQ R a b scaleBase L : ℕ) :
    body pPost m F p alpha2 alphaRank localQ R a b scaleBase L=
      (.call 50 [v 0,v 1,v 2,v 3,v 4] 5 ;;
      .ite (v 5 =' k 0) (.set 0 (k 0))
      (initChunk p R F (
        .call 237 (loopArgs m F p alpha2 alphaRank localQ R a b scaleBase) 12 ;;
        .set 13 (k L *' H 15) ;;
        .set 14 (k 2 *' v 13) ;;
        .call pPost postArgs 0))) := rfl

def values (n U af Bmatrix nB Cmatrix nC Omatrix nO positions menu J p R F q : ℕ) : List ℤ :=
  [n+U,af,Bmatrix,nB,Cmatrix,nC,Omatrix,nO,positions,Bmatrix,Cmatrix,menu,J,p,R,F,q,0,0,0,0,0,0]

def budgetValues (K bDigit n J nO : ℕ) : List ℤ :=
  [1,1,1,((n*n : ℕ) : ℤ),((n*n : ℕ) : ℤ),LightTernaryInitialBudgets.initial K bDigit n J nO]

def budgetedValues (xs : List ℤ) (K bDigit n J nO : ℕ) : List ℤ :=
  List.ofFn (fun (i : Fin 48) => if (41 : ℕ) ≤ i.val ∧ i.val < 47 then
    (budgetValues K bDigit n J nO).getD (i.val-41) 0 else xs.getD i.val 0)

private theorem budgeted_segment {μ ν : ℕ→ℤ} {seed constants K bDigit n J nO : ℕ}
    {xs : List ℤ} (hlen : xs.length=48) (H : Seg μ seed xs)
    (HB : Seg ν (seed+41) (budgetValues K bDigit n J nO))
    (HK : ∀x,(x<seed+41 ∨seed+47≤x)→(x<constants∨constants+3≤x)→ν x=μ x)
    (hconstants : seed+48≤constants) :
    Seg ν seed (budgetedValues xs K bDigit n J nO) := by
  intro i hi
  have hii : i<48 := by simpa only [budgetedValues,List.length_ofFn] using hi
  simp only [budgetedValues,List.getElem_ofFn]
  split_ifs with hb
  · have hj : i-41<(budgetValues K bDigit n J nO).length := by
      simp only [budgetValues,List.length_cons,List.length_nil] ; omega
    have hh:=HB.getD hj 0
    rw [show seed+i=seed+41+(i-41) by omega]
    exact hh
  · rw [HK _ (by omega) (Or.inl (by omega))]
    exact (H.getD (by omega) 0)

private theorem template_call {lim : Limits} {radix D E K bDigit a b scaleBase p R F U af q depth : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (inputs : List ℤ) (hlen : inputs.length=23) (μ : ℕ→ℤ)
    (hU : inputs.getD 0 0=(U:ℤ)) (hFree : inputs.getD 1 0=(af:ℤ))
    (hq : inputs.getD 16 0=(q:ℤ)) (hw : (lim.space:ℤ)≤lim.word)
    (hend : finish af (capacity D E U)≤lim.space)
    (hUW : (U:ℤ)+1≤lim.word) (hEW : (E:ℤ)≤lim.word)
    (hqC : q*q≤capacity D E U) (hd : depth<lim.depth) :
    Meets lim (libraries radix D E K bDigit a b scaleBase p R F raws words maps xl yl zl xr yr zr)
      52 depth inputs μ (LightTernaryArenaTemplate.time E)
      (fun r ν=>r=(af:ℤ) ∧
        Seg ν (addr af (capacity D E U) 0) (LightTernaryArenaTemplate.hostValues (frame inputs) af (capacity D E U)) ∧
        Seg ν (addr af (capacity D E U) 2) (LightTernaryArenaTemplate.seedValues (frame inputs) af (capacity D E U)) ∧
        Kept μ ν af) := by
  have ht:=ReportingHostRelocation.meets
    (LightTernaryArenaTemplate.program_meets inputs hlen μ hU hFree hq hw hend hUW hEW hqC hd)
    (LightTernaryColorPreparation.program radix)
  have hh:=ht.append ((LightTernaryInitialBudgets.program K bDigit a b scaleBase).map
    (ReportingHostRelocation.relocate 53)++
    (LightTernaryPrefixLoop.program p R F K raws words maps xl yl zl xr yr zr).map
      (ReportingHostRelocation.relocate 55))
  convert hh using 1
  all_goals try simp only [libraries,ReportingHostRelocation.program,budgetLibrary_length]
  all_goals try simp only [budgetLibrary,ReportingHostRelocation.program,prepArena_length]
  all_goals try simp only [prepArena,ReportingHostRelocation.program,LightTernaryColorPreparation.program_length,List.append_assoc]

private theorem budgets_call {lim : Limits} {radix D E K bDigit a b scaleBase p R F n J nO seed constants depth : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (μ : ℕ→ℤ) (hn : 1≤n) (hbDigit : 1≤bDigit) (hw : (lim.space:ℤ)≤lim.word)
    (hseed : seed+47≤constants) (hspace : constants+3≤lim.space)
    (hword : (LightTernaryInitialBudgets.word K bDigit a b scaleBase n J nO:ℤ)≤lim.word)
    (hd : depth<lim.depth) :
    Meets lim (libraries radix D E K bDigit a b scaleBase p R F raws words maps xl yl zl xr yr zr)
      54 depth [n,J,nO,seed,constants] μ (LightTernaryInitialBudgets.time K)
      (fun r ν=>r=(LightTernaryInitialBudgets.initial K bDigit n J nO:ℤ) ∧
        Seg ν (seed+41) (budgetValues K bDigit n J nO) ∧
        Seg ν constants [(a:ℤ),b,scaleBase] ∧
        ∀x,(x<seed+41∨seed+47≤x)→(x<constants∨constants+3≤x)→ν x=μ x) := by
  have hb:=ReportingHostRelocation.meets
    (LightTernaryInitialBudgets.program_meets μ hn hbDigit hw hseed hspace hword hd)
    (prepArena radix D E)
  have hh:=hb.append ((LightTernaryPrefixLoop.program p R F K raws words maps xl yl zl xr yr zr).map
    (ReportingHostRelocation.relocate 55))
  convert hh using 1
  all_goals try simp only [libraries,ReportingHostRelocation.program,budgetLibrary_length]
  all_goals try simp only [budgetLibrary,ReportingHostRelocation.program,prepArena_length,List.append_assoc]
  all_goals rfl

def time (E K : ℕ) : ℕ :=LightTernaryArenaTemplate.time E+LightTernaryInitialBudgets.time K+2000

/-- Concrete output of both initialization calls, before the actual prefix
initializer copies the seed template into the live header. -/
structure Initialized (D E K bDigit a b scaleBase n U af q J nO : ℕ)
    (xs : List ℤ) (startLoc loc initial ν : ℕ→ℤ) : Prop where
  nread : loc 1=(n:ℤ)
  arena : loc 6=(af:ℤ)
  capacity : loc 7=(TernaryArenaLayout.capacity D E (n+U):ℤ)
  seedTemplate : loc 8=(addr af (TernaryArenaLayout.capacity D E (n+U)) 2:ℤ)
  liveSeed : loc 9=(addr af (TernaryArenaLayout.capacity D E (n+U)) 3:ℤ)
  liveHost : loc 10=(addr af (TernaryArenaLayout.capacity D E (n+U)) 1:ℤ)
  prefixFree : loc 11=(addr af (TernaryArenaLayout.capacity D E (n+U)) 13:ℤ)
  header : loc 5=startLoc 5
  host : Seg ν (addr af (TernaryArenaLayout.capacity D E (n+U)) 0)
    (LightTernaryArenaTemplate.hostValues (frame xs) af (TernaryArenaLayout.capacity D E (n+U)))
  seed : Seg ν (addr af (TernaryArenaLayout.capacity D E (n+U)) 2)
    (budgetedValues (LightTernaryArenaTemplate.seedValues (frame xs) af (TernaryArenaLayout.capacity D E (n+U))) K bDigit n J nO)
  constants : Seg ν (addr af (TernaryArenaLayout.capacity D E (n+U)) 2+48) [(a:ℤ),b,scaleBase]
  kept : Kept initial ν af

def runtimeValues (n p R F : ℕ) (h : ℕ→ℕ) : List ℤ :=
  values n (h 14) (h 13) (h 6) (h 3) (h 7) (h 5) (h 8) (h 9) (h 10)
    (h 18) (h 16) p R F (h 17)

/-- Both libraries are physically executed; the continuation receives the
templates and the six actual budgets computed from n, J and nO. -/
theorem ends_then {lim : Limits} {radix D E K bDigit a b scaleBase p R F n header depth tailTime : ℕ}
    (raws : List ℤ) (words maps : List ℕ) (xl yl zl xr yr zr : List ℤ)
    (suffix : Program) (locals : List ℤ) (μ : ℕ→ℤ) (h : ℕ→ℕ)
    (h1 : frame locals 1=(n:ℤ)) (h5 : frame locals 5=(header:ℤ))
    (hread : ∀i<19,μ (header+i)=(h i:ℤ)) (hHeader : header+19≤h 13)
    (hn : 1≤n) (hbDigit : 1≤bDigit) (hw : (lim.space:ℤ)≤lim.word)
    (hend : finish (h 13) (capacity D E (n+h 14))≤lim.space)
    (hUW : ((n+h 14:ℕ):ℤ)+1≤lim.word) (hEW : (E:ℤ)≤lim.word)
    (hqC : h 17*h 17≤capacity D E (n+h 14))
    (hconstants : p+R+F≤capacity D E (n+h 14))
    (hword : (LightTernaryInitialBudgets.word K bDigit a b scaleBase n (h 16) (h 9):ℤ)≤lim.word)
    (hd : depth+1<lim.depth) (tail : Stmt) (Q : State→Prop)
    (next : ∀σ,Initialized D E K bDigit a b scaleBase n (h 14) (h 13) (h 17) (h 16) (h 9)
      (runtimeValues n p R F h) (frame locals) σ.loc μ σ.mem→
      Ends lim (libraries radix D E K bDigit a b scaleBase p R F raws words maps xl yl zl xr yr zr++suffix)
        depth tail σ tailTime Q) :
    Ends lim (libraries radix D E K bDigit a b scaleBase p R F raws words maps xl yl zl xr yr zr++suffix)
      depth (initChunk p R F tail) ⟨frame locals,μ⟩ (time E K+tailTime) Q := by
  change locals[1]?.getD 0=(n:ℤ) at h1
  change locals[5]?.getD 0=(header:ℤ) at h5
  let af:=h 13
  let C:=capacity D E (n+h 14)
  let xs:=runtimeValues n p R F h
  have endArena : af+67*C≤lim.space := hend
  have hCmin : 256≤C:=capacity_pos D E (n+h 14)
  have hCspace : C≤lim.space:=by change af+67*C≤lim.space at hend;omega
  have hCword : (C:ℤ)≤lim.word := (Int.ofNat_le.mpr hCspace).trans hw
  have haf : af+1<lim.space :=by change af+67*C≤lim.space at hend;omega
  have hHspace : header+19≤lim.space:=by dsimp only [af] at haf;omega
  have hp : (p:ℤ)≤lim.word:=by dsimp only [C] at hCword;omega
  have hR : (R:ℤ)≤lim.word:=by dsimp only [C] at hCword;omega
  have hF : (F:ℤ)≤lim.word:=by dsimp only [C] at hCword;omega
  have htc := (template_call (K:=K) (bDigit:=bDigit) (a:=a) (b:=b) (scaleBase:=scaleBase)
    (p:=p) (R:=R) (F:=F) (D:=D) (E:=E) (radix:=radix)
    raws words maps xl yl zl xr yr zr xs rfl μ rfl rfl rfl hw hend hUW hEW hqC hd).append suffix
  have readI (i : ℤ) (hi : 0 ≤ i) (hj : i < 19) :
      μ ((header:ℤ)+i).toNat=(h i.toNat:ℤ) := by
    rw [show ((header:ℤ)+i).toNat=header+i.toNat by omega]
    exact hread _ (by omega)
  unfold initChunk time H arenaArgs A
  simp only [H]
  light_set af using H,h5,readI,af
  light_call htc using arenaArgs,H,h1,h5,readI,xs,runtimeValues,values,af with rt μt ⟨hrt,host,seed,keep⟩
  have ht (i : ℕ) (hi : i<19) : μt (header+i)=(h i:ℤ) :=
    (keep _ (by dsimp only [af];omega)).trans (hread i hi)
  have readIT (i : ℤ) (hi : 0 ≤ i) (hj : i < 19) :
      μt ((header:ℤ)+i).toNat=(h i.toNat:ℤ) := by
    rw [show ((header:ℤ)+i).toNat=header+i.toNat by omega]
    exact ht _ (by omega)
  have hzero := host.getD (i:=0) (by simp [LightTernaryArenaTemplate.hostValues]) 0
  have hone := host.getD (i:=1) (by simp [LightTernaryArenaTemplate.hostValues]) 0
  simp only [addr,Nat.zero_mul,Nat.add_zero,LightTernaryArenaTemplate.hostValues,
    LightTernaryArenaTemplate.hostFields,List.map_cons,List.map_nil,List.getD_cons_zero,
    List.getD_cons_succ,LightTernaryArenaTemplate.value] at hzero hone
  have hprod (s : ℕ) (hs : s≤67) : s*C≤lim.space := by
    change af+67*C≤lim.space at hend
    nlinarith
  have haddr (s : ℕ) (hs : s≤67) : af+s*C≤lim.space := by
    change af+67*C≤lim.space at hend
    nlinarith
  have hpWord (s : ℕ) (hs : s≤67) : ((s*C:ℕ):ℤ)≤lim.word:=
    (Int.ofNat_le.mpr (hprod s hs)).trans hw
  have haWord (s : ℕ) (hs : s≤67) : ((af+s*C:ℕ):ℤ)≤lim.word:=
    (Int.ofNat_le.mpr (haddr s hs)).trans hw
  have afAddress (i : ℤ) (hi : 0 ≤ i) : ((af:ℤ)+i).toNat=af+i.toNat := by omega
  light_set C using afAddress,hzero,hone,addr,af,C
  light_set (addr af C 2) using A,addr,hpWord 2 (by decide),haWord 2 (by decide)
  light_set (addr af C 3) using A,addr,hpWord 3 (by decide),haWord 3 (by decide)
  light_set (addr af C 1) using A,addr,hpWord 1 (by decide),haWord 1 (by decide)
  light_set (addr af C 13) using A,addr,hpWord 13 (by decide),haWord 13 (by decide)
  have hbSpace : addr af C 2+48+3≤lim.space:=by
    have hh:=region_space (free:=af) (C:=C) (len:=51) (slot:=2)
      (by decide : 2<slots) (show 51≤C by omega) hend
    omega
  have hb := (budgets_call (radix:=radix) (D:=D) (E:=E) (p:=p) (R:=R) (F:=F)
    raws words maps xl yl zl xr yr zr μt hn hbDigit hw
    (show addr af C 2+47≤addr af C 2+48 by omega) hbSpace hword hd).append suffix
  light_call hb using H,h1,h5,readIT with rb ν ⟨hrb,budgets,constants,bkeep⟩
  have hhost : Seg ν (addr af C 0) (LightTernaryArenaTemplate.hostValues (frame xs) af C) := by
    intro i hi
    have hii : i<106:=by simpa [LightTernaryArenaTemplate.hostValues] using hi
    rw [bkeep _ (Or.inl (by unfold addr;omega)) (Or.inl (by unfold addr;omega))]
    exact host i hi
  have hseed := budgeted_segment (seed:=addr af C 2) (constants:=addr af C 2+48)
    (by simp [LightTernaryArenaTemplate.seedValues]) seed budgets bkeep (le_refl _)
  have hkeep : Kept μ ν af := by
    intro x hx
    exact (bkeep x (Or.inl (by unfold addr;omega)) (Or.inl (by unfold addr;omega))).trans (keep x hx)
  refine Ends.mono (next _ ?_) (by light_time) (fun _ h=>h)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hhost,hseed,constants,hkeep⟩
  all_goals simp [State.loc,frame_setLocal,h1,af,C]

end ThreeSum.LightTernaryColoredInitializationProof
