import Submission.ThreeSum.TernaryWantedRadix
import Submission.ThreeSum.LightSignedFiniteTable
import Submission.ThreeSum.LightTernaryDivide
import Submission.ThreeSum.LightResidues
import Submission.ThreeSum.WantedPairs

namespace ThreeSum.LightTernaryWantedDFS
open Light TernaryWantedRadix
set_option maxHeartbeats 2000000
set_option maxRecDepth 18000

/-- Arguments: remaining blocks, signed target, tuple code, tuple digit
scale, original requester position, next output cell, division scratch. -/
def recordSteps (pSelf pDivide P : ℕ) (raws : List ℤ) : List ℕ → Stmt
  | [] => .skip
  | i::is =>
      .call pDivide [v 1 -' LightSignedFiniteTable.literal (raws.getD i 0),k P,v 6] 7 ;;
      .call pSelf [v 0 -' k 1,v 7,v 2 +' v 3 *' k i,
        v 3 *' k raws.length,v 4,v 8,v 6] 8 ;;
      recordSteps pSelf pDivide P raws is

def selector (pSelf pDivide P : ℕ) (raws : List ℤ) : List ℕ → Stmt
  | [] => .skip
  | r::rs => .ite (v 9 =' k r)
      (recordSteps pSelf pDivide P raws (localBucket (P : ℤ) raws (r : ℤ)))
      (selector pSelf pDivide P raws rs)

def body (pSelf pDivide pEmod P : ℕ) (raws : List ℤ) : Stmt :=
  .ite (k 0 <' v 0)
    (.call pEmod [v 1,k P,v 6] 9 ;;
      .set 8 (v 5) ;;
      selector pSelf pDivide P raws (List.range P) ;;
      .set 0 (v 8))
    (.store (v 5) (v 4) ;;
      .store (v 5 +' k 1) (v 2) ;;
      .set 0 (v 5 +' k 2))

def program (P : ℕ) (raws : List ℤ) : Program :=
  [body 0 1 3 P raws,LightTernaryDivide.body 2,LightOutputDecodeDivide.body,emodBody]

def overhead (P V : ℕ) : ℕ := LightResidues.residueBudget (2*V)+10*P+40
def stepCost (V : ℕ) : ℕ := LightTernaryDivide.time (2*V)+100

def time (P C V : ℕ) : ℕ → ℕ
  | 0 => 20
  | j+1 => overhead P V+C*(stepCost V+time P C V j)

theorem time_bound (P C V : ℕ) (hC : 1 ≤ C) : ∀ j,
    time P C V j ≤ (overhead P V+stepCost V+20)*(j+1)*C^j := by
  intro j
  induction j with
  | zero => simp [time]
  | succ j ih =>
    have hc := Nat.pow_le_pow_right (by omega : 0 < C) (by omega : 1 ≤ j+1)
    simp only [pow_one] at hc
    have hp := one_le_pow₀ hC (n := j+1)
    have hh : C*time P C V j ≤ (overhead P V+stepCost V+20)*(j+1)*C^(j+1) := by
      simpa [pow_succ',Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left C ih
    have h1 := Nat.mul_le_mul_left (overhead P V) hp
    have h2 := Nat.mul_le_mul_left (stepCost V) hc
    have hb : overhead P V+C*stepCost V ≤ (overhead P V+stepCost V+20)*C^(j+1) := by
      nlinarith
    calc
      _ = (overhead P V+C*stepCost V)+C*time P C V j := by rw [time]; ring
      _ ≤ (overhead P V+stepCost V+20)*C^(j+1)+
          (overhead P V+stepCost V+20)*(j+1)*C^(j+1) := Nat.add_le_add hb hh
      _ = _ := by ring

variable {lim : Limits} {Prog : Program} {d : ℕ}

/-- The actual leaf emits one original-position/code pair. -/
theorem leaf_meets {pMain pDivide pEmod P : ℕ} {raws : List ℤ}
    (hmain : Prog[pMain]? = some (body pMain pDivide pEmod P raws))
    (x : ℤ) (code scale original dst work : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : dst+2 ≤ lim.space)
    (hc : (code : ℤ) ≤ lim.word) (ho : (original : ℤ) ≤ lim.word) :
    Meets lim Prog pMain d [0,x,code,scale,original,dst,work] μ 20
      (fun r ν => r=((dst+2 : ℕ) : ℤ) ∧
        Seg ν dst [(original : ℤ),(code : ℤ)] ∧ Kept μ ν dst) := by
  apply Meets.of_body hmain
  unfold body
  light_if hyes hno : (0 : ℕ) < 0
  · omega
  · light_store dst (original : ℕ)
    light_store (dst+1) (code : ℕ)
    light_set (dst+2 : ℕ)
    refine ⟨rfl,?_,?_⟩
    · simp [seg_cons]
    · light_keep

def rowCells (original : ℕ) (codes : List ℕ) : List ℤ :=
  WantedPairs.cells (codes.map fun code => (original,code))

@[simp] theorem rowCells_length (original : ℕ) (codes : List ℕ) :
    (rowCells original codes).length=2*codes.length := by
  simp [rowCells,WantedPairs.cells_length]

@[simp] theorem rowCells_append (original : ℕ) (as bs : List ℕ) :
    rowCells original (as++bs)=rowCells original as++rowCells original bs := by
  simp [rowCells,List.map_append,WantedPairs.cells_append]

def branchCodes (P : ℕ) (raws : List ℤ) (j : ℕ) (x : ℤ) (code scale : ℕ)
    (is : List ℕ) : List ℕ := is.flatMap fun i =>
      wantedCodes (P : ℤ) raws j ((x-raws.getD i 0)/(P : ℤ))
        (code+scale*i) (scale*raws.length)

theorem recordSteps_ends {pMain pDivide pDecode P C V j : ℕ} {raws : List ℤ}
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body)
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (x : ℤ) (code scale original baseDst work : ℕ)
    (F : Emod.Pre lim P (2*V) work) (hx : |x| ≤ (V : ℤ))
    (hc : (codeLimit raws.length code scale (j+1) : ℤ) ≤ lim.word)
    (ho : (original : ℤ) ≤ lim.word) (hJ : ((j+1 : ℕ) : ℤ) ≤ lim.word)
    (hNW : (raws.length : ℤ) ≤ lim.word) (hd : d+j+3 ≤ lim.depth)
    (hchild : ∀ (i : ℕ), i ∈ localBucket (P : ℤ) raws x →
      ∀ (dst : ℕ) (ν : ℕ → ℤ), dst+2*C^j ≤ work →
      Meets lim Prog pMain (d+1)
        [j,(x-raws.getD i 0)/(P : ℤ),code+scale*i,scale*raws.length,original,dst,work]
        ν (time P C V j)
        (fun r ξ => r=((dst+2*(wantedCodes (P : ℤ) raws j
          ((x-raws.getD i 0)/(P : ℤ)) (code+scale*i) (scale*raws.length)).length : ℕ) : ℤ) ∧
          Seg ξ dst (rowCells original (wantedCodes (P : ℤ) raws j
            ((x-raws.getD i 0)/(P : ℤ)) (code+scale*i) (scale*raws.length))) ∧
          Kept ν ξ dst)) :
    ∀ (is : List ℕ), (∀ i ∈ is, i ∈ localBucket (P : ℤ) raws x) →
    ∀ (cursor : ℕ) (q residue : ℤ) (μ : ℕ → ℤ), cursor+2*is.length*C^j ≤ work →
      Ends lim Prog d (recordSteps pMain pDivide P raws is)
        ⟨frame [j+1,x,code,scale,original,baseDst,work,q,cursor,residue],μ⟩
        (is.length*(stepCost V+time P C V j))
        (fun σ => ∃ q', σ.loc=frame [j+1,x,code,scale,original,baseDst,work,q',
          cursor+2*(branchCodes P raws j x code scale is).length,residue] ∧
          Seg σ.mem cursor (rowCells original (branchCodes P raws j x code scale is)) ∧
          Kept μ σ.mem cursor) := by
  intro is
  induction is with
  | nil =>
    intro hi cursor q residue μ hs
    exact Ends.skip ⟨q,by simp [branchCodes],by simp [branchCodes,rowCells,WantedPairs.cells],
      fun _ _ => rfl⟩
  | cons i is ih =>
    intro hall cursor q residue μ hs
    obtain ⟨hi,hdiv⟩ := (mem_localBucket _ _ _ _).mp (hall i (by simp))
    have hbase := codeLimit_base (code := code) (scale := scale) (j := j+1) hN
    have hcode : (code : ℤ) ≤ lim.word := by omega
    have hscale : (scale : ℤ) ≤ lim.word := by omega
    have hchildlim := codeLimit_child (code := code) (scale := scale) (j := j) hN hi
    have hb := codeLimit_base (code := code+scale*i) (scale := scale*raws.length) (j := j) hN
    have hcCode : ((code+scale*i : ℕ) : ℤ) ≤ lim.word := by omega
    have hcScale : ((scale*raws.length : ℕ) : ℤ) ≤ lim.word := by omega
    have hiW : (i : ℤ) ≤ lim.word := by omega
    have hcursor : (cursor : ℤ) ≤ lim.word := by
      have hf := F.free
      have hw := F.space
      omega
    have htarget := hraw i hi
    have hdiff : |x-raws.getD i 0| ≤ ((2*V : ℕ) : ℤ) := by
      have hh : |x-raws.getD i 0| ≤ |x|+|raws.getD i 0| := by
        simpa using abs_sub_le x 0 (raws.getD i 0)
      push_cast
      linarith
    have ha : (x-raws.getD i 0).natAbs ≤ 2*V := by
      simpa only [← Int.natCast_natAbs,Nat.cast_le] using hdiff
    have heq : x-raws.getD i 0=(P : ℤ)*((x-raws.getD i 0)/(P : ℤ)) :=
      (Int.mul_ediv_cancel' hdiv).symm
    have hdivcall := LightTernaryDivide.meets (d := d+1) hdivide hdecode μ F ha heq (by omega)
    have hpW : (P : ℤ) ≤ lim.word := by have hh:=F.word; omega
    have hworkW : (work : ℤ) ≤ lim.word := by have hh:=F.free; have hh':=F.space; omega
    have hvW : (V : ℤ) ≤ lim.word := by have hh:=F.word; omega
    have hdiffBounds := abs_le.mp hdiff
    have hxBounds := abs_le.mp hx
    have hrawBounds := abs_le.mp htarget
    have hpos : ((raws.getD i 0).toNat : ℤ) ≤ lim.word := by omega
    have hneg : ((-raws.getD i 0).toNat : ℤ) ≤ lim.word := by omega
    have hlit := Int.toNat_sub_toNat_neg (raws.getD i 0)
    have hchildSpace : cursor+2*C^j ≤ work := by
      have hh : 2*C^j ≤ 2*(is.length+1)*C^j := Nat.mul_le_mul_right _ (by omega)
      simp only [List.length_cons] at hs
      omega
    have hquot := child_target_bound P V hp hx htarget hdiv
    have hquotBounds := abs_le.mp hquot
    simp only [List.getD] at hdiffBounds hrawBounds hpos hneg hlit hquotBounds
    light_facts F
    simp only [List.getD] at *
    rw [recordSteps]
    light_call hdivcall using LightSignedFiniteTable.literal,hlit,stepCost,time with q' ν ⟨hq',hkeepD⟩
    have hcc := hchild i (hall i (by simp)) cursor ν hchildSpace
    light_call hcc using hq',stepCost,time,LightSignedFiniteTable.literal with result ξ ⟨hr,hseg,hkeepC⟩
    let children := wantedCodes (P : ℤ) raws j ((x-raws.getD i 0)/(P : ℤ))
      (code+scale*i) (scale*raws.length)
    have hlen : children.length ≤ C^j := by
      simpa [children,wantedCodes_length] using wantedOutputs_length_le (P : ℤ) raws C hcap j _
    have hsTail : cursor+2*children.length+2*is.length*C^j ≤ work := by
      simp only [List.length_cons] at hs
      have hm := Nat.mul_le_mul_left 2 hlen
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at hs
      omega
    have ht := ih (fun a ha => hall a (by simp [ha]))
      (cursor+2*children.length) q' residue ξ hsTail
    change Seg ξ cursor (rowCells original children) at hseg
    change result=((cursor+2*children.length : ℕ) : ℤ) at hr
    simp only [setLocal,hr]
    apply ht.mono (by simp [stepCost,LightSignedFiniteTable.literal,Expr.cost,List.length_cons,Nat.add_mul]; omega)
    rintro σ ⟨q'',hloc,hsegT,hkeepT⟩
    refine ⟨q'',?_,?_,?_⟩
    · simpa only [branchCodes,List.flatMap_cons,List.length_append,children,
        Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Int.mul_add,Int.add_assoc] using hloc
    · simp only [branchCodes,List.flatMap_cons,rowCells_append]
      apply seg_append.mpr
      constructor
      · change Seg σ.mem cursor (rowCells original children)
        intro a ha
        rw [hkeepT (cursor+a) (by rw [rowCells_length] at ha; omega)]
        exact hseg a ha
      · simpa only [rowCells_length,branchCodes] using hsegT
    · intro a ha
      rw [hkeepT a (by omega),hkeepC a ha,hkeepD a (by omega)]

/-- The selector visits only the chosen fixed residue bucket. -/
theorem selector_ends {pSelf pDivide P T r0 : ℕ} {raws : List ℤ}
    (l : List ℤ) (μ : ℕ → ℤ) (Q : State → Prop)
    (hres : frame l 9=(r0 : ℤ)) (hword : (r0 : ℤ) ≤ lim.word) :
    ∀ (rs : List ℕ), r0 ∈ rs → (∀ r ∈ rs, (r : ℤ) ≤ lim.word) →
    (∀ r ∈ rs, r0=r → Ends lim Prog d
      (recordSteps pSelf pDivide P raws (localBucket (P : ℤ) raws (r : ℤ)))
      ⟨frame l,μ⟩ T Q) →
    Ends lim Prog d (selector pSelf pDivide P raws rs) ⟨frame l,μ⟩
      (T+5*rs.length) Q := by
  simp only [frame,List.getD] at hres
  intro rs
  induction rs with
  | nil => intro hh; simp at hh
  | cons r rs ih =>
    intro hh hb hs
    have hr := hb r (by simp)
    rw [selector]
    refine Ends.iteLast (fun he => ?_) (fun hn => ?_)
    · have he' : (r0 : ℤ)=(r : ℤ) := by simpa [Cond.Holds,Expr.val,hres] using he
      have heN : r0=r := by exact_mod_cast he'
      exact (hs r (by simp) heN).mono (by simp [Cond.cost,Expr.cost]; omega) (fun _ h => h)
    · have hn' : r0 ≠ r := by
        intro heN
        apply hn
        simp [Cond.Holds,Expr.val,hres,heN]
      have hh' : r0 ∈ rs := by simpa [hn'] using hh
      exact (ih hh' (fun a ha => hb a (by simp [ha]))
        (fun a ha heN => hs a (by simp [ha]) heN)).mono
        (by simp [Cond.cost,Expr.cost]; omega) (fun _ h => h)

/-- A real program enumerates only the target's carry-compatible radix tuples. -/
theorem meets {pMain pDivide pDecode pEmod P C V work : ℕ} {raws : List ℤ}
    (hmain : Prog[pMain]? = some (body pMain pDivide pEmod P raws))
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body)
    (hem : Prog[pEmod]? = some emodBody)
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2*V) work) :
    ∀ (J d : ℕ) (x : ℤ) (code scale original dst : ℕ) (μ : ℕ → ℤ),
      |x| ≤ (V : ℤ) → (codeLimit raws.length code scale J : ℤ) ≤ lim.word →
      (original : ℤ) ≤ lim.word → (J : ℤ) ≤ lim.word →
      dst+2*C^J ≤ work → d+J+3 ≤ lim.depth →
      Meets lim Prog pMain d [J,x,code,scale,original,dst,work] μ (time P C V J)
        (fun r ν => r=((dst+2*(wantedCodes (P : ℤ) raws J x code scale).length : ℕ) : ℤ) ∧
          Seg ν dst (rowCells original (wantedCodes (P : ℤ) raws J x code scale)) ∧
          Kept μ ν dst) := by
  intro J
  induction J with
  | zero =>
    intro d x code scale original dst μ hx hc ho hJ hs hd
    have hw := F.space
    have hf := F.free
    have hs' : dst+2 ≤ lim.space := by simp only [pow_zero] at hs; omega
    have hc' : (code : ℤ) ≤ lim.word := by
      simp only [codeLimit,pow_zero,Nat.mul_one] at hc
      omega
    simpa [time,wantedCodes,wantedOutputs,encode,rowCells,WantedPairs.cells] using
      leaf_meets (d := d) hmain x code scale original dst work μ hw hs' hc' ho
  | succ J ih =>
    intro d x code scale original dst μ hx hc ho hJ hs hd
    light_facts F
    have hb := codeLimit_base (code := code) (scale := scale) (j := J+1) hN
    have hcode : (code : ℤ) ≤ lim.word := by omega
    have hscale : (scale : ℤ) ≤ lim.word := by omega
    have hdst : (dst : ℤ) ≤ lim.word := by omega
    have hwork : (work : ℤ) ≤ lim.word := by omega
    have hP : (P : ℤ) ≤ lim.word := by omega
    have hx2 : |x| ≤ ((2*V : ℕ) : ℤ) := by omega
    have hxBounds := abs_le.mp hx
    have hemod := emod_meets (d := d+1) (μ := μ) (x := x) hem F hx2
    have hemodTime := LightResidues.emodTime_le (p := P) hx2
    simp only [emodTime,LightResidues.residueBudget,Nat.mul_comm] at hemodTime
    let r0 := (x % (P : ℤ)).toNat
    have hrcast : (r0 : ℤ)=x % (P : ℤ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
    have hrlt : r0 < P := by
      have hh := Int.emod_lt_of_pos x (by omega : (0 : ℤ)<P)
      omega
    have hrword : (r0 : ℤ) ≤ lim.word := by omega
    have hbuckets : localBucket (P : ℤ) raws (r0 : ℤ)=localBucket (P : ℤ) raws x := by
      apply localBucket_eq_of_emod raws
      rw [hrcast,Int.emod_emod]
    have hlength := wantedOutputs_length_le (P : ℤ) raws C hcap (J+1) x
    have hcodesLength : (wantedCodes (P : ℤ) raws (J+1) x code scale).length ≤ C^(J+1) := by
      simpa only [wantedCodes_length] using hlength
    have houtWord : ((dst+2*(wantedCodes (P : ℤ) raws (J+1) x code scale).length : ℕ) : ℤ) ≤ lim.word := by
      have hh := Nat.mul_le_mul_left 2 hcodesLength
      omega
    apply Meets.of_body hmain
    unfold body
    light_if hyes hno : 0 < J+1 using time,overhead
    · light_call hemod using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm with remainder ν ⟨hrem,hkeepE⟩
      light_set (dst : ℕ) using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm
      simp only [setLocal]
      have hchildren : ∀ i ∈ localBucket (P : ℤ) raws x,
        ∀ (start : ℕ) (ξ : ℕ → ℤ), start+2*C^J ≤ work →
        Meets lim Prog pMain (d+1)
          [J,(x-raws.getD i 0)/(P : ℤ),code+scale*i,scale*raws.length,original,start,work]
          ξ (time P C V J)
          (fun r ζ => r=((start+2*(wantedCodes (P : ℤ) raws J
            ((x-raws.getD i 0)/(P : ℤ)) (code+scale*i) (scale*raws.length)).length : ℕ) : ℤ) ∧
            Seg ζ start (rowCells original (wantedCodes (P : ℤ) raws J
              ((x-raws.getD i 0)/(P : ℤ)) (code+scale*i) (scale*raws.length))) ∧ Kept ξ ζ start) := by
        intro i hi start ξ hs'
        obtain ⟨hi',hdiv⟩ := (mem_localBucket _ _ _ _).mp hi
        apply ih (d+1) _ _ _ original start ξ
          (child_target_bound P V hp hx (hraw i hi') hdiv)
          ((Int.ofNat_le.mpr (codeLimit_child hN hi')).trans hc) ho (by omega) hs' (by omega)
      have hrec := recordSteps_ends (d := d) hdivide hdecode hp hN hcap hraw
        x code scale original dst work F hx hc ho hJ hNW (by omega) hchildren
        (localBucket (P : ℤ) raws x) (fun _ h => h) dst (0 : ℤ) remainder ν
        (by
          have hh := Nat.mul_le_mul_right (2*C^J) (hcap x)
          rw [pow_succ'] at hs
          nlinarith)
      let Q := fun σ : State => ∃ q', σ.loc=frame [J+1,x,code,scale,original,dst,work,q',
          dst+2*(wantedCodes (P : ℤ) raws (J+1) x code scale).length,remainder] ∧
          Seg σ.mem dst (rowCells original (wantedCodes (P : ℤ) raws (J+1) x code scale)) ∧
          Kept ν σ.mem dst
      have hrec' : Ends lim Prog d
          (recordSteps pMain pDivide P raws (localBucket (P : ℤ) raws x))
          ⟨frame [J+1,x,code,scale,original,dst,work,0,dst,remainder],ν⟩
          (C*(stepCost V+time P C V J)) Q := by
        apply hrec.mono (Nat.mul_le_mul_right _ (hcap x))
        intro σ hσ
        simpa only [Q,branchCodes,← wantedCodes_succ] using hσ
      have hsel := selector_ends (d := d) (pSelf := pMain) (pDivide := pDivide) (P := P)
        (raws := raws) (Prog := Prog) (T := C*(stepCost V+time P C V J))
        [J+1,x,code,scale,original,dst,work,0,dst,remainder] ν Q
        (by simp [frame,hrem,hrcast]) hrword (List.range P) (by simp [hrlt])
        (fun r hr => by have hh := List.mem_range.mp hr; omega)
        (fun r hr he => by subst r; simpa only [hbuckets] using hrec')
      light_piece hsel using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm with σ ⟨q',hloc,hseg,hkeepS⟩
      cases σ with
      | mk loc mem =>
        dsimp only at hloc hseg hkeepS ⊢
        subst loc
        light_set (dst+2*(wantedCodes (P : ℤ) raws (J+1) x code scale).length : ℕ) using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm
        refine ⟨rfl,hseg,?_⟩
        intro a ha
        change mem a=μ a
        rw [hkeepS a ha,hkeepE a (by omega)]
    · omega

theorem program_meets {P C V work J d : ℕ} {raws : List ℤ}
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2*V) work)
    (x : ℤ) (code scale original dst : ℕ) (μ : ℕ → ℤ)
    (hx : |x| ≤ (V : ℤ)) (hc : (codeLimit raws.length code scale J : ℤ) ≤ lim.word)
    (ho : (original : ℤ) ≤ lim.word) (hJ : (J : ℤ) ≤ lim.word)
    (hs : dst+2*C^J ≤ work) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program P raws) 0 d [J,x,code,scale,original,dst,work] μ (time P C V J)
      (fun r ν => r=((dst+2*(wantedCodes (P : ℤ) raws J x code scale).length : ℕ) : ℤ) ∧
        Seg ν dst (rowCells original (wantedCodes (P : ℤ) raws J x code scale)) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl rfl hp hN hC hcap hraw hNW F J d x code scale original dst μ hx hc ho hJ hs hd

end ThreeSum.LightTernaryWantedDFS
