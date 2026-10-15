import Submission.ThreeSum.TernaryWantedLittleEndian
import Submission.ThreeSum.LightSignedFiniteTable
import Submission.ThreeSum.LightTernaryDivide
import Submission.ThreeSum.LightResidues
import Submission.ThreeSum.WantedPairs

namespace ThreeSum.LightTernaryWantedCanonical
open Light
open TernaryWantedRadix (localBucket mem_localBucket localBucket_eq_of_emod wantedOutputs wantedOutputs_length_le child_target_bound codeLimit codeLimit_base codeLimit_child)
open TernaryWantedLittleEndian (wantedCodes wantedCodes_length wantedCodes_succ encode)
set_option maxHeartbeats 4000000
set_option maxRecDepth 18000

/-- Arguments: remaining blocks, signed target, canonical word code and scale,
map-vector code and scale, original requester position, output cursor, scratch.
Both codes accumulate from the least native block upward. -/
def recordSteps (pSelf pDivide P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : List ℕ → Stmt
  | [] => .skip
  | i::is =>
      .call pDivide [v 1 -' LightSignedFiniteTable.literal (raws.getD i 0),k P,v 8] 9 ;;
      .call pSelf [v 0 -' k 1,v 9,v 2 +' v 3 *' k (words.getD i 0),v 3 *' k R,
        v 4 +' v 5 *' k (maps.getD i 0),v 5 *' k S,v 6,v 10,v 8] 10 ;;
      recordSteps pSelf pDivide P R S raws words maps is

def selector (pSelf pDivide P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : List ℕ → Stmt
  | [] => .skip
  | r::rs => .ite (v 11 =' k r)
      (recordSteps pSelf pDivide P R S raws words maps (localBucket (P : ℤ) raws (r : ℤ)))
      (selector pSelf pDivide P R S raws words maps rs)

def body (pSelf pDivide pEmod P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.call pEmod [v 1,k P,v 8] 11 ;;
      .set 10 (v 7) ;;
      selector pSelf pDivide P R S raws words maps (List.range P) ;;
      .set 0 (v 10))
    (.store (v 7) (v 6) ;;
      .store (v 7 +' k 1) (v 2) ;;
      .store (v 7 +' k 2) (v 4) ;;
      .set 0 (v 7 +' k 3))

def program (P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) : Program :=
  [body 0 1 3 P R S raws words maps,LightTernaryDivide.body 2,LightOutputDecodeDivide.body,emodBody]

def overhead (P V : ℕ) : ℕ := LightResidues.residueBudget (2*V)+10*P+40
def stepCost (V : ℕ) : ℕ := LightTernaryDivide.time (2*V)+100

def time (P C V : ℕ) : ℕ → ℕ
  | 0 => 40
  | j+1 => overhead P V+C*(stepCost V+time P C V j)

theorem time_bound (P C V : ℕ) (hC : 1 ≤ C) : ∀ j,
    time P C V j ≤ (overhead P V+stepCost V+40)*(j+1)*C^j := by
  intro j
  induction j with
  | zero => simp [time]
  | succ j ih =>
    have hc := Nat.pow_le_pow_right (by omega : 0 < C) (by omega : 1 ≤ j+1)
    simp only [pow_one] at hc
    have hp := one_le_pow₀ hC (n := j+1)
    have hh : C*time P C V j ≤ (overhead P V+stepCost V+40)*(j+1)*C^(j+1) := by
      simpa [pow_succ',Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using Nat.mul_le_mul_left C ih
    have h1 := Nat.mul_le_mul_left (overhead P V) hp
    have h2 := Nat.mul_le_mul_left (stepCost V) hc
    have hb : overhead P V+C*stepCost V ≤ (overhead P V+stepCost V+40)*C^(j+1) := by
      nlinarith
    calc
      _ = (overhead P V+C*stepCost V)+C*time P C V j := by rw [time]; ring
      _ ≤ (overhead P V+stepCost V+40)*C^(j+1)+
          (overhead P V+stepCost V+40)*(j+1)*C^(j+1) := Nat.add_le_add hb hh
      _ = _ := by ring

variable {lim : Limits} {Prog : Program} {d : ℕ}

/-- The leaf emits original position, canonical word address, and map-vector code. -/
theorem leaf_meets {pMain pDivide pEmod P R S : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hmain : Prog[pMain]? = some (body pMain pDivide pEmod P R S raws words maps))
    (x : ℤ) (code scale mapCode mapScale original dst work : ℕ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : dst+3 ≤ lim.space)
    (hc : (code : ℤ) ≤ lim.word) (hm : (mapCode : ℤ) ≤ lim.word) (ho : (original : ℤ) ≤ lim.word) :
    Meets lim Prog pMain d [0,x,code,scale,mapCode,mapScale,original,dst,work] μ 40
      (fun r ν => r=((dst+3 : ℕ) : ℤ) ∧
        Seg ν dst [(original : ℤ),(code : ℤ),(mapCode : ℤ)] ∧ Kept μ ν dst) := by
  apply Meets.of_body hmain
  unfold body
  light_if hyes hno : (0 : ℕ) < 0
  · omega
  · light_store dst (original : ℕ)
    light_store (dst+1) (code : ℕ)
    light_store (dst+2) (mapCode : ℕ)
    light_set (dst+3 : ℕ)
    refine ⟨rfl,?_,?_⟩
    · simp [seg_cons]
    · light_keep

abbrev rowCells := TernaryWantedCanonicalPairs.rowCells
abbrev rowCells_length := TernaryWantedCanonicalPairs.rowCells_length
abbrev rowCells_append := TernaryWantedCanonicalPairs.rowCells_append

def branchCodes (P R S : ℕ) (raws : List ℤ) (words maps : List ℕ) (j : ℕ) (x : ℤ) (code scale mapCode mapScale : ℕ)
    (is : List ℕ) : List (ℕ × ℕ) := is.flatMap fun i =>
      wantedCodes (P : ℤ) raws words maps j ((x-raws.getD i 0)/(P : ℤ))
        R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S)

theorem recordSteps_ends {pMain pDivide pDecode P R S C V j : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body)
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S)
    (x : ℤ) (code scale mapCode mapScale original baseDst work : ℕ)
    (F : Emod.Pre lim P (2*V) work) (hx : |x| ≤ (V : ℤ))
    (hc : (codeLimit R code scale (j+1) : ℤ) ≤ lim.word)
    (hm : (codeLimit S mapCode mapScale (j+1) : ℤ) ≤ lim.word)
    (ho : (original : ℤ) ≤ lim.word) (hJ : ((j+1 : ℕ) : ℤ) ≤ lim.word)
    (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word) (hNW : (raws.length : ℤ) ≤ lim.word) (hd : d+j+3 ≤ lim.depth)
    (hchild : ∀ (i : ℕ), i ∈ localBucket (P : ℤ) raws x →
      ∀ (dst : ℕ) (ν : ℕ → ℤ), dst+3*C^j ≤ work →
      Meets lim Prog pMain (d+1)
        [j,(x-raws.getD i 0)/(P : ℤ),code+scale*words.getD i 0,scale*R,mapCode+mapScale*maps.getD i 0,mapScale*S,original,dst,work]
        ν (time P C V j)
        (fun r ξ => r=((dst+3*(wantedCodes (P : ℤ) raws words maps j
          ((x-raws.getD i 0)/(P : ℤ)) R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S)).length : ℕ) : ℤ) ∧
          Seg ξ dst (rowCells original (wantedCodes (P : ℤ) raws words maps j
            ((x-raws.getD i 0)/(P : ℤ)) R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S))) ∧
          Kept ν ξ dst)) :
    ∀ (is : List ℕ), (∀ i ∈ is, i ∈ localBucket (P : ℤ) raws x) →
    ∀ (cursor : ℕ) (q residue : ℤ) (μ : ℕ → ℤ), cursor+3*is.length*C^j ≤ work →
      Ends lim Prog d (recordSteps pMain pDivide P R S raws words maps is)
        ⟨frame [j+1,x,code,scale,mapCode,mapScale,original,baseDst,work,q,cursor,residue],μ⟩
        (is.length*(stepCost V+time P C V j))
        (fun σ => ∃ q', σ.loc=frame [j+1,x,code,scale,mapCode,mapScale,original,baseDst,work,q',
          cursor+3*(branchCodes P R S raws words maps j x code scale mapCode mapScale is).length,residue] ∧
          Seg σ.mem cursor (rowCells original (branchCodes P R S raws words maps j x code scale mapCode mapScale is)) ∧
          Kept μ σ.mem cursor) := by
  intro is
  induction is with
  | nil =>
    intro hi cursor q residue μ hs
    exact Ends.skip ⟨q,by simp [branchCodes],by simp [branchCodes,rowCells,TernaryWantedCanonicalPairs.rowCells],
      fun _ _ => rfl⟩
  | cons i is ih =>
    intro hall cursor q residue μ hs
    obtain ⟨hi,hdiv⟩ := (mem_localBucket _ _ _ _).mp (hall i (by simp))
    have hbase := codeLimit_base (code := code) (scale := scale) (j := j+1) hR
    have hcode : (code : ℤ) ≤ lim.word := by omega
    have hscale : (scale : ℤ) ≤ lim.word := by omega
    have hmapbase := codeLimit_base (code := mapCode) (scale := mapScale) (j := j+1) hS
    have hmapCodeW : (mapCode : ℤ) ≤ lim.word := by omega
    have hmapScaleW : (mapScale : ℤ) ≤ lim.word := by omega
    have hchildlim := codeLimit_child (code := code) (scale := scale) (j := j) hR (hwords i hi)
    have hb := codeLimit_base (code := code+scale*words.getD i 0) (scale := scale*R) (j := j) hR
    have hmchild := codeLimit_child (code := mapCode) (scale := mapScale) (j := j) hS (hmaps i hi)
    have hmb := codeLimit_base (code := mapCode+mapScale*maps.getD i 0) (scale := mapScale*S) (j := j) hS
    have hcCode : ((code+scale*words.getD i 0 : ℕ) : ℤ) ≤ lim.word := by omega
    have hcScale : ((scale*R : ℕ) : ℤ) ≤ lim.word := by omega
    have hmCode : ((mapCode+mapScale*maps.getD i 0 : ℕ) : ℤ) ≤ lim.word := by omega
    have hmScale : ((mapScale*S : ℕ) : ℤ) ≤ lim.word := by omega
    have hwordDigit : ((words.getD i 0) : ℤ) ≤ lim.word := by have hh := hwords i hi; omega
    have hmapDigit : ((maps.getD i 0) : ℤ) ≤ lim.word := by have hh := hmaps i hi; omega
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
    have hchildSpace : cursor+3*C^j ≤ work := by
      have hh : 3*C^j ≤ 3*(is.length+1)*C^j := Nat.mul_le_mul_right _ (by omega)
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
    let children := wantedCodes (P : ℤ) raws words maps j ((x-raws.getD i 0)/(P : ℤ))
      R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S)
    have hlen : children.length ≤ C^j := by
      simpa [children,wantedCodes_length] using wantedOutputs_length_le (P : ℤ) raws C hcap j _
    have hsTail : cursor+3*children.length+3*is.length*C^j ≤ work := by
      simp only [List.length_cons] at hs
      have hm := Nat.mul_le_mul_left 3 hlen
      simp only [Nat.mul_add,Nat.add_mul,Nat.mul_one] at hs
      omega
    have ht := ih (fun a ha => hall a (by simp [ha]))
      (cursor+3*children.length) q' residue ξ hsTail
    change Seg ξ cursor (rowCells original children) at hseg
    change result=((cursor+3*children.length : ℕ) : ℤ) at hr
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
theorem selector_ends {pSelf pDivide P R S T r0 : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (l : List ℤ) (μ : ℕ → ℤ) (Q : State → Prop)
    (hres : frame l 11=(r0 : ℤ)) (hword : (r0 : ℤ) ≤ lim.word) :
    ∀ (rs : List ℕ), r0 ∈ rs → (∀ r ∈ rs, (r : ℤ) ≤ lim.word) →
    (∀ r ∈ rs, r0=r → Ends lim Prog d
      (recordSteps pSelf pDivide P R S raws words maps (localBucket (P : ℤ) raws (r : ℤ)))
      ⟨frame l,μ⟩ T Q) →
    Ends lim Prog d (selector pSelf pDivide P R S raws words maps rs) ⟨frame l,μ⟩
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
theorem meets {pMain pDivide pDecode pEmod P R S C V work : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hmain : Prog[pMain]? = some (body pMain pDivide pEmod P R S raws words maps))
    (hdivide : Prog[pDivide]? = some (LightTernaryDivide.body pDecode))
    (hdecode : Prog[pDecode]? = some LightOutputDecodeDivide.body)
    (hem : Prog[pEmod]? = some emodBody)
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S)
    (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word) (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2*V) work) :
    ∀ (J d : ℕ) (x : ℤ) (code scale mapCode mapScale original dst : ℕ) (μ : ℕ → ℤ),
      |x| ≤ (V : ℤ) → (codeLimit R code scale J : ℤ) ≤ lim.word →
      (codeLimit S mapCode mapScale J : ℤ) ≤ lim.word →
      (original : ℤ) ≤ lim.word → (J : ℤ) ≤ lim.word →
      dst+3*C^J ≤ work → d+J+3 ≤ lim.depth →
      Meets lim Prog pMain d [J,x,code,scale,mapCode,mapScale,original,dst,work] μ (time P C V J)
        (fun r ν => r=((dst+3*(wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale).length : ℕ) : ℤ) ∧
          Seg ν dst (rowCells original (wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale)) ∧
          Kept μ ν dst) := by
  intro J
  induction J with
  | zero =>
    intro d x code scale mapCode mapScale original dst μ hx hc hm ho hJ hs hd
    have hw := F.space
    have hf := F.free
    have hs' : dst+3 ≤ lim.space := by simp only [pow_zero] at hs; omega
    have hc' : (code : ℤ) ≤ lim.word := by
      simp only [codeLimit,pow_zero,Nat.mul_one] at hc
      omega
    simpa [time,wantedCodes,wantedOutputs,encode,rowCells,TernaryWantedCanonicalPairs.rowCells] using
      leaf_meets (d := d) hmain x code scale mapCode mapScale original dst work μ hw hs' hc' (by simp only [codeLimit,pow_zero,Nat.mul_one] at hm; omega) ho
  | succ J ih =>
    intro d x code scale mapCode mapScale original dst μ hx hc hm ho hJ hs hd
    light_facts F
    have hb := codeLimit_base (code := code) (scale := scale) (j := J+1) hR
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
    have hcodesLength : (wantedCodes (P : ℤ) raws words maps (J+1) x R S code scale mapCode mapScale).length ≤ C^(J+1) := by
      simpa only [wantedCodes_length] using hlength
    have houtWord : ((dst+3*(wantedCodes (P : ℤ) raws words maps (J+1) x R S code scale mapCode mapScale).length : ℕ) : ℤ) ≤ lim.word := by
      have hh := Nat.mul_le_mul_left 3 hcodesLength
      omega
    apply Meets.of_body hmain
    unfold body
    light_if hyes hno : 0 < J+1 using time,overhead
    · light_call hemod using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm with remainder ν ⟨hrem,hkeepE⟩
      light_set (dst : ℕ) using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm
      simp only [setLocal]
      have hchildren : ∀ i ∈ localBucket (P : ℤ) raws x,
        ∀ (start : ℕ) (ξ : ℕ → ℤ), start+3*C^J ≤ work →
        Meets lim Prog pMain (d+1)
          [J,(x-raws.getD i 0)/(P : ℤ),code+scale*words.getD i 0,scale*R,mapCode+mapScale*maps.getD i 0,mapScale*S,original,start,work]
          ξ (time P C V J)
          (fun r ζ => r=((start+3*(wantedCodes (P : ℤ) raws words maps J
            ((x-raws.getD i 0)/(P : ℤ)) R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S)).length : ℕ) : ℤ) ∧
            Seg ζ start (rowCells original (wantedCodes (P : ℤ) raws words maps J
              ((x-raws.getD i 0)/(P : ℤ)) R S (code+scale*words.getD i 0) (scale*R) (mapCode+mapScale*maps.getD i 0) (mapScale*S))) ∧ Kept ξ ζ start) := by
        intro i hi start ξ hs'
        obtain ⟨hi',hdiv⟩ := (mem_localBucket _ _ _ _).mp hi
        apply ih (d+1) _ _ _ _ _ original start ξ
          (child_target_bound P V hp hx (hraw i hi') hdiv)
          ((Int.ofNat_le.mpr (codeLimit_child hR (hwords i hi'))).trans hc)
          ((Int.ofNat_le.mpr (codeLimit_child hS (hmaps i hi'))).trans hm) ho (by omega) hs' (by omega)
      have hrec := recordSteps_ends (d := d) hdivide hdecode hp hN hR hS hcap hraw hwords hmaps
        x code scale mapCode mapScale original dst work F hx hc hm ho hJ hRW hSW hNW (by omega) hchildren
        (localBucket (P : ℤ) raws x) (fun _ h => h) dst (0 : ℤ) remainder ν
        (by
          have hh := Nat.mul_le_mul_right (3*C^J) (hcap x)
          rw [pow_succ'] at hs
          nlinarith)
      let Q := fun σ : State => ∃ q', σ.loc=frame [J+1,x,code,scale,mapCode,mapScale,original,dst,work,q',
          dst+3*(wantedCodes (P : ℤ) raws words maps (J+1) x R S code scale mapCode mapScale).length,remainder] ∧
          Seg σ.mem dst (rowCells original (wantedCodes (P : ℤ) raws words maps (J+1) x R S code scale mapCode mapScale)) ∧
          Kept ν σ.mem dst
      have hrec' : Ends lim Prog d
          (recordSteps pMain pDivide P R S raws words maps (localBucket (P : ℤ) raws x))
          ⟨frame [J+1,x,code,scale,mapCode,mapScale,original,dst,work,0,dst,remainder],ν⟩
          (C*(stepCost V+time P C V J)) Q := by
        apply hrec.mono (Nat.mul_le_mul_right _ (hcap x))
        intro σ hσ
        simpa only [Q,branchCodes,← wantedCodes_succ] using hσ
      have hsel := selector_ends (d := d) (pSelf := pMain) (pDivide := pDivide) (P := P)
        (R := R) (S := S) (raws := raws) (words := words) (maps := maps) (Prog := Prog) (T := C*(stepCost V+time P C V J))
        [J+1,x,code,scale,mapCode,mapScale,original,dst,work,0,dst,remainder] ν Q
        (by simp [frame,hrem,hrcast]) hrword (List.range P) (by simp [hrlt])
        (fun r hr => by have hh := List.mem_range.mp hr; omega)
        (fun r hr he => by subst r; simpa only [hbuckets] using hrec')
      light_piece hsel using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm with σ ⟨q',hloc,hseg,hkeepS⟩
      cases σ with
      | mk loc mem =>
        dsimp only at hloc hseg hkeepS ⊢
        subst loc
        light_set (dst+3*(wantedCodes (P : ℤ) raws words maps (J+1) x R S code scale mapCode mapScale).length : ℕ) using time,overhead,emodTime,LightResidues.residueBudget,Nat.mul_comm
        refine ⟨rfl,hseg,?_⟩
        intro a ha
        change mem a=μ a
        rw [hkeepS a ha,hkeepE a (by omega)]
    · omega

theorem program_meets {P R S C V work J d : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S)
    (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word) (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2*V) work)
    (x : ℤ) (code scale mapCode mapScale original dst : ℕ) (μ : ℕ → ℤ)
    (hx : |x| ≤ (V : ℤ)) (hc : (codeLimit R code scale J : ℤ) ≤ lim.word)
    (hm : (codeLimit S mapCode mapScale J : ℤ) ≤ lim.word)
    (ho : (original : ℤ) ≤ lim.word) (hJ : (J : ℤ) ≤ lim.word)
    (hs : dst+3*C^J ≤ work) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program P R S raws words maps) 0 d [J,x,code,scale,mapCode,mapScale,original,dst,work] μ (time P C V J)
      (fun r ν => r=((dst+3*(wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale).length : ℕ) : ℤ) ∧
        Seg ν dst (rowCells original (wantedCodes (P : ℤ) raws words maps J x R S code scale mapCode mapScale)) ∧ Kept μ ν dst) :=
  meets rfl rfl rfl rfl hp hN hR hS hC hcap hraw hwords hmaps hRW hSW hNW F J d x code scale mapCode mapScale original dst μ hx hc hm ho hJ hs hd

/-- Uniform start state: every actual representation is emitted directly,
without enumerating the full global output dictionary. -/
theorem program_from_zero {P R S C V work J d : ℕ} {raws : List ℤ} {words maps : List ℕ}
    (hp : 2 ≤ P) (hN : 1 ≤ raws.length) (hR : 1 ≤ R) (hS : 1 ≤ S) (hC : 1 ≤ C)
    (hcap : ∀ x, (localBucket (P : ℤ) raws x).length ≤ C)
    (hraw : ∀ i < raws.length, |raws.getD i 0| ≤ (V : ℤ))
    (hwords : ∀ i < raws.length, words.getD i 0 < R)
    (hmaps : ∀ i < raws.length, maps.getD i 0 < S)
    (hRW : (R : ℤ) ≤ lim.word) (hSW : (S : ℤ) ≤ lim.word)
    (hNW : (raws.length : ℤ) ≤ lim.word) (F : Emod.Pre lim P (2*V) work)
    (x : ℤ) (original dst : ℕ) (μ : ℕ → ℤ)
    (hx : |x| ≤ (V : ℤ)) (hc : (((2*R)^J : ℕ) : ℤ) ≤ lim.word)
    (hm : (((2*S)^J : ℕ) : ℤ) ≤ lim.word)
    (ho : (original : ℤ) ≤ lim.word) (hJ : (J : ℤ) ≤ lim.word)
    (hs : dst+3*C^J ≤ work) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program P R S raws words maps) 0 d [J,x,0,1,0,1,original,dst,work] μ
      ((overhead P V+stepCost V+40)*(J+1)*C^J)
      (fun r ν => r=((dst+3*(wantedCodes (P : ℤ) raws words maps J x R S 0 1 0 1).length : ℕ) : ℤ) ∧
        r ≤ ((dst+3*C^J : ℕ) : ℤ) ∧
        Seg ν dst (rowCells original (wantedCodes (P : ℤ) raws words maps J x R S 0 1 0 1)) ∧
        Kept μ ν dst) := by
  have h := program_meets hp hN hR hS hC hcap hraw hwords hmaps hRW hSW hNW F
    x 0 1 0 1 original dst μ hx (by simpa [codeLimit] using hc)
      (by simpa [codeLimit] using hm) ho hJ hs hd
  apply h.mono (time_bound P C V hC J)
  rintro r ν ⟨hr,hseg,hkeep⟩
  refine ⟨hr,?_,hseg,hkeep⟩
  have hlen : (wantedCodes (P : ℤ) raws words maps J x R S 0 1 0 1).length ≤ C^J := by
    simpa only [wantedCodes_length] using wantedOutputs_length_le (P : ℤ) raws C hcap J x
  rw [hr]
  exact_mod_cast (show dst+3*(wantedCodes (P : ℤ) raws words maps J x R S 0 1 0 1).length ≤ dst+3*C^J by omega)

end ThreeSum.LightTernaryWantedCanonical
