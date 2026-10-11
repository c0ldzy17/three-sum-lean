import Submission.ThreeSum.WeightedScore
import Submission.ThreeSum.ModuloRuntime

/-!
# Executing the weighted modular score

The joint-modulus helper uses the verified division-free remainder routine.
The score loop computes a base count, then visits the auxiliary-prime array
once.  All calls reuse the same scratch region and preserve the original
arrays.  Its intermediate scores are proved nonnegative.

The generic loop theorem exposes the modular-counting execution contract.
The concrete wrapper instantiates that contract with the checked fixed
modular-counting program; no counting operation is added to the machine.
-/

namespace ThreeSum.LightWeightedScore

open Light WeightedModuli WeightedScore LightResidues

variable {lim : Limits} {P : Program} {d : ℕ}

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Arguments: positive base modulus, positive auxiliary modulus, scratch. -/
def jointBody (pEmod : ℕ) : Stmt :=
  .call pEmod [v 0, v 1, v 2] 3 ;;
  .ite (v 3 =' k 0) .skip (.set 0 (v 0 *' v 1))

def jointTime (maxMod : ℕ) : ℕ := residueBudget maxMod + 40

theorem joint_meets {pJoint pEmod : ℕ}
    (hjoint : P[pJoint]? = some (jointBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {q p maxMod free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hq : 0 < q) (hp : 0 < p) (hmax : q*p ≤ maxMod)
    (hspace : free + (Nat.log 2 (maxMod+1)+2) ≤ lim.space)
    (hword : (8*maxMod+16 : ℕ) ≤ lim.word) :
    Meets lim P pJoint d [q,p,free] μ (jointTime maxMod)
      fun r μ' => r = (joint q p : ℤ) ∧ Kept μ μ' free := by
  have hqmax : q ≤ maxMod := (Nat.le_mul_of_pos_right q hp).trans hmax
  have hpmax : p ≤ maxMod := (Nat.le_mul_of_pos_left p hq).trans hmax
  have hpre : Emod.Pre lim p maxMod free := ⟨hp, hw, by
    have hpZ : (p : ℤ) ≤ maxMod := by exact_mod_cast hpmax
    have hwZ : (8*(maxMod : ℤ)+16) ≤ lim.word := by exact_mod_cast hword
    omega, hspace⟩
  have hx : |(q : ℤ)| ≤ (maxMod : ℤ) := by simpa using (Int.ofNat_le.mpr hqmax)
  have ht := emodTime_le (p := p) hx
  simp only [Int.natAbs_natCast] at ht
  unfold emodTime residueBudget at ht
  have hlog : Nat.log 2 (1+maxMod) = Nat.log 2 (maxMod+1) := by rw [Nat.add_comm]
  have hmulZ : (q : ℤ)*(p : ℤ) ≤ lim.word := by
    have hh : ((q*p : ℕ) : ℤ) ≤ (maxMod : ℤ) := by exact_mod_cast hmax
    have hwZ : (8*(maxMod : ℤ)+16) ≤ lim.word := by exact_mod_cast hword
    push_cast at hh
    omega
  apply Meets.of_body hjoint
  unfold jointBody jointTime
  light_call (emod_meets (x := (q : ℤ)) hem hpre hx)
    using residueBudget with result μ₁ ⟨hresult,hkeep⟩
  subst result
  refine Ends.iteLast (fun hz => ?_) (fun hnz => ?_) (by light_side)
    (hT := by light_time [residueBudget])
  · have hdiv : p ∣ q := by
      have hh : (q : ℤ) % (p : ℤ) = 0 := by simpa using hz
      exact Int.natCast_dvd_natCast.mp (Int.dvd_of_emod_eq_zero hh)
    apply Ends.skip
    exact ⟨by simp [joint,hdiv],hkeep⟩
  · have hnot : ¬ p ∣ q := by
      intro hh
      apply hnz
      have he : (q : ℤ) % (p : ℤ) = 0 :=
        Int.emod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mpr hh)
      simpa using he
    light_set (q*p : ℕ) using jointTime, residueBudget
    exact ⟨by simp [joint,hnot],hkeep⟩

/-- Arguments: A, B, C, their lengths, base modulus, maximum array length,
auxiliary-prime array, number of primes, and scratch.
Locals 11 and 12 hold the base count and remaining score; 13 is the loop
counter, and 14 and 15 hold the joint modulus and its count. -/
def body (pCount pJoint : ℕ) : Stmt :=
  .call pCount [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 10] 11 ;;
  .set 12 (v 9 *' v 11) ;;
  .for 13 (v 9) (
    .call pJoint [v 6,M (v 8 +' v 13),v 10] 14 ;;
    .call pCount [v 0,v 1,v 2,v 3,v 4,v 5,v 14,v 7,v 10] 15 ;;
    .set 12 (v 12 -' v 15)) ;;
  .set 0 (v 12)

def time (countTime s maxMod : ℕ) : ℕ :=
  countTime + s*(countTime+jointTime maxMod+100)+100

def Inv (μ : ℕ → ℤ) (primes : ℕ → ℕ)
    (a b c nA nB nC q N aux s free : ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (jval cval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(a : ℤ),b,c,nA,nB,nC,q,N,aux,s,free,
      ModuloCounts.count q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)),
      remaining primes s q nA nB nC (fun j => μ (a+j)) (fun j => μ (b+j))
        (fun j => μ (c+j)) i,i,jval,cval],ν⟩ ∧ Kept μ ν free

theorem meets_of_count_backend {pMain pCount pJoint pEmod : ℕ}
    (hmain : P[pMain]? = some (body pCount pJoint))
    (hjoint : P[pJoint]? = some (jointBody pEmod))
    (hem : P[pEmod]? = some emodBody)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod countTime : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free) (hN : N ≤ lim.space)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space)
    (hword : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word)
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod)
    (hcount : ∀ (ν : ℕ → ℤ) (p : ℕ), Kept μ ν free → 0 < p → p ≤ maxMod →
      Meets lim P pCount (d+1) [a,b,c,nA,nB,nC,p,N,free] ν countTime
        (fun r ν' => r = (ModuloCounts.count p nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept ν ν' free)) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ (time countTime s maxMod)
      fun r μ' => r = (score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free := by
  let A := fun j => μ (a+j)
  let B := fun j => μ (b+j)
  let C := fun j => μ (c+j)
  let base := ModuloCounts.count q nA nB nC A B C
  have hprodN : nA*nB*nC ≤ N^3 := by
    calc
      _ ≤ N*N*N := Nat.mul_le_mul (Nat.mul_le_mul hnA hnB) hnC
      _ = _ := by ring
  have hbase : base ≤ N^3 := (ModuloCounts.count_le q nA nB nC A B C).trans hprodN
  have hbound (i : ℕ) : remaining primes s q nA nB nC A B C i ≤ s*N^3 :=
    (remaining_le primes s q nA nB nC A B C i).trans (Nat.mul_le_mul_left s hprodN)
  have hbaseZ : (base : ℤ) ≤ lim.word := by
    have hm : N^3 ≤ (s+1)*N^3+8*maxMod+16 := by nlinarith
    exact (Int.ofNat_le.mpr (hbase.trans hm)).trans hword
  have hscoreZ (i : ℕ) : (remaining primes s q nA nB nC A B C i : ℤ) ≤ lim.word := by
    have hm : s*N^3 ≤ (s+1)*N^3+8*maxMod+16 := by nlinarith
    exact (Int.ofNat_le.mpr ((hbound i).trans hm)).trans hword
  have hinitZ : ((s*base : ℕ) : ℤ) ≤ lim.word := by
    simpa only [remaining_zero] using hscoreZ 0
  have hinitNonneg : (0 : ℤ) ≤ (s : ℤ) * (base : ℤ) := by positivity
  dsimp [base,A,B,C] at hinitZ hinitNonneg
  have hjword : (8*maxMod+16 : ℕ) ≤ lim.word := by
    have hh : 8*maxMod+16 ≤ (s+1)*N^3+8*maxMod+16 := by omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hNword : (N : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hN).trans hw
  have hmodword : (maxMod : ℤ) ≤ lim.word := by
    have hwZ : (8*(maxMod : ℤ)+16) ≤ lim.word := by exact_mod_cast hjword
    omega
  apply Meets.of_body hmain
  unfold body time
  light_call (hcount μ q (fun _ _ => rfl) hq hqmax)
    using A,B,C,base with res μ₀ ⟨hres,hkept₀⟩
  have hres' : res = (base : ℤ) := hres
  subst res
  light_set (s*base : ℕ) using A,B,C,base
  refine Ends.pieceThen (Ends.for (T := s*(countTime+jointTime maxMod+100)+20)
    (Q := Inv μ primes a b c nA nB nC q N aux s free s)
    (Inv μ primes a b c nA nB nC q N aux s free) s
    (countTime+jointTime maxMod+80) ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · refine ⟨0,0,μ₀,?_,hkept₀⟩
    simp only [Inv,remaining_zero,update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc,μ₀⟩ : State)) (frame_append_zeros _ 2).symm
  · rintro i _ hi _ ⟨jval,cval,ν,rfl,hkept⟩
    have hp := (hprime i hi).pos
    have hpmax : primes i ≤ maxMod :=
      (Nat.le_mul_of_pos_left (primes i) hq).trans (hproduct i hi)
    have hpword : (primes i : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hpmax).trans hmodword
    have hreadν : ν (aux+i) = (primes i : ℤ) := (hkept _ (by omega)).trans (hread i hi)
    have hnext := next_count_le_remaining (q := q) (nA := nA) (nB := nB) (nC := nC)
      primes A B C hi
    have hremaincast := remaining_succ_cast (q := q) (nA := nA) (nB := nB) (nC := nC)
      primes A B C hi
    have hscoreNext := hscoreZ (i+1)
    have hscoreNow := hscoreZ i
    dsimp [A,B,C] at hnext hremaincast hscoreNext hscoreNow
    light_call (joint_meets (d := d+1) (q := q) (p := primes i) hjoint hem hw
      (by omega) hq hp (hproduct i hi) hspace hjword)
      using hreadν,A,B,C,base with jres ν₁ ⟨hjres,hkeep₁⟩
    subst jres
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j hj).trans (hkept j hj)
    have hjpos := joint_positive hq (hprime i hi)
    have hjmax := (joint_le_mul q (primes i) hp).trans (hproduct i hi)
    light_call (hcount ν₁ (joint q (primes i)) hkept₁ hjpos hjmax)
      using A,B,C,base with cres ν₂ ⟨hcres,hkeep₂⟩
    subst cres
    light_set (remaining primes s q nA nB nC A B C (i+1))
      using A,B,C,base,hremaincast
    refine ⟨by simp, (joint q (primes i) : ℤ),
      (ModuloCounts.count (joint q (primes i)) nA nB nC A B C : ℤ),ν₂,?_,?_⟩
    · simp [Inv,update_frame_setLocal,A,B,C,base]
    · intro j hj
      exact (hkeep₂ j hj).trans (hkept₁ j hj)
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨jval,cval,ν,rfl,hkept⟩
    simp
  · rintro σ ⟨jval,cval,ν,rfl,hkept⟩
    have hsc := hscoreZ s
    light_set (remaining primes s q nA nB nC A B C s) using A,B,C,base
    exact ⟨by rw [score_eq_remaining primes s q nA nB nC A B C hprime hinj]; simp,hkept⟩

/-- Time for the score with the actual modular-counting implementation. -/
def runtimeTime (maxMod nA nB nC s U : ℕ) : ℕ :=
  time (LightModuloCounts.time maxMod nA nB nC U) s maxMod

/-- Both helpers reuse the same scratch region, so their reservations take a
maximum. No scratch allocation is multiplied by the number of primes. -/
def space (free maxMod N U : ℕ) : ℕ :=
  max (LightModuloCounts.space free maxMod N U)
    (free + (Nat.log 2 (maxMod+1)+2))

def word (maxMod N s U : ℕ) : ℕ :=
  LightModuloCounts.word maxMod N U + (s+1)*N^3 + 8*maxMod + 16

/-- Syntax-only closure for a weighted-score procedure and its concrete
modular-counting, joint-modulus, and arithmetic procedures. -/
structure Procs (P : Program) (pMain : ℕ) where
  pCount : ℕ
  pJoint : ℕ
  count : LightModuloCounts.Procs P pCount
  main : P[pMain]? = some (body pCount pJoint)
  joint : P[pJoint]? = some (jointBody count.pEmod)

/-- Execute the weighted score on the original signed input arrays. Every
counting premise is discharged by the fixed counting syntax in `C.count`.
The preserved prefix includes the original arrays and the auxiliary primes. -/
theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+4 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (runtimeTime maxMod nA nB nC s U)
      (fun r μ' => r = (score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) := by
  have hcountSpace : LightModuloCounts.space free maxMod N U ≤ lim.space :=
    (Nat.le_max_left _ _).trans hspace
  have hjointSpace : free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space :=
    (Nat.le_max_right _ _).trans hspace
  have hN : N ≤ lim.space := by
    unfold LightModuloCounts.space at hcountSpace
    omega
  have hcountWord : (LightModuloCounts.word maxMod N U : ℤ) ≤ lim.word := by
    have hh : LightModuloCounts.word maxMod N U ≤ word maxMod N s U := by
      unfold word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hscoreWord : ((s+1)*N^3+8*maxMod+16 : ℕ) ≤ lim.word := by
    have hh : (s+1)*N^3+8*maxMod+16 ≤ word maxMod N s U := by
      unfold word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  apply meets_of_count_backend C.main C.joint C.count.emod primes hw (by omega)
    hq hqmax ha hb hc haux hN hnA hnB hnC hjointSpace hscoreWord
    hread hprime hinj hproduct
  intro ν p hkept hp hpmax
  have hAν : ∀ i < nA, |ν (a+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hA i hi
  have hBν : ∀ i < nB, |ν (b+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hB i hi
  have hCν : ∀ i < nC, |ν (c+i)| ≤ (U : ℤ) := by
    intro i hi
    rw [hkept _ (by omega)]
    exact hC i hi
  apply (ModuloRuntime.meets_bounded (d := d+1) C.count hw hp hpmax ha hb hc
    hnA hnB hnC hcountSpace hcountWord (by omega) hAν hBν hCν).mono le_rfl
  intro r ν' ⟨hr,hkeep⟩
  refine ⟨hr.trans ?_,hkeep⟩
  congr 1
  exact WeightedScore.count_congr (fun i hi => hkept _ (by omega))
    (fun i hi => hkept _ (by omega)) (fun i hi => hkept _ (by omega))

/-- A fixed fourteen-procedure program. All recursive and nonrecursive calls
refer to members of this list; no modular-counting oracle is assumed. -/
def program : Program :=
  [body 2 1, jointBody 6, LightModuloCounts.body 3 4 8 5 13,
    LightCapacity.body, LightResidueHistogram.body 5 7, residuesBody 6,
    emodBody, LightHistogram.histogramBody 12, LightCyclic.body 9 11,
    LightKaratsuba.body 9 10 11 12, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]

def program_count_procs : LightModuloCounts.Procs program 2 where
  pCapacity := 3
  pHist := 4
  pCyclic := 8
  pResidues := 5
  pEmod := 6
  pHistogram := 7
  pMultiply := 9
  pHalf := 10
  pLinear := 11
  pFill := 12
  pLookup := 13
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl,rfl,rfl,rfl⟩
  lookup := rfl

def program_procs : Procs program 0 where
  pCount := 2
  pJoint := 1
  count := program_count_procs
  main := rfl
  joint := rfl

theorem program_meets
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U ≤ lim.space)
    (hword : (word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+4 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim program 0 d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (runtimeTime maxMod nA nB nC s U)
      (fun r μ' => r = (score primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) :=
  program_procs.meets primes hw hq hqmax ha hb hc haux hnA hnB hnC hspace hword hd
    hA hB hC hread hprime hinj hproduct

end ThreeSum.LightWeightedScore
