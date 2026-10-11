import Submission.ThreeSum.LightPrimeMinimum
import Submission.ThreeSum.PrimeChain

/-!
# Executing a deterministic chain of contracting moduli

Each level runs the concrete prime-score minimum program and multiplies the
current modulus by its returned prime. The exact finite contraction theorem
applies to this executed choice, with all original triple multiplicities.
-/

namespace ThreeSum.LightPrimeChain

open Light WeightedScore LightPrimeMinimum Finset
open scoped BigOperators

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def modulus (primes : ℕ → ℕ) (s nA nB nC : ℕ) (A B C : ℕ → ℤ) : ℕ → ℕ
  | 0 => 1
  | r+1 =>
    let q := modulus primes s nA nB nC A B C r
    q * chosenPrime primes s q nA nB nC A B C

theorem modulus_congr {primes : ℕ → ℕ} {s nA nB nC : ℕ}
    {A A' B B' C C' : ℕ → ℤ}
    (ha : ∀ i < nA, A i = A' i) (hb : ∀ i < nB, B i = B' i)
    (hc : ∀ i < nC, C i = C' i) (r : ℕ) :
    modulus primes s nA nB nC A B C r = modulus primes s nA nB nC A' B' C' r := by
  induction r with
  | zero => rfl
  | succ r ih =>
      simp only [modulus,ih]
      rw [chosenPrime_congr ha hb hc]

theorem modulus_pos (primes : ℕ → ℕ) {s nA nB nC : ℕ}
    (A B C : ℕ → ℤ) (hs : 0 < s)
    (hprime : ∀ i < s, Nat.Prime (primes i)) (r : ℕ) :
    0 < modulus primes s nA nB nC A B C r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
      exact Nat.mul_pos ih
        (hprime _ (chosenIndex_lt primes A B C hs)).pos

theorem modulus_bounds (primes : ℕ → ℕ) {s nA nB nC : ℕ}
    (A B C : ℕ → ℤ) (hs : 0 < s) (y Y r : ℕ)
    (hlo : ∀ i < s, y ≤ primes i) (hhi : ∀ i < s, primes i ≤ Y) :
    y^r ≤ modulus primes s nA nB nC A B C r ∧
      modulus primes s nA nB nC A B C r ≤ Y^r := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
      have hidx := chosenIndex_lt (q := modulus primes s nA nB nC A B C r)
        (nA := nA) (nB := nB) (nC := nC) primes A B C hs
      constructor
      · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.1 (hlo _ hidx)
      · simpa only [modulus,pow_succ,chosenPrime] using Nat.mul_le_mul ih.2 (hhi _ hidx)

/-- Convert the finite-prime averaging theorem to the actual array order. -/
theorem sum_scores_le_log (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    (∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C) ≤
      Nat.log y M * score primes s q nA nB nC A B C := by
  let pool := auxiliarySet primes s
  have hpr : ∀ p ∈ pool, Nat.Prime p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hprime i (mem_range.mp hi)
  have hlow : ∀ p ∈ pool, y ≤ p := by
    intro p hp
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hp
    exact hlo i (mem_range.mp hi)
  have hsum : (∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C) =
      ∑ p ∈ pool, score primes s (q*p) nA nB nC A B C := by
    symm
    unfold pool auxiliarySet
    rw [sum_image]
    intro i hi j hj heq
    exact hinj i (mem_range.mp hi) j (mem_range.mp hj) heq
  rw [hsum]
  have havg := PrimeChain.sum_scores_le_log (ModuloCounts.triples nA nB nC)
    (ModuloCounts.difference A B C) (Arithmetic.missWeight (Auxiliary.moduli pool))
    (Arithmetic.missWeight_zero _) pool q y M hy hpr hlow hbound
  simpa only [PrimeChain.score_eq_weightedFalseCount,score,pool] using havg

theorem chosenPrime_contracts (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    s * score primes s (q*chosenPrime primes s q nA nB nC A B C) nA nB nC A B C ≤
      Nat.log y M * score primes s q nA nB nC A B C := by
  calc
    _ = ∑ _i ∈ range s,
        score primes s (q*chosenPrime primes s q nA nB nC A B C) nA nB nC A B C := by simp
    _ ≤ ∑ i ∈ range s, score primes s (q*primes i) nA nB nC A B C := by
      exact sum_le_sum fun i hi => chosenPrime_min primes s q nA nB nC A B C (mem_range.mp hi)
    _ ≤ _ := sum_scores_le_log primes s q nA nB nC A B C y M hy hprime hinj hlo hbound

/-- Exact contraction for the same minimum choices returned by the program. -/
theorem modulus_score_bound (primes : ℕ → ℕ) (s nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (y M r : ℕ) (hy : 1 < y)
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hlo : ∀ i < s, y ≤ primes i)
    (hbound : ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ M) :
    s^r * score primes s (modulus primes s nA nB nC A B C r) nA nB nC A B C ≤
      (Nat.log y M)^r * score primes s 1 nA nB nC A B C := by
  induction r with
  | zero => simp [modulus]
  | succ r ih =>
      let q := modulus primes s nA nB nC A B C r
      have hstep := chosenPrime_contracts primes s q nA nB nC A B C y M
        hy hprime hinj hlo hbound
      calc
        _ = s^r * (s * score primes s
            (q*chosenPrime primes s q nA nB nC A B C) nA nB nC A B C) := by
          simp only [modulus,q,pow_succ]
          ring
        _ ≤ s^r * (Nat.log y M * score primes s q nA nB nC A B C) :=
          Nat.mul_le_mul_left _ hstep
        _ = Nat.log y M * (s^r * score primes s q nA nB nC A B C) := by ring
        _ ≤ Nat.log y M * ((Nat.log y M)^r * score primes s 1 nA nB nC A B C) :=
          Nat.mul_le_mul_left _ ih
        _ = _ := by ring

theorem difference_bound {nA nB nC U : ℕ} {A B C : ℕ → ℤ}
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    ∀ t ∈ ModuloCounts.triples nA nB nC,
      (ModuloCounts.difference A B C t).natAbs ≤ 3*U := by
  intro t ht
  simp only [ModuloCounts.triples,mem_product,mem_range] at ht
  have ha := abs_le.mp (hA _ ht.1)
  have hb := abs_le.mp (hB _ ht.2.1)
  have hc := abs_le.mp (hC _ ht.2.2)
  have hh : |ModuloCounts.difference A B C t| ≤ (3*U : ℤ) := by
    unfold ModuloCounts.difference
    exact abs_le.mpr ⟨by omega,by omega⟩
  rw [← Int.natCast_natAbs] at hh
  exact_mod_cast hh

/-- Arguments: A, B, C, their lengths, maximum length, prime array, its length,
number of levels, and the first free address. The prefix moduli occupy the
next `levels+1` cells. Every helper reuses the region beyond those cells. -/
def body (pMinimum : ℕ) : Stmt :=
  .set 11 (k 1) ;;
  .set 14 (v 10 +' v 9 +' k 1) ;;
  .store (v 10) (v 11) ;;
  .for 12 (v 9) (
    .call pMinimum [v 0,v 1,v 2,v 3,v 4,v 5,v 11,v 6,v 7,v 8,v 14] 13 ;;
    .set 11 (v 11 *' v 13) ;;
    .store (v 10 +' v 12 +' k 1) (v 11)) ;;
  .set 0 (v 11)

def time (maxMod nA nB nC s U levels : ℕ) : ℕ :=
  levels*(LightPrimeMinimum.time maxMod nA nB nC s U+100)+100

def space (free maxMod N U levels : ℕ) : ℕ :=
  LightWeightedScore.space (free+levels+1) maxMod N U

def Inv (μ : ℕ → ℤ) (qs : ℕ → ℕ)
    (a b c nA nB nC N aux s levels free : ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (pval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(a : ℤ),b,c,nA,nB,nC,N,aux,s,levels,free,
      qs i,i,pval,free+levels+1],ν⟩ ∧
      (∀ j ≤ i, ν (free+j) = (qs j : ℤ)) ∧ Kept μ ν free

structure Procs (P : Program) (pMain : ℕ) where
  pMinimum : ℕ
  minimum : LightPrimeMinimum.Procs P pMinimum
  main : P[pMain]? = some (body pMinimum)

variable {lim : Limits} {P : Program} {d : ℕ}

/-- Execute every level of the deterministic modulus chain, retaining every
prefix modulus and preserving all original cells below `free`. -/
theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC N aux s levels free maxMod U Y : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U levels ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+6 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y^(levels+1) ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,N,aux,s,levels,free] μ
      (time maxMod nA nB nC s U levels)
      (fun r μ' =>
        r = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) levels : ℤ) ∧
        (∀ i ≤ levels, μ' (free+i) = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) i : ℤ)) ∧
        Kept μ μ' free) := by
  let A := fun j => μ (a+j)
  let B := fun j => μ (b+j)
  let C := fun j => μ (c+j)
  let qs := modulus primes s nA nB nC A B C
  let ct := LightPrimeMinimum.time maxMod nA nB nC s U
  have hwork : free+levels+1 ≤ lim.space := by
    have hh := (Nat.le_max_right _ _).trans hspace
    change free+levels+1+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hY : 1 ≤ Y := (hprime 0 hs).one_lt.le.trans (hhi 0 hs)
  have hqpos (i : ℕ) : 0 < qs i := modulus_pos primes A B C hs hprime i
  have hqhi (i : ℕ) : qs i ≤ Y^i :=
    (modulus_bounds primes A B C hs 0 Y i (fun _ _ => Nat.zero_le _) hhi).2
  have hmaxWord : (maxMod : ℤ) ≤ lim.word := by
    have hh : maxMod ≤ LightWeightedScore.word maxMod N s U := by
      unfold LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hqWord (i : ℕ) (hi : i ≤ levels) : (qs i : ℤ) ≤ lim.word := by
    have hh : qs i ≤ maxMod := (hqhi i).trans
      ((Nat.pow_le_pow_right hY (by omega : i ≤ levels+1)).trans hmax)
    exact (Int.ofNat_le.mpr hh).trans hmaxWord
  have hproducts (i : ℕ) (hi : i < levels) :
      ∀ j < s, ∀ k < s, qs i*primes j*primes k ≤ maxMod := by
    intro j hj k hk
    calc
      _ ≤ Y^i*Y*Y := Nat.mul_le_mul (Nat.mul_le_mul (hqhi i) (hhi j hj)) (hhi k hk)
      _ = Y^(i+2) := by simp [pow_succ]
      _ ≤ Y^(levels+1) := Nat.pow_le_pow_right hY (by omega)
      _ ≤ maxMod := hmax
  apply Meets.of_body S.main
  unfold body time
  light_set 1
  light_set (free+levels+1)
  light_store free (1 : ℕ)
  refine Ends.pieceThen (Ends.for (T := levels*(ct+100)+20)
    (Q := Inv μ qs a b c nA nB nC N aux s levels free levels)
    (Inv μ qs a b c nA nB nC N aux s levels free) levels (ct+80)
    ?_ ?_ ?_ ?_ (hT := by light_time [ct])) ?_ (hT := by light_time [ct])
  · refine ⟨0,Function.update μ free (1 : ℤ),?_,?_,?_⟩
    · simp [qs,modulus,update_frame_setLocal]
    · intro j hj
      have hj0 : j = 0 := by omega
      simp [hj0,qs,modulus]
    · intro j hj
      exact Function.update_of_ne (by omega) _ _
  · rintro i _ hi _ ⟨pval,ν,rfl,hwritten,hkept⟩
    have hAν : ∀ j < nA, |ν (a+j)| ≤ (U : ℤ) := by
      intro j hj
      rw [hkept _ (by omega)]
      exact hA j hj
    have hBν : ∀ j < nB, |ν (b+j)| ≤ (U : ℤ) := by
      intro j hj
      rw [hkept _ (by omega)]
      exact hB j hj
    have hCν : ∀ j < nC, |ν (c+j)| ≤ (U : ℤ) := by
      intro j hj
      rw [hkept _ (by omega)]
      exact hC j hj
    have hreadν : ∀ j < s, ν (aux+j) = (primes j : ℤ) := by
      intro j hj
      exact (hkept _ (by omega)).trans (hread j hj)
    light_call (S.minimum.meets (d := d+1) (q := qs i) (free := free+levels+1)
      primes hw (hqpos i) hs (by omega) (by omega) (by omega) (by omega)
      hnA hnB hnC hspace hword (by omega) hAν hBν hCν hreadν hprime hinj (hproducts i hi))
      using ct with result ν₁ ⟨hresult,hkeep₁⟩
    have hchosen : chosenPrime primes s (qs i) nA nB nC
        (fun j => ν (a+j)) (fun j => ν (b+j)) (fun j => ν (c+j)) =
        chosenPrime primes s (qs i) nA nB nC A B C :=
      chosenPrime_congr (fun j hj => hkept _ (by omega))
        (fun j hj => hkept _ (by omega)) (fun j hj => hkept _ (by omega))
    rw [hchosen] at hresult
    subst result
    have hnext := hqWord (i+1) (by omega)
    have hprodWord : (qs i : ℤ)*(chosenPrime primes s (qs i) nA nB nC A B C : ℤ) ≤
        lim.word := by simpa only [qs,modulus,Nat.cast_mul] using hnext
    have hprodNonneg : (0 : ℤ) ≤
        (qs i : ℤ)*(chosenPrime primes s (qs i) nA nB nC A B C : ℤ) := by positivity
    dsimp only [qs] at hprodWord hprodNonneg
    light_set (qs (i+1)) using qs,modulus,ct
    light_store (free+i+1) (qs (i+1)) using ct
    refine ⟨by simp,chosenPrime primes s (qs i) nA nB nC A B C,
      Function.update ν₁ (free+i+1) (qs (i+1) : ℤ),?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro j hj
      by_cases heq : j = i+1
      · simp [heq,Nat.add_assoc]
      · rw [Function.update_of_ne (by omega)]
        exact (hkeep₁ _ (by omega)).trans (hwritten j (by omega))
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      exact (hkeep₁ _ (by omega)).trans (hkept j hj)
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨pval,ν,rfl,hwritten,hkept⟩
    simp
  · rintro σ ⟨pval,ν,rfl,hwritten,hkept⟩
    have hfinal := hqWord levels le_rfl
    light_set (qs levels) using ct
    exact ⟨by simp [qs,A,B,C],hwritten,hkept⟩

def program : Program :=
  [body 1, LightPrimeMinimum.body 2, LightWeightedScore.body 4 3,
    LightWeightedScore.jointBody 8, LightModuloCounts.body 5 6 10 7 15,
    LightCapacity.body, LightResidueHistogram.body 7 9, LightResidues.residuesBody 8,
    emodBody, LightHistogram.histogramBody 14, LightCyclic.body 11 13,
    LightKaratsuba.body 11 12 13 14, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]

def program_count_procs : LightModuloCounts.Procs program 4 where
  pCapacity := 5
  pHist := 6
  pCyclic := 10
  pResidues := 7
  pEmod := 8
  pHistogram := 9
  pMultiply := 11
  pHalf := 12
  pLinear := 13
  pFill := 14
  pLookup := 15
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl,rfl,rfl,rfl⟩
  lookup := rfl

def program_score_procs : LightWeightedScore.Procs program 2 where
  pCount := 4
  pJoint := 3
  count := program_count_procs
  main := rfl
  joint := rfl

def program_minimum_procs : LightPrimeMinimum.Procs program 1 where
  pScore := 2
  score := program_score_procs
  main := rfl

def program_procs : Procs program 0 where
  pMinimum := 1
  minimum := program_minimum_procs
  main := rfl

theorem program_meets
    {μ : ℕ → ℤ} {a b c nA nB nC N aux s levels free maxMod U Y : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : space free maxMod N U levels ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+6 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y^(levels+1) ≤ maxMod) :
    Meets lim program 0 d [a,b,c,nA,nB,nC,N,aux,s,levels,free] μ
      (time maxMod nA nB nC s U levels)
      (fun r μ' =>
        r = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) levels : ℤ) ∧
        (∀ i ≤ levels, μ' (free+i) = (modulus primes s nA nB nC
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) i : ℤ)) ∧
        Kept μ μ' free) :=
  program_procs.meets primes hw hs ha hb hc haux hnA hnB hnC hspace hword hd
    hA hB hC hread hprime hinj hhi hmax

end ThreeSum.LightPrimeChain
