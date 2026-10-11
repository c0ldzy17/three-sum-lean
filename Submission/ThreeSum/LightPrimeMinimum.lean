import Submission.ThreeSum.LightWeightedScore
import Submission.ThreeSum.LightMinimum

/-!
# Executing deterministic prime-score minimization

The same finite prime array supplies the candidate multipliers and the
auxiliary tests. The program streams exact scores at `q * primes i`, retaining
the first minimum. All weighted-score calls reuse one scratch region.
-/

namespace ThreeSum.LightPrimeMinimum

open Light WeightedScore

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

def candidateScore (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) (i : ℕ) : ℤ :=
  (score primes s (q*primes i) nA nB nC A B C : ℤ)

def chosenIndex (primes : ℕ → ℕ) (s q nA nB nC : ℕ) (A B C : ℕ → ℤ) : ℕ :=
  LightMinimum.least (candidateScore primes s q nA nB nC A B C) s

def chosenPrime (primes : ℕ → ℕ) (s q nA nB nC : ℕ) (A B C : ℕ → ℤ) : ℕ :=
  primes (chosenIndex primes s q nA nB nC A B C)

theorem chosenIndex_lt (primes : ℕ → ℕ) {s q nA nB nC : ℕ}
    (A B C : ℕ → ℤ) (hs : 0 < s) :
    chosenIndex primes s q nA nB nC A B C < s :=
  LightMinimum.least_lt _ hs

theorem chosenPrime_min (primes : ℕ → ℕ) (s q nA nB nC : ℕ)
    (A B C : ℕ → ℤ) {i : ℕ} (hi : i < s) :
    score primes s (q*chosenPrime primes s q nA nB nC A B C) nA nB nC A B C ≤
      score primes s (q*primes i) nA nB nC A B C := by
  have h := LightMinimum.least_value_le
    (candidateScore primes s q nA nB nC A B C) s i hi
  dsimp only [candidateScore] at h
  exact_mod_cast h

theorem score_congr {primes : ℕ → ℕ} {s q nA nB nC : ℕ} {A A' B B' C C' : ℕ → ℤ}
    (ha : ∀ i < nA, A i = A' i) (hb : ∀ i < nB, B i = B' i)
    (hc : ∀ i < nC, C i = C' i) :
    score primes s q nA nB nC A B C = score primes s q nA nB nC A' B' C' := by
  unfold score Arithmetic.weightedFalseCount
  apply Finset.sum_congr rfl
  intro t ht
  simp only [ModuloCounts.triples, Finset.mem_product, Finset.mem_range] at ht
  simp only [ModuloCounts.difference, ha _ ht.1, hb _ ht.2.1, hc _ ht.2.2]
  rfl

theorem chosenPrime_congr {primes : ℕ → ℕ} {s q nA nB nC : ℕ}
    {A A' B B' C C' : ℕ → ℤ}
    (ha : ∀ i < nA, A i = A' i) (hb : ∀ i < nB, B i = B' i)
    (hc : ∀ i < nC, C i = C' i) :
    chosenPrime primes s q nA nB nC A B C = chosenPrime primes s q nA nB nC A' B' C' := by
  have hf : candidateScore primes s q nA nB nC A B C =
      candidateScore primes s q nA nB nC A' B' C' := by
    funext i
    unfold candidateScore
    rw [score_congr ha hb hc]
  simp only [chosenPrime,chosenIndex,hf]

/-- Arguments match the weighted-score procedure. Local 11 holds the best
score, 12 its index, 13 the scan counter, and 14 the newly computed score. -/
def body (pScore : ℕ) : Stmt :=
  .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6 *' M (v 8),v 7,v 8,v 9,v 10] 11 ;;
  .set 12 (k 0) ;;
  .for 13 (v 9) (
    .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6 *' M (v 8 +' v 13),v 7,v 8,v 9,v 10] 14 ;;
    .ite (v 14 <' v 11) (.set 11 (v 14) ;; .set 12 (v 13)) .skip) ;;
  .set 0 (M (v 8 +' v 12))

def time (maxMod nA nB nC s U : ℕ) : ℕ :=
  LightWeightedScore.runtimeTime maxMod nA nB nC s U +
    s*(LightWeightedScore.runtimeTime maxMod nA nB nC s U+100)+100

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (a b c nA nB nC q N aux s free : ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (rval : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [(a : ℤ),b,c,nA,nB,nC,q,N,aux,s,free,
      f (LightMinimum.least f i), LightMinimum.least f i,i,rval],ν⟩ ∧ Kept μ ν free

structure Procs (P : Program) (pMain : ℕ) where
  pScore : ℕ
  score : LightWeightedScore.Procs P pScore
  main : P[pMain]? = some (body pScore)

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The selected prime is computed from exact scores on the original input.
All semantic helper contracts follow from the concrete syntax in `S.score`. -/
theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hq : 0 < q) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : LightWeightedScore.space free maxMod N U ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+5 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, ∀ j < s, q*primes i*primes j ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (time maxMod nA nB nC s U)
      (fun r μ' => r = (chosenPrime primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) := by
  let A := fun j => μ (a+j)
  let B := fun j => μ (b+j)
  let C := fun j => μ (c+j)
  let f := candidateScore primes s q nA nB nC A B C
  let ct := LightWeightedScore.runtimeTime maxMod nA nB nC s U
  have hfree : free ≤ lim.space := by
    have hh := (Nat.le_max_right _ _).trans hspace
    change free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hprodN : nA*nB*nC ≤ N^3 := by
    calc
      _ ≤ N*N*N := Nat.mul_le_mul (Nat.mul_le_mul hnA hnB) hnC
      _ = _ := by ring
  have hscoreWord : ((s*N^3 : ℕ) : ℤ) ≤ lim.word := by
    have hm : s*N^3 ≤ (s+1)*N^3 := Nat.mul_le_mul_right _ (by omega)
    have hh : s*N^3 ≤ LightWeightedScore.word maxMod N s U := by
      unfold LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hf (i : ℕ) : 0 ≤ f i ∧ f i ≤ lim.word := by
    unfold f candidateScore
    constructor
    · positivity
    · rw [score_eq_remaining primes s (q*primes i) nA nB nC A B C hprime hinj]
      exact (Int.ofNat_le.mpr ((remaining_le primes s (q*primes i) nA nB nC A B C s).trans
        (Nat.mul_le_mul_left s hprodN))).trans hscoreWord
  have hmaxWord : (maxMod : ℤ) ≤ lim.word := by
    have hh : maxMod ≤ LightWeightedScore.word maxMod N s U := by
      unfold LightWeightedScore.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hqimax (i : ℕ) (hi : i < s) : q*primes i ≤ maxMod :=
    (Nat.le_mul_of_pos_right _ (hprime 0 hs).pos).trans (hproduct i hi 0 hs)
  have hpiWord (i : ℕ) (hi : i < s) : (primes i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((Nat.le_mul_of_pos_left (primes i) hq).trans (hqimax i hi))).trans
      hmaxWord
  have hqiWord (i : ℕ) (hi : i < s) : (q : ℤ)*(primes i : ℤ) ≤ lim.word := by
    have hh := (Int.ofNat_le.mpr (hqimax i hi)).trans hmaxWord
    exact_mod_cast hh
  have hcall (ν : ℕ → ℤ) (i : ℕ) (hi : i < s) (hkept : Kept μ ν free) :
      Meets lim P S.pScore (d+1)
        [a,b,c,nA,nB,nC,q*primes i,N,aux,s,free] ν ct
        (fun r ν' => r = f i ∧ Kept ν ν' free) := by
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
    apply (S.score.meets (d := d+1) primes hw (Nat.mul_pos hq (hprime i hi).pos)
      (hqimax i hi) ha hb hc haux hnA hnB hnC hspace hword (by omega)
      hAν hBν hCν hreadν hprime hinj (hproduct i hi)).mono le_rfl
    intro r ν' ⟨hr,hkeep⟩
    refine ⟨hr.trans ?_,hkeep⟩
    unfold f candidateScore
    congr 1
    exact score_congr (fun j hj => hkept _ (by omega))
      (fun j hj => hkept _ (by omega)) (fun j hj => hkept _ (by omega))
  have hp0 := hpiWord 0 hs
  have hq0 := hqiWord 0 hs
  have hq0nonneg : (0 : ℤ) ≤ (q : ℤ)*(primes 0 : ℤ) := by positivity
  have hread0 : μ aux = (primes 0 : ℤ) := by simpa using hread 0 hs
  apply Meets.of_body S.main
  unfold body time
  light_call (hcall μ 0 hs (fun _ _ => rfl)) using hread0,ct
    with result μ₀ ⟨hresult,hkept₀⟩
  subst result
  light_set 0
  refine Ends.pieceThen (Ends.for (T := s*(ct+100)+20)
    (Q := Inv μ f a b c nA nB nC q N aux s free s)
    (Inv μ f a b c nA nB nC q N aux s free) s (ct+80)
    ?_ ?_ ?_ ?_ (hT := by light_time [ct])) ?_ (hT := by light_time [ct])
  · refine ⟨0,μ₀,?_,hkept₀⟩
    simp only [LightMinimum.least,update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc,μ₀⟩ : State)) (frame_append_zeros _ 1).symm
  · rintro i _ hi _ ⟨rval,ν,rfl,hkept⟩
    have hbest : LightMinimum.least f i < s := LightMinimum.least_lt_of_le f hs (by omega)
    have hpi := hpiWord i hi
    have hqi := hqiWord i hi
    have hqinonneg : (0 : ℤ) ≤ (q : ℤ)*(primes i : ℤ) := by positivity
    have hreadν : ν (aux+i) = (primes i : ℤ) := (hkept _ (by omega)).trans (hread i hi)
    have hfi := hf i
    have hfb := hf (LightMinimum.least f i)
    light_call (hcall ν i hi hkept) using hreadν,ct with result ν₁ ⟨hresult,hkeep₁⟩
    subst result
    have hkept₁ : Kept μ ν₁ free := fun j hj => (hkeep₁ j hj).trans (hkept j hj)
    refine Ends.iteLast (fun hcmp => ?_) (fun hcmp => ?_) (by light_side)
    · have hcmp' : f i < f (LightMinimum.least f i) := by simpa using hcmp
      light_set (f i)
      light_set i
      refine ⟨by simp,f i,ν₁,?_,hkept₁⟩
      simp [LightMinimum.least,hcmp',update_frame_setLocal]
    · have hcmp' : ¬ f i < f (LightMinimum.least f i) := by simpa using hcmp
      apply Ends.skip
      refine ⟨by simp,f i,ν₁,?_,hkept₁⟩
      simp [LightMinimum.least,hcmp',update_frame_setLocal]
  · intro σ _ hI
    exact hI
  · rintro i _ hi _ ⟨rval,ν,rfl,hkept⟩
    simp
  · rintro σ ⟨rval,ν,rfl,hkept⟩
    have hbest : LightMinimum.least f s < s := LightMinimum.least_lt f hs
    have hbestWord := hpiWord (LightMinimum.least f s) hbest
    have hreadBest : ν (aux+LightMinimum.least f s) =
        (primes (LightMinimum.least f s) : ℤ) :=
      (hkept _ (by omega)).trans (hread _ hbest)
    light_set (primes (LightMinimum.least f s)) using hreadBest,ct
    exact ⟨by simp [chosenPrime,chosenIndex,f,A,B,C],hkept⟩

def program : Program :=
  [body 1, LightWeightedScore.body 3 2, LightWeightedScore.jointBody 7,
    LightModuloCounts.body 4 5 9 6 14, LightCapacity.body,
    LightResidueHistogram.body 6 8, LightResidues.residuesBody 7, emodBody,
    LightHistogram.histogramBody 13, LightCyclic.body 10 12,
    LightKaratsuba.body 10 11 12 13, halfBody, LightArray.linearBody, fillBody,
    LightLookupSum.body]

def program_count_procs : LightModuloCounts.Procs program 3 where
  pCapacity := 4
  pHist := 5
  pCyclic := 9
  pResidues := 6
  pEmod := 7
  pHistogram := 8
  pMultiply := 10
  pHalf := 11
  pLinear := 12
  pFill := 13
  pLookup := 14
  main := rfl
  capacity := rfl
  hist := rfl
  residues := rfl
  emod := rfl
  histogram := rfl
  cyclic := rfl
  multiply := ⟨rfl,rfl,rfl,rfl⟩
  lookup := rfl

def program_score_procs : LightWeightedScore.Procs program 1 where
  pCount := 3
  pJoint := 2
  count := program_count_procs
  main := rfl
  joint := rfl

def program_procs : Procs program 0 where
  pScore := 1
  score := program_score_procs
  main := rfl

theorem program_meets
    {μ : ℕ → ℤ} {a b c nA nB nC q N aux s free maxMod U : ℕ}
    (primes : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hq : 0 < q) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (haux : aux+s ≤ free)
    (hnA : nA ≤ N) (hnB : nB ≤ N) (hnC : nC ≤ N)
    (hspace : LightWeightedScore.space free maxMod N U ≤ lim.space)
    (hword : (LightWeightedScore.word maxMod N s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+5 ≤ lim.depth)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i) = (primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i = primes j → i = j)
    (hproduct : ∀ i < s, ∀ j < s, q*primes i*primes j ≤ maxMod) :
    Meets lim program 0 d [a,b,c,nA,nB,nC,q,N,aux,s,free] μ
      (time maxMod nA nB nC s U)
      (fun r μ' => r = (chosenPrime primes s q nA nB nC
        (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) : ℤ) ∧
          Kept μ μ' free) :=
  program_procs.meets primes hw hq hs ha hb hc haux hnA hnB hnC hspace hword hd
    hA hB hC hread hprime hinj hproduct

end ThreeSum.LightPrimeMinimum
