import Submission.ThreeSum.LightBandPrimeMinimum

/-!
# Execute one common modulus chain for all candidate owners

The loop calls the verified aggregate minimum at every level. Its output is
the same common modulus whose contraction is proved in `BandPrimeChoice`.
All prefix moduli are retained; every score computation reuses the region
beyond the prefix array.
-/

namespace ThreeSum.LightBandPrimeChain

open Light BandCandidateRows BandPrimeChoice

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

/-- Arguments: the three original sorted arrays and lengths, band size,
candidate records and count, prime array and count, levels, free address. -/
def body (pMinimum : ℕ) : Stmt :=
  .set 13 (k 1) ;;
  .set 16 (v 12 +' v 11 +' k 1) ;;
  .store (v 12) (v 13) ;;
  .for 14 (v 11) (
    .call pMinimum [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 13,v 9,v 10,v 16] 15 ;;
    .set 13 (v 13 *' v 15) ;;
    .store (v 12 +' v 14 +' k 1) (v 13)) ;;
  .set 0 (v 13)

def program : Program := LightBandPrimeMinimum.program ++ [body 17]

theorem program_length : program.length=19 := rfl

def time (maxMod g R s U levels : ℕ) : ℕ :=
  levels*(LightBandPrimeMinimum.time maxMod g R s U+140)+140

def space (free maxMod g U levels : ℕ) : ℕ :=
  LightWeightedScore.space (free+levels+1) maxMod g U

def Inv (μ : ℕ → ℤ) (qs : ℕ → ℕ)
    (a b c nA nB nC g recs R aux s levels free i : ℕ) (σ : State) : Prop :=
  ∃ (pval : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,aux,s,levels,free,
      qs i,i,pval,free+levels+1],ν⟩ ∧
    (∀ j ≤ i, ν (free+j)=(qs j : ℤ)) ∧ Kept μ ν free

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs aux s levels free maxMod U Y : ℕ}

/-- A closed, literal program executes the common contracting prime choices.
No list of choices, precomputed scores, or semantic subroutine is supplied. -/
theorem program_meets (primes : ℕ → ℕ) (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hs : 0 < s) (hg : 0 < g)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free) (haux : aux+s ≤ free)
    (hspace : space free maxMod g U levels ≤ lim.space)
    (hword : (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+8 ≤ lim.depth)
    (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hhi : ∀ i < s, primes i ≤ Y)
    (hmax : Y^(levels+1) ≤ maxMod) :
    Meets lim program 18 d [a,b,c,nA,nB,nC,g,recs,rs.length,aux,s,levels,free] μ
      (time maxMod g rs.length s U levels)
      (fun result ν =>
        result=(modulus primes s nA nB nC g
          (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs levels : ℤ) ∧
        (∀ i ≤ levels, ν (free+i)=(modulus primes s nA nB nC g
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs i : ℤ)) ∧
        Kept μ ν free) := by
  let A := fun i => μ (a+i)
  let B := fun i => μ (b+i)
  let C := fun i => μ (c+i)
  let qs := modulus primes s nA nB nC g A B C rs
  let ct := LightBandPrimeMinimum.time maxMod g rs.length s U
  have hwork : free+levels+1 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+levels+1+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hY : 1 ≤ Y := (hprime 0 hs).one_lt.le.trans (hhi 0 hs)
  have hqpos (i : ℕ) : 0 < qs i := modulus_pos primes A B C rs hs hprime i
  have hqhi (i : ℕ) : qs i ≤ Y^i :=
    (modulus_bounds primes A B C rs hs 0 Y i (fun _ _ => Nat.zero_le _) hhi).2
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (LightBandPrimeMinimum.maxMod_le_word maxMod nA nB nC g rs.length s U)).trans hword
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
  apply Meets.of_body (p := 18) (by rfl : program[18]?=some (body 17))
  unfold body time
  light_set 1
  light_set (free+levels+1)
  light_store free (1 : ℕ)
  refine Ends.pieceThen (Ends.for (T := levels*(ct+140)+20)
    (Q := Inv μ qs a b c nA nB nC g recs rs.length aux s levels free levels)
    (Inv μ qs a b c nA nB nC g recs rs.length aux s levels free) levels (ct+110)
    ?start ?round ?done ?bound (hT := by light_time [ct])) ?finish (hT := by light_time [ct])
  case start =>
    refine ⟨0,Function.update μ free (1 : ℤ),?_,?_,?_⟩
    · simp [qs,modulus,update_frame_setLocal]
    · intro j hj
      have hj0 : j=0 := by omega
      simp [hj0,qs,modulus]
    · intro j hj
      exact Function.update_of_ne (by omega) _ _
  case round =>
    rintro i _ hi _ ⟨pval,ν,rfl,hwritten,hkept⟩
    have hrecordsν : Seg ν recs (cells rs) := by
      apply hrecords.congr
      intro j hj
      rw [cells_length] at hj
      exact hkept _ (by omega)
    have hAν : ∀ j < nA, |ν (a+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkept _ (by omega)]; exact hA j hj
    have hBν : ∀ j < nB, |ν (b+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkept _ (by omega)]; exact hB j hj
    have hCν : ∀ j < nC, |ν (c+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkept _ (by omega)]; exact hC j hj
    have hreadν : ∀ j < s, ν (aux+j)=(primes j : ℤ) := by
      intro j hj; exact (hkept _ (by omega)).trans (hread j hj)
    light_call ((LightBandPrimeMinimum.program_meets (d := d+1) (q := qs i)
      (free := free+levels+1) primes rs hw (by omega) hg (hqpos i) hs
      (by omega) (by omega) (by omega) (by omega) (by omega) hspace hword
      hrecordsν hflag hvalid hAν hBν hCν hreadν hprime hinj (hproducts i hi)).append [body 17])
      using ct with result ν₁ ⟨hresult,hkeep₁⟩
    have hchosen : chosenPrime primes s (qs i) nA nB nC g
        (fun j => ν (a+j)) (fun j => ν (b+j)) (fun j => ν (c+j)) rs=
        chosenPrime primes s (qs i) nA nB nC g A B C rs :=
      chosenPrime_congr rs (fun j hj => hkept _ (by omega))
        (fun j hj => hkept _ (by omega)) (fun j hj => hkept _ (by omega))
    rw [hchosen] at hresult
    subst result
    have hnext := hqWord (i+1) (by omega)
    have hprodWord : (qs i : ℤ)*(chosenPrime primes s (qs i) nA nB nC g A B C rs : ℤ) ≤
        lim.word := by simpa only [qs,modulus,Nat.cast_mul] using hnext
    have hprodNonneg : (0 : ℤ) ≤
        (qs i : ℤ)*(chosenPrime primes s (qs i) nA nB nC g A B C rs : ℤ) := by positivity
    dsimp only [qs] at hprodWord hprodNonneg
    light_set (qs (i+1)) using qs,modulus,ct
    light_store (free+i+1) (qs (i+1)) using ct
    refine ⟨by simp,chosenPrime primes s (qs i) nA nB nC g A B C rs,
      Function.update ν₁ (free+i+1) (qs (i+1) : ℤ),?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro j hj
      by_cases heq : j=i+1
      · simp [heq,Nat.add_assoc]
      · rw [Function.update_of_ne (by omega)]
        exact (hkeep₁ _ (by omega)).trans (hwritten j (by omega))
    · intro j hj
      rw [Function.update_of_ne (by omega)]
      exact (hkeep₁ _ (by omega)).trans (hkept j hj)
  case done =>
    intro σ _ H
    exact H
  case bound =>
    rintro i _ hi _ ⟨pval,ν,rfl,hwritten,hkept⟩
    simp
  case finish =>
    rintro _ ⟨pval,ν,rfl,hwritten,hkept⟩
    have hfinal := hqWord levels le_rfl
    light_set (qs levels) using ct
    exact ⟨by simp [qs,A,B,C],hwritten,hkept⟩

end ThreeSum.LightBandPrimeChain
