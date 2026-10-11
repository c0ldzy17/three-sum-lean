import Submission.ThreeSum.LightBandWeightedScore
import Submission.ThreeSum.BandPrimeChoice

/-!
# Execute common-prime minimization over all owner candidates

Every candidate prime is scored by the actual aggregate band loop. The
first minimum is returned, with no supplied score array or counting oracle.
-/

namespace ThreeSum.LightBandPrimeMinimum

open Light BandCandidateRows BandWeightedScore BandPrimeChoice

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def body (pScore : ℕ) : Stmt :=
  .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9 *' M (v 10),v 10,v 11,v 12] 13 ;;
  .set 14 (k 0) ;;
  .for 15 (v 11) (
    .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,
      v 9 *' M (v 10 +' v 15),v 10,v 11,v 12] 16 ;;
    .ite (v 16 <' v 13) (.set 13 (v 16) ;; .set 14 (v 15)) .skip) ;;
  .set 0 (M (v 10 +' v 14))

def program : Program := LightBandWeightedScore.program ++ [body 16]

theorem program_length : program.length=18 := rfl

def time (maxMod g R s U : ℕ) : ℕ :=
  LightBandWeightedScore.time maxMod g R s U+
    s*(LightBandWeightedScore.time maxMod g R s U+140)+140

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (a b c nA nB nC g recs R q aux s free i : ℕ) (σ : State) : Prop :=
  ∃ (value : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,q,aux,s,free,
      f (LightMinimum.least f i),LightMinimum.least f i,i,value],ν⟩ ∧ Kept μ ν free

theorem maxMod_le_word (maxMod nA nB nC g R s U : ℕ) :
    maxMod ≤ LightBandWeightedScore.word maxMod nA nB nC g R s U := by
  unfold LightBandWeightedScore.word LightBandWeightedScoreCell.word LightWeightedScore.word
  omega

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}

theorem program_meets (primes : ℕ → ℕ) (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+7 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hs : 0 < s)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free) (haux : aux+s ≤ free)
    (hspace : LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
    (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, ∀ j < s, q*primes i*primes j ≤ maxMod) :
    Meets lim program 17 d [a,b,c,nA,nB,nC,g,recs,rs.length,q,aux,s,free] μ
      (time maxMod g rs.length s U)
      (fun result ν => result=(chosenPrime primes s q nA nB nC g
        (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs : ℤ) ∧ Kept μ ν free) := by
  let A := fun i => μ (a+i)
  let B := fun i => μ (b+i)
  let C := fun i => μ (c+i)
  let f := candidateScore primes s q nA nB nC g A B C rs
  let ct := LightBandWeightedScore.time maxMod g rs.length s U
  have htotal : rs.length*(s*g^3) ≤ LightBandWeightedScore.word maxMod nA nB nC g rs.length s U := by
    unfold LightBandWeightedScore.word
    omega
  have htotalWord : ((rs.length*(s*g^3) : ℕ) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr htotal).trans hword
  have hf (i : ℕ) : 0 ≤ f i ∧ f i ≤ lim.word := by
    constructor
    · exact Int.natCast_nonneg _
    · exact (Int.ofNat_le.mpr (score_bound primes s (q*primes i) nA nB nC g A B C rs hprime hinj)).trans htotalWord
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (maxMod_le_word maxMod nA nB nC g rs.length s U)).trans hword
  have hqiMax (i : ℕ) (hi : i < s) : q*primes i ≤ maxMod :=
    (Nat.le_mul_of_pos_right _ (hprime 0 hs).pos).trans (hproduct i hi 0 hs)
  have hpiWord (i : ℕ) (hi : i < s) : (primes i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((Nat.le_mul_of_pos_left (primes i) hq).trans (hqiMax i hi))).trans hmaxWord
  have hqiWord (i : ℕ) (hi : i < s) : (q : ℤ)*(primes i : ℤ) ≤ lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr (hqiMax i hi)).trans hmaxWord
  have hfree : free ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hcall (ν : ℕ → ℤ) (i : ℕ) (hi : i < s) (hkeep : Kept μ ν free) :
      Meets lim program 16 (d+1) [a,b,c,nA,nB,nC,g,recs,rs.length,q*primes i,aux,s,free] ν ct
        (fun value ξ => value=f i ∧ Kept ν ξ free) := by
    have hrecordsν : Seg ν recs (cells rs) := by
      apply hrecords.congr
      intro j hj
      rw [cells_length] at hj
      exact hkeep _ (by omega)
    have hAν : ∀ j < nA, |ν (a+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hA j hj
    have hBν : ∀ j < nB, |ν (b+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hB j hj
    have hCν : ∀ j < nC, |ν (c+j)| ≤ (U : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hC j hj
    have hreadν : ∀ j < s, ν (aux+j)=(primes j : ℤ) := by
      intro j hj; rw [hkeep _ (by omega)]; exact hread j hj
    refine ((LightBandWeightedScore.program_meets (d := d+1) (μ := ν) primes rs hw (by omega)
      hg (Nat.mul_pos hq (hprime i hi).pos) (hqiMax i hi) ha hb hc hrecs haux hspace hword
      hrecordsν hflag hvalid hAν hBν hCν hreadν hprime hinj (hproduct i hi)).append [body 16]).mono le_rfl ?_
    rintro value ξ ⟨hvalue,hkeep'⟩
    refine ⟨hvalue.trans ?_,hkeep'⟩
    unfold f candidateScore
    congr 1
    exact score_congr rs (fun j hj => hkeep _ (by omega))
      (fun j hj => hkeep _ (by omega)) (fun j hj => hkeep _ (by omega))
  have hp0 := hpiWord 0 hs
  have hq0 := hqiWord 0 hs
  have hq0Nonneg : (0 : ℤ) ≤ (q : ℤ)*(primes 0 : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
  have hread0 : μ aux=(primes 0 : ℤ) := by simpa only [Nat.add_zero] using hread 0 hs
  apply Meets.of_body (p := 17) (by rfl : program[17]?=some (body 16))
  unfold body time
  light_call (hcall μ 0 hs (fun _ _ => rfl)) using hread0,ct with value μ₁ ⟨hvalue,hkeep₁⟩
  subst value
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for (T := s*(ct+140)+30)
    (Q := Inv μ f a b c nA nB nC g recs rs.length q aux s free s)
    (Inv μ f a b c nA nB nC g recs rs.length q aux s free) s (ct+110)
    ?start ?round ?done ?bound (hT := by light_time [ct])) ?finish (hT := by light_time [ct])
  case start =>
    refine ⟨0,μ₁,?_,hkeep₁⟩
    simp only [LightMinimum.least,update_frame_setLocal]
    exact congrArg (fun loc => (⟨loc,μ₁⟩ : State)) (frame_append_zeros _ 1).symm
  case round =>
    rintro i _ hi _ ⟨old,ν,rfl,hkeep⟩
    have hbest : LightMinimum.least f i < s := LightMinimum.least_lt_of_le f hs (by omega)
    have hpi := hpiWord i hi
    have hqi := hqiWord i hi
    have hqiNonneg : (0 : ℤ) ≤ (q : ℤ)*(primes i : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hreadν : ν (aux+i)=(primes i : ℤ) := (hkeep _ (by omega)).trans (hread i hi)
    have hfi := hf i
    have hfb := hf (LightMinimum.least f i)
    light_call (hcall ν i hi hkeep) using hreadν,ct with value ξ ⟨hvalue,hkeep'⟩
    subst value
    have hkept : Kept μ ξ free := fun j hj => (hkeep' j hj).trans (hkeep j hj)
    refine Ends.iteLast (fun hcmp => ?_) (fun hcmp => ?_) (by light_side)
    · have hcmp' : f i < f (LightMinimum.least f i) := by simpa using hcmp
      light_set (f i)
      light_set (i : ℕ)
      refine ⟨by simp,f i,ξ,?_,hkept⟩
      simp [LightMinimum.least,hcmp',update_frame_setLocal]
    · have hcmp' : ¬ f i < f (LightMinimum.least f i) := by simpa using hcmp
      apply Ends.skip
      refine ⟨by simp,f i,ξ,?_,hkept⟩
      simp [LightMinimum.least,hcmp',update_frame_setLocal]
  case done =>
    intro σ _ H
    exact H
  case bound =>
    rintro i _ hi _ ⟨old,ν,rfl,hkeep⟩
    simp
  case finish =>
    rintro _ ⟨old,ν,rfl,hkeep⟩
    have hbest : LightMinimum.least f s < s := LightMinimum.least_lt f hs
    have hbestWord := hpiWord (LightMinimum.least f s) hbest
    have hreadBest : ν (aux+LightMinimum.least f s)=(primes (LightMinimum.least f s) : ℤ) :=
      (hkeep _ (by omega)).trans (hread _ hbest)
    light_set (primes (LightMinimum.least f s) : ℕ) using hreadBest,ct
    exact ⟨by simp [chosenPrime,chosenIndex,f,A,B,C],hkeep⟩

end ThreeSum.LightBandPrimeMinimum
