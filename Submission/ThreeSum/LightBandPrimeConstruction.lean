import Submission.ThreeSum.LightBandPrimeChain
import Submission.ThreeSum.LightPrimePool
import Submission.ThreeSum.ReportingHostRelocation

/-!
# Construct the prime pool and common contracting modulus from band records

The fixed host constructs the candidate prime array, then executes the
aggregate modulus chain on every owner record. The physical prime array and
every prefix modulus remain available to the encoder and reporting stages.
-/

namespace ThreeSum.LightBandPrimeConstruction

open Light BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def modulus (y nA nB nC g : ℕ) (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) : ℕ :=
  BandPrimeChoice.modulus (LightPrimePool.prime y) (LightPrimePool.size y)
    nA nB nC g A B C rs levels

theorem modulus_bounds {y nA nB nC g : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 0 < y) :
    y^levels ≤ modulus y nA nB nC g A B C rs levels ∧
      modulus y nA nB nC g A B C rs levels ≤ (4*y)^levels :=
  BandPrimeChoice.modulus_bounds (LightPrimePool.prime y) A B C rs
    (LightPrimePool.size_pos hy) y (4*y) levels
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le)
    (fun i hi => (LightPrimePool.prime_spec hi).2.2)

theorem modulus_score_bound {y nA nB nC g U : ℕ}
    (A B C : ℕ → ℤ) (rs : List Record) (levels : ℕ) (hy : 1 < y)
    (hA : ∀ i < nA, |A i| ≤ (U : ℤ))
    (hB : ∀ i < nB, |B i| ≤ (U : ℤ))
    (hC : ∀ i < nC, |C i| ≤ (U : ℤ)) :
    (LightPrimePool.size y)^levels * BandWeightedScore.score
      (LightPrimePool.prime y) (LightPrimePool.size y)
      (modulus y nA nB nC g A B C rs levels) nA nB nC g A B C rs ≤
      (Nat.log y (3*U))^levels * BandWeightedScore.score
        (LightPrimePool.prime y) (LightPrimePool.size y) 1 nA nB nC g A B C rs :=
  BandPrimeChoice.modulus_score_bound (LightPrimePool.prime y) (LightPrimePool.size y)
    nA nB nC g y U levels A B C rs hy (fun i hi => (LightPrimePool.prime_spec hi).1)
    (fun i hi j hj heq => LightPrimePool.prime_injective hi hj heq)
    (fun i hi => (LightPrimePool.prime_spec hi).2.1.le) hA hB hC

/-- Arrays and lengths, band size, records and length, window, levels, free. -/
def body (pPool pChain : ℕ) : Stmt :=
  .call pPool [v 9,v 11] 12 ;;
  .set 13 (v 11 +' k 3 *' v 9) ;;
  .call pChain [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 11,v 12,v 10,v 13] 0

def program : Program := ReportingHostRelocation.program
  LightPrimePool.program LightBandPrimeChain.program ++ [body 0 21]

theorem program_length : program.length=23 := rfl

def time (maxMod g R y U levels : ℕ) : ℕ :=
  LightPrimePool.time y+
    LightBandPrimeChain.time maxMod g R (LightPrimePool.size y) U levels+140

def space (free maxMod g y U levels : ℕ) : ℕ :=
  max (LightPrimePool.space free y)
    (LightBandPrimeChain.space (free+3*y) maxMod g U levels)

def word (maxMod nA nB nC g R y U : ℕ) : ℕ :=
  max (LightPrimePool.word y)
    (LightBandWeightedScore.word maxMod nA nB nC g R (LightPrimePool.size y) U)

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs y levels free maxMod U : ℕ}

theorem program_meets (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free)
    (hspace : space free maxMod g y U levels ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+9 ≤ lim.depth)
    (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hmax : (4*y)^(levels+1) ≤ maxMod) :
    Meets lim program 22 d [a,b,c,nA,nB,nC,g,recs,rs.length,y,levels,free] μ
      (time maxMod g rs.length y U levels)
      (fun result ν =>
        result=(modulus y nA nB nC g
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs levels : ℤ) ∧
        SegN ν free (LightPrimePool.values y) ∧
        (∀ i ≤ levels, ν (free+3*y+i)=(modulus y nA nB nC g
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs i : ℤ)) ∧
        Kept μ ν free) := by
  have hpoolSpace : LightPrimePool.space free y ≤ lim.space := (le_max_left _ _).trans hspace
  have hchainSpace : LightBandPrimeChain.space (free+3*y) maxMod g U levels ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hpoolWord : (LightPrimePool.word y : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hchainWord : (LightBandWeightedScore.word maxMod nA nB nC g rs.length (LightPrimePool.size y) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  have hpoolEnd : free+3*y ≤ lim.space := by unfold LightPrimePool.space at hpoolSpace; omega
  have hsize := LightPrimePool.size_le y
  apply Meets.of_body (p := 22) (by rfl : program[22]?=some (body 0 21))
  unfold body time
  have hp := ((LightPrimePool.program_meets (d := d+1) (μ := μ) (y := y) (free := free)
    hw (by omega) hy hpoolSpace hpoolWord).append
      (LightBandPrimeChain.program.map (ReportingHostRelocation.relocate 3))).append [body 0 21]
  light_call hp with count μ₁ ⟨hcount,hpool,hkeep₁⟩
  subst count
  light_set (free+3*y)
  have hrecords₁ : Seg μ₁ recs (cells rs) := by
    apply hrecords.congr
    intro j hj
    rw [cells_length] at hj
    exact hkeep₁ _ (by omega)
  have hA₁ : ∀ i < nA, |μ₁ (a+i)| ≤ (U : ℤ) := by
    intro i hi; rw [hkeep₁ _ (by omega)]; exact hA i hi
  have hB₁ : ∀ i < nB, |μ₁ (b+i)| ≤ (U : ℤ) := by
    intro i hi; rw [hkeep₁ _ (by omega)]; exact hB i hi
  have hC₁ : ∀ i < nC, |μ₁ (c+i)| ≤ (U : ℤ) := by
    intro i hi; rw [hkeep₁ _ (by omega)]; exact hC i hi
  have hread : ∀ i < LightPrimePool.size y, μ₁ (free+i)=(LightPrimePool.prime y i : ℤ) :=
    fun i hi => hpool.read hi
  have hc := (ReportingHostRelocation.meets
    (LightBandPrimeChain.program_meets (d := d+1) (μ := μ₁) (aux := free) (free := free+3*y)
      (Y := 4*y) (LightPrimePool.prime y) rs hw (LightPrimePool.size_pos hy) hg
      (by omega) (by omega) (by omega) (by omega) (by omega) hchainSpace hchainWord (by omega)
      hrecords₁ hflag hvalid hA₁ hB₁ hC₁ hread
      (fun i hi => (LightPrimePool.prime_spec hi).1)
      (fun i hi j hj heq => LightPrimePool.prime_injective hi hj heq)
      (fun i hi => (LightPrimePool.prime_spec hi).2.2) hmax) LightPrimePool.program).append [body 0 21]
  light_call hc with result ν ⟨hresult,hprefix,hkeep₂⟩
  have hmod (i : ℕ) :
      BandPrimeChoice.modulus (LightPrimePool.prime y) (LightPrimePool.size y) nA nB nC g
        (fun j => μ₁ (a+j)) (fun j => μ₁ (b+j)) (fun j => μ₁ (c+j)) rs i=
      modulus y nA nB nC g (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs i :=
    BandPrimeChoice.modulus_congr rs (fun j hj => hkeep₁ _ (by omega))
      (fun j hj => hkeep₁ _ (by omega)) (fun j hj => hkeep₁ _ (by omega)) i
  refine ⟨?_,?_,?_,?_⟩
  · change result=_
    rw [hresult,hmod levels]
  · apply hpool.congr
    intro i hi
    simp only [List.length_map] at hi
    change i < LightPrimePool.size y at hi
    exact hkeep₂ _ (by omega)
  · intro i hi
    change ν (free+3*y+i)=_
    rw [hprefix i hi,hmod i]
  · intro i hi
    exact (hkeep₂ i (by omega)).trans (hkeep₁ i hi)

end ThreeSum.LightBandPrimeConstruction
