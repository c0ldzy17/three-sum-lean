import Submission.ThreeSum.LightBandPrimeDepth
import Submission.ThreeSum.LightBandPrimeConstruction

/-!
# Compute the chain depth and construct the common owner modulus

Only the original arrays, candidate records, radix and prime window are
inputs. The host computes the prescribed depth, generates its own prime
pool and executes the common minimum chain, retaining all prefix moduli.
-/

namespace ThreeSum.LightBandPrimeSetup

open Light BandCandidateRows

set_option maxHeartbeats 1600000
set_option maxRecDepth 9000

def body (pDepth pConstruct : ℕ) : Stmt :=
  .call pDepth [v 9,v 10] 12 ;;
  .call pConstruct [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 10,v 12,v 11] 0

def program : Program := ReportingHostRelocation.program
  LightBandPrimeDepth.program LightBandPrimeConstruction.program ++ [body 0 23]

theorem program_length : program.length=25 := rfl

def time (maxMod g count M y U : ℕ) : ℕ := LightBandPrimeDepth.time M y+
  LightBandPrimeConstruction.time maxMod g count y U (LightBandPrimeDepth.depth M y)+100

def space (free maxMod g M y U : ℕ) : ℕ :=
  LightBandPrimeConstruction.space free maxMod g y U (LightBandPrimeDepth.depth M y)

def word (maxMod nA nB nC g count M y U : ℕ) : ℕ :=
  max (LightBandPrimeDepth.word M y)
    (LightBandPrimeConstruction.word maxMod nA nB nC g count y U)

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}

theorem program_meets (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free)
    (hspace : space free maxMod g M y U ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+10 ≤ lim.depth)
    (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hmax : (4*y)^(LightBandPrimeDepth.depth M y+1) ≤ maxMod) :
    Meets lim program 24 d [a,b,c,nA,nB,nC,g,recs,rs.length,M,y,free] μ
      (time maxMod g rs.length M y U)
      (fun result ν =>
        result=(LightBandPrimeConstruction.modulus y nA nB nC g
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs
            (LightBandPrimeDepth.depth M y) : ℤ) ∧
        SegN ν free (LightPrimePool.values y) ∧
        (∀ i ≤ LightBandPrimeDepth.depth M y,
          ν (free+3*y+i)=(LightBandPrimeConstruction.modulus y nA nB nC g
            (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs i : ℤ)) ∧
        Kept μ ν free) := by
  have hdWord : (LightBandPrimeDepth.word M y : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hcWord : (LightBandPrimeConstruction.word maxMod nA nB nC g rs.length y U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_right _ _)).trans hword
  apply Meets.of_body (p := 24) (by rfl : program[24]?=some (body 0 23))
  unfold body time
  have hD := ((LightBandPrimeDepth.program_meets (d := d+1) (μ := μ) hy hdWord).append
    (LightBandPrimeConstruction.program.map (ReportingHostRelocation.relocate 1))).append [body 0 23]
  light_call hD with levels μ₁ ⟨hlevels,hmem⟩
  subst μ₁
  have hC := (ReportingHostRelocation.meets
    (LightBandPrimeConstruction.program_meets (d := d+1) (μ := μ)
      (a := a) (b := b) (c := c) (y := y) (levels := LightBandPrimeDepth.depth M y)
      rs hw hy hg ha hb hc hrecs hspace hcWord (by omega)
      hrecords hflag hvalid hA hB hC hmax) LightBandPrimeDepth.program).append [body 0 23]
  light_call hC using hlevels with result ν hresult
  exact hresult

end ThreeSum.LightBandPrimeSetup
