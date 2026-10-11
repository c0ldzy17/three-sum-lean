import Submission.ThreeSum.LightDenseCap
import Submission.ThreeSum.LightBandWeightedScore
import Submission.ThreeSum.BandRawAFinite

/-!
# Construct the dense-stop threshold from actual cover and source records

The host computes the representation cap, recomputes the exact aggregate
weighted score at the selected common modulus, multiplies the two, and
initializes the running counter. The four retained cells are counter,
threshold, representation cap and weighted score. Scratch starts after them.
-/

namespace ThreeSum.LightDenseSetup

open Light GlobalEncoding BandCandidateRows

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def body (pCap pScore : ℕ) : Stmt :=
  .set 15 (v 14 +' k 4) ;;
  .call pCap [v 12,v 13] 16 ;;
  .call pScore [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 15] 17 ;;
  .set 18 (v 16 *' v 17) ;;
  .store (v 14) (k 0) ;;
  .store (v 14 +' k 1) (v 18) ;;
  .store (v 14 +' k 2) (v 16) ;;
  .store (v 14 +' k 3) (v 17) ;;
  .set 0 (v 14)

def joinedProgram : Program :=
  ReportingHostRelocation.program LightDenseCap.program LightBandWeightedScore.program

def program : Program := joinedProgram++[body 0 18]

theorem program_length : program.length=20 := rfl

def time (maxMod g R s U J : ℕ) : ℕ :=
  LightDenseCap.time J+LightBandWeightedScore.time maxMod g R s U+400

def word (maxMod nA nB nC g R s U h J : ℕ) : ℕ :=
  LightDenseCap.word h J+LightBandWeightedScore.word maxMod nA nB nC g R s U+
    representationCap h J*(R*(s*g^3))+representationCap h J+20

def Stored (μ : ℕ → ℤ) (free cap H : ℕ) : Prop :=
  μ free=0 ∧ μ (free+1)=((cap*H : ℕ) : ℤ) ∧
    μ (free+2)=(cap : ℤ) ∧ μ (free+3)=(H : ℤ)

def falseScore (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) : ℕ :=
  Arithmetic.weightedFalseCount (BandRawA.finiteAllProducts nA nB nC g rs)
    (fun t => C t.2.2.val-B t.2.1.val-BandRawA.valueAt nA g rs A t.1.val)
    (Auxiliary.moduli (WeightedScore.auxiliarySet primes s)) q

theorem falseScore_eq (primes : ℕ → ℕ) (s q nA nB nC g : ℕ)
    (A B C : ℕ → ℤ) (rs : List Record) :
    falseScore primes s q nA nB nC g A B C rs=
      BandWeightedScore.score primes s q nA nB nC g A B C rs :=
  BandRawA.finiteAll_weightedFalseCount primes s q nA nB nC g A B C rs

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s cover free maxMod U h J : ℕ}

theorem program_meets (primes : ℕ → ℕ) (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+7 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free) (haux : aux+s ≤ free)
    (hcover : LightCoverKeyData.keyEnd cover h J ≤ free)
    (hspace : LightWeightedScore.space (free+4) maxMod g U ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length s U h J : ℤ) ≤ lim.word)
    (H : LightCoverKeyData.Stored μ cover h J)
    (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim program 19 d [a,b,c,nA,nB,nC,g,recs,rs.length,q,aux,s,cover,J,free] μ
      (time maxMod g rs.length s U J)
      (fun result ν => result=(free : ℤ) ∧
        Stored ν free (representationCap h J)
          (falseScore primes s q nA nB nC g
            (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs) ∧
        LightCoverKeyData.Stored ν cover h J ∧ Kept μ ν free) := by
  let score := BandWeightedScore.score primes s q nA nB nC g
    (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs
  have budget (x : ℕ) (hx : x ≤ word maxMod nA nB nC g rs.length s U h J) :
      (x : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hx).trans hword
  have hcapWord := budget (LightDenseCap.word h J) (by unfold word; omega)
  have hscoreWord := budget (LightBandWeightedScore.word maxMod nA nB nC g rs.length s U)
    (by unfold word; omega)
  have hcapFit := budget (representationCap h J) (by unfold word; omega)
  have hsBound : score ≤ rs.length*(s*g^3) :=
    BandWeightedScore.score_bound primes s q nA nB nC g _ _ _ rs hprime hinj
  have hthresholdFit : ((representationCap h J*score : ℕ) : ℤ) ≤ lim.word := by
    apply budget
    exact (Nat.mul_le_mul_left _ hsBound).trans (by unfold word; omega)
  have hthresholdZ : (representationCap h J : ℤ)*(score : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_mul] using hthresholdFit
  have hthresholdN : (0 : ℤ) ≤ (representationCap h J : ℤ)*(score : ℤ) := by positivity
  have hscoreFit : (score : ℤ) ≤ lim.word := by
    apply budget
    apply hsBound.trans
    unfold word LightBandWeightedScore.word
    omega
  have hfree : free+4 ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+4+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hcoverBase := LightLocalCoverRetention.base_le_nextFree (LightLocalCoverInit.base cover) h
  change cover+20 ≤ LightCoverKeys.afterCover cover h at hcoverBase
  have hcoverNext := LightCoverKeyData.afterCover_le_keyEnd cover h J
  apply Meets.of_body (p := 19) (by rfl : program[19]?=some (body 0 18))
  unfold body time
  light_set (free+4 : ℕ)
  have hcapCall := ((LightDenseCap.program_meets (d := d+1) (μ := μ)
    hw (by omega) hcapWord (by omega) H).append
      (LightBandWeightedScore.program.map (ReportingHostRelocation.relocate 2))).append [body 0 18]
  light_call hcapCall with cap μ₁ ⟨hcap,hμ₁⟩
  subst μ₁
  have hscoreCall := (ReportingHostRelocation.meets
    (LightBandWeightedScore.program_meets (d := d+1) (μ := μ) (free := free+4)
      primes rs hw (by omega) hg hq hqmax (by omega) (by omega) (by omega)
      (by omega) (by omega) hspace hscoreWord hrecords hflag hvalid hA hB hC
      hread hprime hinj hproduct) LightDenseCap.program).append [body 0 18]
  light_call hscoreCall with total μ₂ ⟨hscore,hkeep⟩
  have htotal : total=(score : ℤ) := hscore
  light_set (representationCap h J*score : ℕ) using hcap,htotal
  light_store free (0 : ℕ)
  light_store (free+1) (representationCap h J*score : ℕ)
  light_store (free+2) (representationCap h J : ℕ) using hcap
  light_store (free+3) (score : ℕ) using htotal
  light_set (free : ℕ)
  refine ⟨rfl,?_,?_,?_⟩
  · exact ⟨by simp,by simp [score,falseScore_eq],by simp,by simp [score,falseScore_eq]⟩
  · apply H.of_kept
    intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₂ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeep i (by omega)
  · intro i hi
    change Function.update (Function.update (Function.update (Function.update μ₂ free _)
      (free+1) _) (free+2) _) (free+3) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),
      Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeep i (by omega)

end ThreeSum.LightDenseSetup
