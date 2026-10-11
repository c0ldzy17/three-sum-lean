import Submission.ThreeSum.LightBandWeightedScoreSlice
import Submission.ThreeSum.BandCandidateRowsMemory
import Submission.ThreeSum.ReportingHostRelocation

/-!
# Compute one flagged owner's weighted modular score

The actual record supplies its three band indices. This routine computes
their truncated lengths and invokes the existing exact counting program on
those slices. An unflagged record contributes zero without a counting call.
-/

namespace ThreeSum.LightBandWeightedScoreCell

open Light BandCandidateRows BandWeightedScore

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def body (pLength pScore : ℕ) : Stmt :=
  .set 12 (M (v 7)) ;;
  .ite (v 12 =' k 1)
    (.set 13 (M (v 7 +' k 1)) ;;
     .set 14 (M (v 7 +' k 2)) ;;
     .set 15 (M (v 7 +' k 3)) ;;
     .call pLength [v 3,v 6,v 13] 16 ;;
     .call pLength [v 4,v 6,v 14] 17 ;;
     .call pLength [v 5,v 6,v 15] 18 ;;
     .call pScore [v 0 +' v 13 *' v 6,v 1 +' v 14 *' v 6,v 2 +' v 15 *' v 6,
       v 16,v 17,v 18,v 8,v 6,v 9,v 10,v 11] 0)
    (.set 0 (k 0))

def time (maxMod g s U : ℕ) : ℕ :=
  3*LightBandWeightedScoreSlice.time+LightWeightedScore.runtimeTime maxMod g g g s U+250

def word (maxMod nA nB nC g s U : ℕ) : ℕ :=
  LightWeightedScore.word maxMod g s U+nA+nB+nC+g+8

theorem score_time_le {nA nB nC g : ℕ} (maxMod s U : ℕ)
    (hA : nA ≤ g) (hB : nB ≤ g) (hC : nC ≤ g) :
    LightWeightedScore.runtimeTime maxMod nA nB nC s U ≤
      LightWeightedScore.runtimeTime maxMod g g g s U := by
  have hta := Nat.mul_le_mul_right (LightResidues.residueBudget U+30) hA
  have htb := Nat.mul_le_mul_right (LightResidues.residueBudget U+30) hB
  have htc := Nat.mul_le_mul_right (LightResidues.residueBudget U+30) hC
  have hc : LightModuloCounts.time maxMod nA nB nC U ≤ LightModuloCounts.time maxMod g g g U := by
    unfold LightModuloCounts.time LightResidueHistogram.time LightHistogram.histogramTime
      LightHistogram.countTime LightResidues.residuesTime LightLookupSum.time
    omega
  have hs := Nat.mul_le_mul_left s (Nat.add_le_add_right
    (Nat.add_le_add_right hc (LightWeightedScore.jointTime maxMod)) 100)
  unfold LightWeightedScore.runtimeTime LightWeightedScore.time
  omega

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g rec q aux s free maxMod U : ℕ}

theorem meets {pMain pLength pScore : ℕ} (S : LightWeightedScore.Procs P pScore)
    (hmain : P[pMain]?=some (body pLength pScore))
    (hlength : P[pLength]?=some LightBandWeightedScoreSlice.body)
    (primes : ℕ → ℕ) (r : Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+5 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrec : rec+4 ≤ free) (haux : aux+s ≤ free)
    (hspace : LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (word maxMod nA nB nC g s U : ℤ) ≤ lim.word)
    (hrecord : Seg μ rec r.cells) (hflag : r.flag=0 ∨ r.flag=1)
    (hvalid : r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hread : ∀ i < s, μ (aux+i)=(primes i : ℤ))
    (hprime : ∀ i < s, Nat.Prime (primes i))
    (hinj : ∀ i < s, ∀ j < s, primes i=primes j → i=j)
    (hproduct : ∀ i < s, q*primes i ≤ maxMod) :
    Meets lim P pMain d [a,b,c,nA,nB,nC,g,rec,q,aux,s,free] μ (time maxMod g s U)
      (fun result ν => result=(block primes s q nA nB nC g
        (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) r : ℤ) ∧ Kept μ ν free) := by
  have hbudget (k : ℕ) (hk : k ≤ word maxMod nA nB nC g s U) : (k : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hk).trans hword
  have hscoreWord := hbudget (LightWeightedScore.word maxMod g s U) (by unfold word; omega)
  have hlenAWord := hbudget (nA+g+4) (by unfold word; omega)
  have hlenBWord := hbudget (nB+g+4) (by unfold word; omega)
  have hlenCWord := hbudget (nC+g+4) (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  have hgWord := hbudget g (by unfold word; omega)
  have hflagLe : r.flag ≤ 1 := by rcases hflag with hh | hh <;> omega
  have hflagWord : (r.flag : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hflagLe).trans h1Word
  have hfree : free ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  obtain ⟨hfRead,haRead,hbRead,hcRead⟩ := record_fields hrecord
  have hrec1Addr : ((rec : ℤ)+1).toNat=rec+1 := by omega
  have hrec2Addr : ((rec : ℤ)+2).toNat=rec+2 := by omega
  have hrec3Addr : ((rec : ℤ)+3).toNat=rec+3 := by omega
  apply Meets.of_body hmain
  unfold body time
  light_set (r.flag : ℕ) using hfRead
  light_if hf hf : (r.flag : ℤ)=1
  · have hfNat : r.flag=1 := by omega
    obtain ⟨hstartA,hstartB,hstartC⟩ := hvalid hfNat
    have hAi : r.a ≤ nA := (Nat.le_mul_of_pos_right r.a hg).trans hstartA
    have hBi : r.b ≤ nB := (Nat.le_mul_of_pos_right r.b hg).trans hstartB
    have hCi : r.c ≤ nC := (Nat.le_mul_of_pos_right r.c hg).trans hstartC
    have hAiWord := hbudget r.a (by unfold word; omega)
    have hBiWord := hbudget r.b (by unfold word; omega)
    have hCiWord := hbudget r.c (by unfold word; omega)
    have hApWord : (r.a : ℤ)*(g : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show r.a*g ≤ lim.space by omega) : (r.a : ℤ)*(g : ℤ) ≤ lim.space).trans hw
    have hBpWord : (r.b : ℤ)*(g : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show r.b*g ≤ lim.space by omega) : (r.b : ℤ)*(g : ℤ) ≤ lim.space).trans hw
    have hCpWord : (r.c : ℤ)*(g : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show r.c*g ≤ lim.space by omega) : (r.c : ℤ)*(g : ℤ) ≤ lim.space).trans hw
    have hApN : (0 : ℤ) ≤ (r.a : ℤ)*(g : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hBpN : (0 : ℤ) ≤ (r.b : ℤ)*(g : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hCpN : (0 : ℤ) ≤ (r.c : ℤ)*(g : ℤ) := mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    have hAend := end_le (g := g) hstartA
    have hBend := end_le (g := g) hstartB
    have hCend := end_le (g := g) hstartC
    light_set (r.a : ℕ) using haRead,hrec1Addr
    light_set (r.b : ℕ) using hbRead,hrec2Addr
    light_set (r.c : ℕ) using hcRead,hrec3Addr
    light_call (LightBandWeightedScoreSlice.meets (d := d+1) hlength hg hstartA hlenAWord)
      with va μ₁ ⟨hva,hmemA⟩
    subst μ₁
    light_call (LightBandWeightedScoreSlice.meets (d := d+1) hlength hg hstartB hlenBWord)
      with vb μ₂ ⟨hvb,hmemB⟩
    subst μ₂
    light_call (LightBandWeightedScoreSlice.meets (d := d+1) hlength hg hstartC hlenCWord)
      with vc μ₃ ⟨hvc,hmemC⟩
    subst μ₃
    have hcall := (S.meets (d := d+1) (a := a+r.a*g) (b := b+r.b*g) (c := c+r.c*g)
      (nA := length nA g r.a) (nB := length nB g r.b) (nC := length nC g r.c)
      primes hw hq hqmax (by omega) (by omega) (by omega) haux
      (length_le ..) (length_le ..) (length_le ..) hspace hscoreWord (by omega)
      (fun i hi => by rw [Nat.add_assoc]; exact hA _ (position_lt hi))
      (fun i hi => by rw [Nat.add_assoc]; exact hB _ (position_lt hi))
      (fun i hi => by rw [Nat.add_assoc]; exact hC _ (position_lt hi)) hread hprime hinj hproduct).mono_time
        (score_time_le maxMod s U (length_le ..) (length_le ..) (length_le ..))
    light_call hcall using hva,hvb,hvc with value ν ⟨hvalue,hkeep⟩
    refine ⟨?_,hkeep⟩
    change value=_
    rw [hvalue,block,if_pos hfNat]
    simp only [Nat.add_assoc]
  · light_set (0 : ℕ)
    exact ⟨by rw [block,if_neg (show r.flag ≠ 1 by omega)]; rfl,fun _ _ => rfl⟩

def program : Program := LightWeightedScore.program ++
  [LightBandWeightedScoreSlice.body,body 14 0]

theorem program_length : program.length=16 := rfl

def programProcs : LightWeightedScore.Procs program 0 where
  pCount := 2
  pJoint := 1
  count :=
    { pCapacity := 3, pHist := 4, pCyclic := 8, pResidues := 5, pEmod := 6,
      pHistogram := 7, pMultiply := 9, pHalf := 10, pLinear := 11, pFill := 12, pLookup := 13,
      main := rfl, capacity := rfl, hist := rfl, residues := rfl, emod := rfl,
      histogram := rfl, cyclic := rfl, multiply := ⟨rfl,rfl,rfl,rfl⟩, lookup := rfl }
  main := rfl
  joint := rfl

end ThreeSum.LightBandWeightedScoreCell
