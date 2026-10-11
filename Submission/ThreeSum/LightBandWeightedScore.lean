import Submission.ThreeSum.LightBandWeightedScoreCell

/-!
# Actual aggregate weighted scoring over the band-owner catalog

The fixed program scans the physical four-cell records once, reuses the
same counting scratch for every flagged owner, and sums their exact scores.
Both the original arrays and complete owner catalog are retained.
-/

namespace ThreeSum.LightBandWeightedScore

open Light BandCandidateRows BandWeightedScore

set_option maxHeartbeats 2200000
set_option maxRecDepth 10000

def body (pCell : ℕ) : Stmt :=
  .set 13 (k 0) ;;
  .for 14 (v 8) (
    .call pCell [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7 +' k 4 *' v 14,v 9,v 10,v 11,v 12] 15 ;;
    .set 13 (v 13 +' v 15)) ;;
  .set 0 (v 13)

def program : Program := LightBandWeightedScoreCell.program ++ [body 15]

theorem program_length : program.length=17 := rfl

def time (maxMod g R s U : ℕ) : ℕ := R*(LightBandWeightedScoreCell.time maxMod g s U+100)+50

def word (maxMod nA nB nC g R s U : ℕ) : ℕ :=
  LightBandWeightedScoreCell.word maxMod nA nB nC g s U+R*(s*g^3)+R+8

def Inv (μ : ℕ → ℤ) (f : ℕ → ℕ)
    (a b c nA nB nC g recs R q aux s free i : ℕ) (σ : State) : Prop :=
  ∃ (value : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [a,b,c,nA,nB,nC,g,recs,R,q,aux,s,free,f i,i,value],ν⟩ ∧ Kept μ ν free

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs q aux s free maxMod U : ℕ}

theorem program_meets (primes : ℕ → ℕ) (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+Nat.clog 2 maxMod+6 ≤ lim.depth)
    (hg : 0 < g) (hq : 0 < q) (hqmax : q ≤ maxMod)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free) (haux : aux+s ≤ free)
    (hspace : LightWeightedScore.space free maxMod g U ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length s U : ℤ) ≤ lim.word)
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
    Meets lim program 16 d [a,b,c,nA,nB,nC,g,recs,rs.length,q,aux,s,free] μ
      (time maxMod g rs.length s U)
      (fun result ν => result=(score primes s q nA nB nC g
        (fun i => μ (a+i)) (fun i => μ (b+i)) (fun i => μ (c+i)) rs : ℤ) ∧ Kept μ ν free) := by
  let A := fun i => μ (a+i)
  let B := fun i => μ (b+i)
  let C := fun i => μ (c+i)
  let f := partialScore primes s q nA nB nC g A B C rs
  have hf0 : f 0=0 := partialScore_zero ..
  have hbudget (k : ℕ) (hk : k ≤ word maxMod nA nB nC g rs.length s U) : (k : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hk).trans hword
  have hcellWord := hbudget (LightBandWeightedScoreCell.word maxMod nA nB nC g s U)
    (by unfold word; omega)
  have htotalWord := hbudget (rs.length*(s*g^3)) (by unfold word; omega)
  have hfWord (i : ℕ) (hi : i ≤ rs.length) : (f i : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((partialScore_bound primes s q nA nB nC g A B C rs i hprime hinj).trans
      (Nat.mul_le_mul_right _ hi))).trans htotalWord
  have hfree : free ≤ lim.space := by
    have hh := (le_max_right _ _).trans hspace
    change free+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    omega
  have hcall (ν : ℕ → ℤ) (i : ℕ) (hi : i < rs.length) (hkeep : Kept μ ν free) :
      Meets lim program 15 (d+1) [a,b,c,nA,nB,nC,g,recs+4*i,q,aux,s,free] ν
        (LightBandWeightedScoreCell.time maxMod g s U)
        (fun value ξ => value=(block primes s q nA nB nC g A B C (rs.getD i default) : ℤ) ∧ Kept ν ξ free) := by
    have hmem : rs.getD i default ∈ rs := by
      rw [List.getD_eq_getElem _ _ hi]
      exact List.getElem_mem hi
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
    refine ((LightBandWeightedScoreCell.meets (d := d+1) (μ := ν)
      LightBandWeightedScoreCell.programProcs (pMain := 15) (pLength := 14) rfl rfl primes (rs.getD i default)
      hw (by omega) hg hq hqmax ha hb hc (by omega) haux hspace hcellWord
      (seg_record hrecordsν hi) (hflag _ hmem) (hvalid _ hmem)
      hAν hBν hCν hreadν hprime hinj hproduct).append [body 15]).mono le_rfl ?_
    rintro value ξ ⟨hvalue,hkeep'⟩
    refine ⟨hvalue.trans ?_,hkeep'⟩
    congr 1
    exact block_congr _ (fun j hj => hkeep _ (by omega))
      (fun j hj => hkeep _ (by omega)) (fun j hj => hkeep _ (by omega))
  apply Meets.of_body (p := 16) (by rfl : program[16]?=some (body 15))
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := rs.length*(LightBandWeightedScoreCell.time maxMod g s U+100)+6)
    (Q := Inv μ f a b c nA nB nC g recs rs.length q aux s free rs.length)
    (Inv μ f a b c nA nB nC g recs rs.length q aux s free) rs.length
    (LightBandWeightedScoreCell.time maxMod g s U+92) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,μ,?_,fun _ _ => rfl⟩
    simp [update_frame_setLocal,hf0]
    exact (frame_append_zeros [a,b,c,nA,nB,nC,g,recs,rs.length,q,aux,s,free,0,0] 1).symm
  case round =>
    rintro i _ hi _ ⟨old,ν,rfl,hkeep⟩
    have hsum := partialScore_succ primes s q nA nB nC g A B C rs i
    change f (i+1)=f i+block primes s q nA nB nC g A B C (rs.getD i default) at hsum
    have hfi := hfWord i (by omega)
    have hnext := hfWord (i+1) (by omega)
    have hsumWord : (f i : ℤ)+(block primes s q nA nB nC g A B C (rs.getD i default) : ℤ) ≤ lim.word := by
      rw [hsum,Nat.cast_add] at hnext
      exact hnext
    have hsumNonneg : (0 : ℤ) ≤ (f i : ℤ)+(block primes s q nA nB nC g A B C (rs.getD i default) : ℤ) :=
      add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    simp only [List.getD] at hsumWord hsumNonneg hsum
    light_call (hcall ν i hi hkeep) with value ξ ⟨hvalue,hkeep'⟩
    subst value
    light_set (f (i+1) : ℕ) using hsum
    refine ⟨by simp,(block primes s q nA nB nC g A B C (rs.getD i default) : ℤ),ξ,?_,?_⟩
    · simp [update_frame_setLocal]
    · exact fun j hj => (hkeep' j hj).trans (hkeep j hj)
  case done =>
    rintro _ _ H
    exact H
  case bound =>
    rintro i _ hi _ ⟨old,ν,rfl,hkeep⟩
    have hfi := hfWord i hi
    light_side
  case finish =>
    rintro _ ⟨old,ν,rfl,hkeep⟩
    have hf := hfWord rs.length le_rfl
    light_set (f rs.length : ℕ)
    exact ⟨rfl,hkeep⟩

end ThreeSum.LightBandWeightedScore
