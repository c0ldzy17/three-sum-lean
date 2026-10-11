import Submission.ThreeSum.LightBandRawARow

/-! # Append the actual A band of one flagged owner record -/

namespace ThreeSum.LightBandRawAStep

open Light BandCandidateRows BandRawA

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def tail (pRow : ℕ) : Stmt :=
  .call pRow [v 0 +' v 10,v 6 +' v 9,v 7 +' v 9,v 8 +' v 9,v 11,v 5,v 10] 12 ;;
  .set 0 (v 9 +' v 11)

/-- Sorted A base and length, g, flag, A band, owner, three output bases,
and the previous incidence count. -/
def body (pRow : ℕ) : Stmt :=
  .ite (v 3 =' k 1)
    (.set 10 (v 4 *' v 2) ;;
      .set 11 (v 1 -' v 10) ;;
      .ite (v 2 <' v 11) (.set 11 (v 2)) .skip ;;
      tail pRow)
    (.set 0 (v 9))

def time (g : ℕ) : ℕ := LightBandRawARow.time g+250

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src n g owner values owners positions previous capacity : ℕ} {r : Record}

theorem meets {pMain pRow pCopy pFill : ℕ}
    (hmain : P[pMain]?=some (body pRow))
    (hrow : P[pRow]?=some (LightBandRawARow.body pCopy pFill))
    (hcopy : P[pCopy]?=some copyBody) (hfill : P[pFill]?=some fillBody)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hg : 0 < g)
    (hvalid : r.flag=1 → r.a < BandPartition.size n g)
    (hsrc : src+n ≤ values) (hvalues : values+capacity ≤ owners)
    (howners : owners+capacity ≤ positions) (hspace : positions+capacity ≤ lim.space)
    (hfit : previous+(row n g owner r).length ≤ capacity)
    (hword : ((n+g+owner+10 : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pMain d [src,n,g,r.flag,r.a,owner,values,owners,positions,previous] μ (time g)
      (fun result ν => result=((previous+(row n g owner r).length : ℕ) : ℤ) ∧
        (∀ j < (row n g owner r).length,
          ν (values+previous+j)=μ (src+BandPartition.start g r.a+j) ∧
          ν (owners+previous+j)=(owner : ℤ) ∧
          ν (positions+previous+j)=((BandPartition.start g r.a+j : ℕ) : ℤ)) ∧
        LightBandRawARow.KeptOthers μ ν (values+previous) (owners+previous)
          (positions+previous) (row n g owner r).length) := by
  have hnWord : (n : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : n ≤ n+g+owner+10)).trans hword
  have hgWord : (g : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : g ≤ n+g+owner+10)).trans hword
  have hoWord : (owner : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by omega : owner ≤ n+g+owner+10)).trans hword
  have hpWord : (previous : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (show previous ≤ lim.space by omega)).trans hw
  apply Meets.of_body hmain
  unfold body time
  light_if hf hf : (r.flag : ℤ)=1
  · have hfN : r.flag=1 := by exact_mod_cast hf
    have ha := hvalid hfN
    let s := BandPartition.start g r.a
    have hs : s < n := BandPartition.start_lt hg ha
    have hsWord : (r.a : ℤ)*(g : ℤ) ≤ lim.word := by
      have hh : r.a*g ≤ n := hs.le
      exact (by exact_mod_cast hh : (r.a : ℤ)*(g : ℤ) ≤ (n : ℤ)).trans hnWord
    have hsNonneg : (0 : ℤ) ≤ (r.a : ℤ)*(g : ℤ) := by positivity
    have hlen : (row n g owner r).length=bandLength n g r.a := by rw [row_length,if_pos hfN]
    have hlenG : bandLength n g r.a ≤ g := BandPartition.length_le n g r.a
    have hslen : s+bandLength n g r.a ≤ n := by
      have hstart := BandPartition.start_lt_stop hg ha
      have hstop := BandPartition.stop_le n g r.a
      unfold bandLength
      dsimp [s]
      omega
    have htail (len : ℕ) (he : len=bandLength n g r.a) :
        Ends lim P d (tail pRow)
          ⟨frame [src,n,g,r.flag,r.a,owner,values,owners,positions,previous,s,len],μ⟩
          (LightBandRawARow.time g+100)
          (fun σ => σ.loc 0=((previous+(row n g owner r).length : ℕ) : ℤ) ∧
            (∀ j < (row n g owner r).length,
              σ.mem (values+previous+j)=μ (src+BandPartition.start g r.a+j) ∧
              σ.mem (owners+previous+j)=(owner : ℤ) ∧
              σ.mem (positions+previous+j)=((BandPartition.start g r.a+j : ℕ) : ℤ)) ∧
            LightBandRawARow.KeptOthers μ σ.mem (values+previous) (owners+previous)
              (positions+previous) (row n g owner r).length) := by
      have hlenFit : previous+len ≤ capacity := by rwa [hlen,← he] at hfit
      have hlenLe : len ≤ g := by omega
      have hslen' : s+len ≤ n := by omega
      have hcost : LightBandRawARow.time len ≤ LightBandRawARow.time g := by
        unfold LightBandRawARow.time copyTime fillTime
        omega
      unfold tail
      have hc := LightBandRawARow.meets (d := d+1) (μ := μ)
        (src := src+s) (values := values+previous) (owners := owners+previous)
        (positions := positions+previous) (n := len) (owner := owner) (start := s)
        hrow hcopy hfill hw (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      light_call (hc.mono_time hcost) with unused ν ⟨hout,hkeep⟩
      light_set (previous+len : ℕ)
      refine ⟨?_,?_,?_⟩
      · simp [update_frame_setLocal,hlen,← he]
      · simpa only [hlen,← he,s] using hout
      · simpa only [hlen,← he] using hkeep
    light_set (s : ℕ) using s,BandPartition.start
    light_set (n-s : ℕ)
    light_if hgmin hgmin : (g : ℤ) < ((n-s : ℕ) : ℤ)
    · have hlenEq : g=bandLength n g r.a := by rw [bandLength_eq_min]; dsimp [s] at hgmin; omega
      light_set (g : ℕ)
      light_piece (htail g hlenEq) with σ h
      light_skip
      exact h
    · have hlenEq : n-s=bandLength n g r.a := by rw [bandLength_eq_min]; dsimp [s] at hgmin; omega
      light_piece (htail (n-s) hlenEq) with σ h
      light_skip
      exact h
  · have hfN : r.flag ≠ 1 := by exact_mod_cast hf
    have hlen : (row n g owner r).length=0 := by simp [row,hfN]
    light_set (previous : ℕ)
    refine ⟨by rw [hlen]; simp,?_,SameOn.refl⟩
    intro j hj
    rw [hlen] at hj
    omega

end ThreeSum.LightBandRawAStep
