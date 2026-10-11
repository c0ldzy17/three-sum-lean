import Submission.ThreeSum.LightBandCandidatesCell

/-! # One actual row of flagged band-owner records -/

namespace ThreeSum.LightBandCandidatesRow

open Light BandCandidateRows

set_option maxHeartbeats 1600000
set_option maxRecDepth 7000

def body (pCell : ℕ) : Stmt :=
  .for 4 (v 2) (
    .set 5 (M (v 0 +' v 4)) ;;
    .call pCell [v 5,v 3,v 4,v 1 +' k 4 *' v 4] 6)

def time (n : ℕ) : ℕ := n*(LightBandCandidatesCell.time+100)+6

def Inv (μ : ℕ → ℤ) (mode : Mode) (f : ℕ → ℕ)
    (src dst n outer j : ℕ) (σ : State) : Prop :=
  ∃ (x r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [src,dst,n,outer,j,x,r],ν⟩ ∧
    (∀ k < j, Seg ν (dst+4*k) (make mode outer k (f k)).cells) ∧
    SameOutside μ ν dst (4*n)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst n outer U : ℕ} {f : ℕ → ℕ}

theorem meets {pMain pCell : ℕ} (mode : Mode)
    (hmain : P[pMain]?=some (body pCell))
    (hcell : P[pCell]?=some (LightBandCandidatesCell.body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+n ≤ dst) (hspace : dst+4*n ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word)
    (hn : n ≤ U) (houter : outer ≤ U)
    (hf : ∀ j < n, f j ≤ U) (hread : ∀ j < n, μ (src+j)=(f j : ℤ)) :
    Meets lim P pMain d [src,dst,n,outer] μ (time n)
      (fun _ ν =>
        (∀ j < n, Seg ν (dst+4*j) (make mode outer j (f j)).cells) ∧
        SameOutside μ ν dst (4*n)) := by
  have hnWord : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : n ≤ U+10)).trans hword
  have hoWord : (outer : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : outer ≤ U+10)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ mode f src dst n outer) n
    (LightBandCandidatesCell.time+92) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,0,μ,?_,?_,SameOutside.refl⟩
    · simp [update_frame_setLocal]
      exact (frame_append_zeros [src,dst,n,outer,0] 2).symm
    · intro k hk; omega
  case round =>
    rintro j _ hj _ ⟨x,r,ν,rfl,written,kept⟩
    have hjWord : (j : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : j ≤ U+10)).trans hword
    have hfWord : (f j : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by have := hf j hj; omega : f j ≤ U+10)).trans hword
    have hread' : ν (src+j)=(f j : ℤ) := by
      rw [kept _ (Or.inl (by omega))]
      exact hread j hj
    light_set (f j : ℕ) using hread'
    have hc := LightBandCandidatesCell.meets (d := d+1) (μ := ν)
      (r := f j) (i := outer) (j := j) (dst := dst+4*j)
      mode hcell hw (by omega) hword (hf j hj) houter (by omega)
    light_call hc using LightBandCandidatesCell.time with value ν₁ ⟨hrow,hkeep⟩
    refine ⟨by simp,f j,value,ν₁,by simp [update_frame_setLocal],?_,?_⟩
    · intro k hk
      rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
      · exact (written k hk).of_sameOutside hkeep (Or.inl (by simp [Record.cells]; omega))
      · exact hrow
    · intro a ha
      rw [hkeep a (by unfold Outside at *; omega),kept a ha]
  case done =>
    rintro _ _ ⟨x,r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro j _ _ _ ⟨x,r,ν,rfl,_,_⟩
    light_side

end ThreeSum.LightBandCandidatesRow
