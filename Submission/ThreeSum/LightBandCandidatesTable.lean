import Submission.ThreeSum.LightBandCandidatesRow
import Submission.ThreeSum.BandCandidateRowsMemory

/-! # Actual rectangular owner records with two nested loops -/

namespace ThreeSum.LightBandCandidatesTable

open Light BandCandidateRows

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pRow : ℕ) : Stmt :=
  .for 4 (v 2) (
    .call pRow [v 0 +' v 4 *' v 3,v 1 +' k 4 *' (v 4 *' v 3),v 3,v 4] 5)

def time (m n : ℕ) : ℕ := m*(LightBandCandidatesRow.time n+100)+6

def Inv (μ : ℕ → ℤ) (mode : Mode) (f : ℕ → ℕ → ℕ)
    (src dst m n i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [src,dst,m,n,i,r],ν⟩ ∧
    (∀ x < i, ∀ y < n, Seg ν (dst+4*(x*n+y)) (make mode x y (f x y)).cells) ∧
    SameOutside μ ν dst (4*(m*n))

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {src dst m n U : ℕ} {f : ℕ → ℕ → ℕ}

theorem meets {pMain pRow pCell : ℕ} (mode : Mode)
    (hmain : P[pMain]?=some (body pRow))
    (hrow : P[pRow]?=some (LightBandCandidatesRow.body pCell))
    (hcell : P[pCell]?=some (LightBandCandidatesCell.body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hsrc : src+m*n ≤ dst) (hspace : dst+4*(m*n) ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word) (hm : m ≤ U) (hn : n ≤ U)
    (hf : ∀ i < m, ∀ j < n, f i j ≤ U)
    (hread : ∀ i < m, ∀ j < n, μ (src+i*n+j)=(f i j : ℤ)) :
    Meets lim P pMain d [src,dst,m,n] μ (time m n)
      (fun _ ν =>
        (∀ i < m, ∀ j < n, Seg ν (dst+4*(i*n+j)) (make mode i j (f i j)).cells) ∧
        SameOutside μ ν dst (4*(m*n))) := by
  have hmWord : (m : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : m ≤ U+10)).trans hword
  have hnWord : (n : ℤ) ≤ lim.word := (Int.ofNat_le.mpr (by omega : n ≤ U+10)).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ mode f src dst m n) m
    (LightBandCandidatesRow.time n+92) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · simp [update_frame_setLocal]
      exact (frame_append_zeros [src,dst,m,n,0] 1).symm
    · intro x hx; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hprod := Nat.mul_le_mul_right n (show i+1 ≤ m by omega)
    simp only [Nat.add_mul,Nat.one_mul] at hprod
    have hmulWord : (i : ℤ)*(n : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show i*n ≤ lim.space by omega) :
        (i : ℤ)*(n : ℤ) ≤ (lim.space : ℤ)).trans hw
    have hmulNonneg : (0 : ℤ) ≤ (i : ℤ)*(n : ℤ) := by positivity
    have hfourWord : 4*((i : ℤ)*(n : ℤ)) ≤ lim.word :=
      (by exact_mod_cast (show 4*(i*n) ≤ lim.space by omega) :
        4*((i : ℤ)*(n : ℤ)) ≤ (lim.space : ℤ)).trans hw
    have hfourNonneg : (0 : ℤ) ≤ 4*((i : ℤ)*(n : ℤ)) := by positivity
    have hread' : ∀ j < n, ν (src+i*n+j)=(f i j : ℤ) := by
      intro j hj
      rw [kept _ (Or.inl (by omega))]
      exact hread i hi j hj
    have hc := LightBandCandidatesRow.meets (d := d+1) (μ := ν)
      (src := src+i*n) (dst := dst+4*(i*n)) (n := n) (outer := i) (f := f i)
      mode hrow hcell hw (by omega) (by omega) (by omega) hword hn (by omega)
      (hf i hi) hread'
    light_call hc using LightBandCandidatesRow.time,LightBandCandidatesCell.time
      with value ν₁ ⟨hrows,hkeep⟩
    refine ⟨by simp,value,ν₁,by simp [update_frame_setLocal],?_,?_⟩
    · intro x hx y hy
      rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
      · have hxy := index_lt hx hy
        exact (written x hx y hy).of_sameOutside hkeep
          (Or.inl (by simp [Record.cells]; omega))
      · simpa only [show dst+4*(x*n)+4*y=dst+4*(x*n+y) by ring] using hrows y hy
    · intro a ha
      rw [hkeep a (by unfold Outside at *; omega),kept a ha]
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    light_side

theorem meets_segment {pMain pRow pCell : ℕ} (mode : Mode)
    (hmain : P[pMain]?=some (body pRow))
    (hrow : P[pRow]?=some (LightBandCandidatesRow.body pCell))
    (hcell : P[pCell]?=some (LightBandCandidatesCell.body mode))
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hsrc : src+m*n ≤ dst) (hspace : dst+4*(m*n) ≤ lim.space)
    (hword : ((U+10 : ℕ) : ℤ) ≤ lim.word) (hm : m ≤ U) (hn : n ≤ U)
    (hf : ∀ i < m, ∀ j < n, f i j ≤ U)
    (hread : ∀ i < m, ∀ j < n, μ (src+i*n+j)=(f i j : ℤ)) :
    Meets lim P pMain d [src,dst,m,n] μ (time m n)
      (fun _ ν => Seg ν dst (cells (rect m n (fun i j => make mode i j (f i j)))) ∧
        SameOutside μ ν dst (4*(m*n))) :=
  (meets mode hmain hrow hcell hw hd hsrc hspace hword hm hn hf hread).mono le_rfl
    (fun _ _ h => ⟨seg_rect _ h.1,h.2⟩)

def program (mode : Mode) : Program :=
  [body 1,LightBandCandidatesRow.body 2,LightBandCandidatesCell.body mode]

end ThreeSum.LightBandCandidatesTable
