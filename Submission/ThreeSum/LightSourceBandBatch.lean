import Submission.ThreeSum.LightSourceBandStep

/-! # Actual once-per-original-band histogram and bucket loop -/

namespace ThreeSum.LightSourceBandBatch

open Light BandPartition SourceBandLayout

set_option maxHeartbeats 2200000
set_option maxRecDepth 16000

def body (pStep : ℕ) : Stmt :=
  .for 12 (v 8) (
    .call pStep [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 13)

def time (n g p m U D : ℕ) : ℕ :=
  size n g*(LightSourceBandStep.time n g p m U D+180)+20

structure Procs (P : Program) (pMain : ℕ) where
  pStep : ℕ
  step : LightSourceBandStep.Procs P pStep
  main : P[pMain]? = some (body pStep)

def Inv (μ : ℕ → ℤ) (f : ℕ → ℤ) (src n g p m base : ℕ) (shift : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [src,n,g,p,m,shift,base,cap n g,size n g,data base n g,stride n g m,
      work base n g m,i,r],ν⟩ ∧
    (∀ j < i, SourceBandData.At ν f base n g p m shift j) ∧ Kept μ ν base

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {src n g p m base U D : ℕ} {shift : ℤ} (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+4 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m) (hsrc : src+n ≤ base)
    (hspace : LightSourceResidues.space (work base n g m) p U D ≤ lim.space)
    (hshift : |shift| ≤ (D : ℤ)) (hword : (LightSourceBandStep.word n g p m U D : ℤ) ≤ lim.word)
    (hread : ∀ j < n, μ (src+j)=f j) (hvalues : ∀ j < n, |f j| ≤ (U : ℤ)) :
    Meets lim P pMain d
      [src,n,g,p,m,shift,base,cap n g,size n g,data base n g,stride n g m,work base n g m]
      μ (time n g p m U D) (fun _ ν =>
        (∀ i < size n g, SourceBandData.At ν f base n g p m shift i) ∧ Kept μ ν base) := by
  have hwork : work base n g m ≤ lim.space := by unfold LightSourceResidues.space at hspace; omega
  have hbase : base ≤ work base n g m := by
    have hh := data_le_hist base n g m (size n g)
    unfold data at hh
    exact (by omega : base ≤ hist base n g m (size n g))
  have hcount := size_le n g
  apply Meets.of_body C.main
  unfold body time
  refine Ends.for (Inv μ f src n g p m base shift) (size n g)
    (LightSourceBandStep.time n g p m U D+172) ?start ?round ?done ?bound
  case start =>
    refine ⟨0,μ,?_,?_,fun _ _ => rfl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi; omega
  case round =>
    rintro i _ hi _ ⟨r,ν,rfl,written,kept⟩
    have hread' : ∀ j < n, ν (src+j)=f j := by
      intro j hj
      exact (kept _ (by omega)).trans (hread j hj)
    have hrun := C.step.meets (d := d+1) (μ := ν) (src := src) (n := n) (g := g)
      (p := p) (m := m) (base := base) (U := U) (D := D) (shift := shift) (i := i)
      f hw (by omega) hg hp hm hi hsrc hspace hshift hword hread' hvalues
    light_call hrun with s ν' ⟨stored,kept'⟩
    refine ⟨by simp,s,ν',by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · exact (written j hj).of_later kept' hm hj hi
      · exact stored
    · intro x hx
      have hb := data_le_hist base n g m i
      unfold data at hb
      exact (kept' x ⟨by omega,Or.inl (by omega)⟩).trans (kept x hx)
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,kept⟩
    exact ⟨written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨r,ν,rfl,_,_⟩
    simp

theorem time_bound (n g p m U D : ℕ) (hg : 0 < g) :
    time n g p m U D ≤
      996*n*(Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1)+size n g*(233*m+1713)+20 := by
  have hc := capacity_product_le n g hg
  have hh := Nat.mul_le_mul_left 498 (Nat.mul_le_mul_right
    (Nat.log 2 (U+1)+Nat.log 2 (p+D+1)+1) hc)
  unfold time LightSourceBandStep.time LightSourceBandStep.charge
  nlinarith

end ThreeSum.LightSourceBandBatch
