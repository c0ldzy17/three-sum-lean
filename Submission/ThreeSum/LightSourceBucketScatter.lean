import Submission.ThreeSum.SourceBuckets

/-!
# Actual linear scatter of original indices into residue buckets

Each original physical index is stored exactly once at its current bucket
cursor; that cursor is incremented. The position proof supplies complete,
duplicate-free fibers and charges one constant-time iteration per input.
-/

namespace ThreeSum.LightSourceBucketScatter

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body : Stmt :=
  .for 5 (v 3) (
    .set 6 (M (v 0 +' v 5)) ;;
    .set 7 (M (v 1 +' v 6)) ;;
    .store (v 2 +' v 7) (v 5) ;;
    .store (v 1 +' v 6) (v 7 +' k 1))

def time (N : ℕ) : ℕ := 120*N+20

def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (keys cursor flat N M i : ℕ) (σ : State) : Prop :=
  ∃ (k q : ℤ) (ν : ℕ → ℤ), σ = ⟨frame [keys,cursor,flat,N,M,i,k,q],ν⟩ ∧
    (∀ r < M, ν (cursor+r) = ((offset key N r+count key r i : ℕ) : ℤ)) ∧
    (∀ j < i, ν (flat+position key N j) = (j : ℤ)) ∧
    SameOutside μ ν cursor (flat+N-cursor)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain : ℕ} (hmain : P[pMain]? = some body)
    {μ : ℕ → ℤ} {keys cursor flat N M : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+N ≤ cursor) (hcursor : cursor+M ≤ flat) (hspace : flat+N ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ i < N, μ (keys+i) = (key i : ℤ))
    (hzero : ∀ r < M, μ (cursor+r) = (offset key N r : ℤ)) :
    Meets lim P pMain d [keys,cursor,flat,N,M] μ (time N)
      (fun _ ν => (∀ i < N, ν (flat+position key N i) = (i : ℤ)) ∧
        (∀ r < M, ν (cursor+r) = (offset key N (r+1) : ℤ)) ∧
        SameOutside μ ν cursor (flat+N-cursor)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ key keys cursor flat N M) N 112 ?start ?round ?done ?bound
  case start =>
    refine ⟨0,0,μ,?_,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 2).symm)
    · simpa only [count_zero,Nat.add_zero] using hzero
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨k,q,ν,rfl,cursors,written,kept⟩
    have hki := hkey i hi
    have hread' : ν (keys+i) = (key i : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hread i hi)
    have hcur : ν (cursor+key i) = (position key N i : ℤ) := cursors (key i) hki
    have hpos := position_lt hkey hi
    have hkiWord : (key i : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show key i ≤ lim.space by omega) : (key i : ℤ) ≤ lim.space).trans hw
    have hposWord : (position key N i : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show position key N i ≤ lim.space by omega) :
        (position key N i : ℤ) ≤ lim.space).trans hw
    have hnextWord : (position key N i+1 : ℤ) ≤ lim.word :=
      (by exact_mod_cast (show position key N i+1 ≤ lim.space by omega) :
        (position key N i+1 : ℤ) ≤ lim.space).trans hw
    light_set (key i : ℕ) using hread'
    light_set (position key N i : ℕ) using hcur
    light_store (flat+position key N i) (i : ℕ)
    light_store (cursor+key i) (position key N i+1 : ℕ)
    refine ⟨by simp,key i,position key N i,
      Function.update (Function.update ν (flat+position key N i) (i : ℤ))
        (cursor+key i) (position key N i+1 : ℕ),
      by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro r hr
      rw [count_succ]
      by_cases he : key i = r
      · subst r
        rw [Function.update_self]
        simp only [ite_true,position,Nat.cast_add,Nat.cast_one]
        ring
      · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),cursors r hr]
        simp only [he,ite_false,Nat.add_zero]
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · have hne : position key N j ≠ position key N i := by
          intro he
          have hh := position_injective (show j < N by omega) hi he
          omega
        rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
        exact written j hj
      · rw [Function.update_of_ne (by omega),Function.update_self]
    · intro a ha
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    rintro _ _ ⟨k,q,ν,rfl,cursors,written,kept⟩
    refine ⟨written,?_,kept⟩
    intro r hr
    rw [offset_succ]
    exact cursors r hr
  case bound =>
    rintro i _ hi _ ⟨k,q,ν,rfl,_,_,_⟩
    simp

def program : Program := [body]

end ThreeSum.LightSourceBucketScatter
