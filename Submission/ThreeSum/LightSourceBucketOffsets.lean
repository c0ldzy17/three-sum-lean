import Submission.ThreeSum.SourceBuckets

/-!
# Actual prefix offsets and initial scatter cursors

One linear scan of the retained count histogram writes all M+1 bucket
offsets and the M initial cursors. Original arrays before the output remain
untouched; no bucket is found by searching its original indices.
-/

namespace ThreeSum.LightSourceBucketOffsets

open Light SourceBuckets LightHistogram

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def body : Stmt :=
  .set 6 (k 0) ;;
  .for 5 (v 3) (
    .store (v 1 +' v 5) (v 6) ;;
    .store (v 2 +' v 5) (v 6) ;;
    .set 6 (v 6 +' M (v 0 +' v 5))) ;;
  .store (v 1 +' v 3) (v 6)

def time (M : ℕ) : ℕ := 120*M+120

def Inv (μ : ℕ → ℤ) (key : ℕ → ℕ) (hist offsets cursor M N j : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ → ℤ, σ = ⟨frame [hist,offsets,cursor,M,N,j,offset key N j],ν⟩ ∧
    (∀ r < j, ν (offsets+r) = (offset key N r : ℤ) ∧
      ν (cursor+r) = (offset key N r : ℤ)) ∧
    SameOutside μ ν offsets (cursor+M-offsets)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain : ℕ} (hmain : P[pMain]? = some body)
    {μ : ℕ → ℤ} {hist offsets cursor M N : ℕ} (key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hN : (N : ℤ) ≤ lim.word)
    (hhist : hist+M ≤ offsets) (hoffsets : offsets+M+1 ≤ cursor)
    (hspace : cursor+M ≤ lim.space)
    (hkey : ∀ i < N, key i < M)
    (hread : ∀ r < M, μ (hist+r) = (count key r N : ℤ)) :
    Meets lim P pMain d [hist,offsets,cursor,M,N] μ (time M)
      (fun _ ν => (∀ r ≤ M, ν (offsets+r) = (offset key N r : ℤ)) ∧
        (∀ r < M, ν (cursor+r) = (offset key N r : ℤ)) ∧
        SameOutside μ ν offsets (cursor+M-offsets)) := by
  have hval : (offset key N M : ℤ) ≤ lim.word := by
    rw [offset_total hkey]
    exact hN
  apply Meets.of_body hmain
  unfold body time
  light_set 0
  refine Ends.pieceThen (Ends.for (Inv μ key hist offsets cursor M N) M 100
    ?start ?round ?done ?bound (Q := Inv μ key hist offsets cursor M N M)
    (T := 120*M+10) (hT := by light_time)) ?finish
  case start =>
    refine ⟨μ,?_,?_,SameOutside.refl⟩
    · simp [update_frame_setLocal]
    · intro r hr; omega
  case round =>
    rintro i _ hi _ ⟨ν,rfl,written,kept⟩
    have hread' : ν (hist+i) = (count key i N : ℤ) :=
      (kept _ (Or.inl (by omega))).trans (hread i hi)
    have ho := offset_le hkey (show i ≤ M by omega)
    have hn := offset_le hkey (show i+1 ≤ M by omega)
    have hoWord := (Int.ofNat_le.mpr ho).trans hN
    have hnWord := (Int.ofNat_le.mpr hn).trans hN
    have hcWord := (Int.ofNat_le.mpr (count_le key i N)).trans hN
    have hsum : (offset key N i : ℤ)+(count key i N : ℤ) = (offset key N (i+1) : ℤ) := by
      rw [offset_succ,Nat.cast_add]
    light_store (offsets+i) (offset key N i : ℕ)
    light_store (cursor+i) (offset key N i : ℕ)
    have hread'' : Function.update (Function.update ν (offsets+i) (offset key N i : ℤ))
        (cursor+i) (offset key N i : ℤ) (hist+i) = (count key i N : ℤ) := by
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),hread']
    light_set (offset key N (i+1) : ℕ) using hread'',hsum
    refine ⟨by simp,Function.update (Function.update ν (offsets+i) (offset key N i : ℤ))
      (cursor+i) (offset key N i : ℤ),by simp [update_frame_setLocal],?_,?_⟩
    · intro r hr
      rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
      · constructor
        · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
          exact (written r hr).1
        · rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
          exact (written r hr).2
      · constructor
        · rw [Function.update_of_ne (by omega),Function.update_self]
        · exact Function.update_self ..
    · intro a ha
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    intro σ _ hs
    exact hs
  case bound =>
    rintro i _ hi _ ⟨ν,rfl,_,_⟩
    simp
  case finish =>
    rintro _ ⟨ν,rfl,written,kept⟩
    light_store (offsets+M) (offset key N M : ℕ)
    dsimp only
    refine ⟨?_,?_,?_⟩
    · intro r hr
      rcases lt_or_eq_of_le hr with hr | rfl
      · rw [Function.update_of_ne (by omega)]
        exact (written r hr).1
      · exact Function.update_self ..
    · intro r hr
      rw [Function.update_of_ne (by omega)]
      exact (written r hr).2
    · intro a ha
      rw [Function.update_of_ne (by omega)]
      exact kept a ha

def program : Program := [body]

end ThreeSum.LightSourceBucketOffsets
