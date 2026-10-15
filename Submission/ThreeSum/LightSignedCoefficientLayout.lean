import Submission.ThreeSum.TernarySignedLayout
import Submission.ThreeSum.LightArray

namespace ThreeSum.LightSignedCoefficientLayout
open Light TernarySignedLayout
set_option maxHeartbeats 2000000

def roundBody : Stmt :=
  .ite (v 3 <' v 2)
    (.store (v 1 +' v 2 -' k 1 -' v 3) (M (v 0 +' v 3)))
    (.store (v 1 +' v 3) (M (v 0 +' v 3)))

def body : Stmt := .for 3 (v 2 +' k 2) roundBody

def time (J : ℕ) : ℕ := 50*(J+2)+10

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc src dst J U : ℕ} (hp : P[proc]?=some body) (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+(J+2)≤dst) (hspace : dst+(J+2)≤lim.space)
    (hread : ∀ i < J+2, μ (src+i)=f i) (hf : ∀ i < J+2, |f i|≤(U : ℤ))
    (hword : (U : ℤ)≤lim.word) :
    Meets lim P proc depth [src,dst,J] μ (time J)
      (fun _ ν => (∀ i < J+2, ν (dst+i)=f (offset J i)) ∧ SameOutside μ ν dst (J+2)) := by
  apply Meets.of_body hp
  unfold body time
  refine Ends.for (fun i σ => σ.loc=frame [src,dst,J,i] ∧
      (∀ j < i, σ.mem (dst+offset J j)=f j) ∧ SameOutside μ σ.mem dst (J+2))
    (J+2) 40 ?start ?round ?done ?bound
  case start => refine ⟨by simp [update_frame_setLocal],?_,SameOutside.refl⟩; intro j hj; omega
  case round =>
    rintro i σ hi _ ⟨hloc,written,kept⟩
    cases σ with
    | mk loc ν =>
      dsimp only at hloc written kept ⊢
      subst loc
      have hr : ν (src+i)=f i := (kept _ (Or.inl (by omega))).trans (hread i hi)
      have hfit := (hf i hi).trans hword
      have ho := offset_lt hi
      have haddrWord : ((dst+offset J i : ℕ) : ℤ)≤lim.word :=
        (Int.ofNat_le.mpr (show dst+offset J i ≤ lim.space by omega)).trans hw
      have hnew : ∀ j < i, j≠i → offset J j≠offset J i := by
        intro j hj hji heq
        have hh := congrArg (offset J) heq
        rw [offset_involutive (by omega),offset_involutive hi] at hh
        exact hji hh
      have finish : ∀ value : ℤ, value=f i →
          (Function.update (frame [src,dst,J,i]) 3 ((i : ℤ)+1)=frame [src,dst,J,i+1] ∧
            (∀ j < i+1, Function.update ν (dst+offset J i) value (dst+offset J j)=f j) ∧
            SameOutside μ (Function.update ν (dst+offset J i) value) dst (J+2)) := by
        intro value hval
        refine ⟨by simp [update_frame_setLocal],?_,kept.update ⟨by omega,by omega⟩ _⟩
        intro j hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · rw [Function.update_of_ne (by have := hnew j hj (by omega); omega),written j hj]
        · simpa [hval]
      unfold roundBody
      refine Ends.iteLast ?_ ?_ (by light_side) (by light_time)
      · intro hd
        have hd' : i < J := by exact_mod_cast (show (i : ℤ)<(J : ℤ) from hd)
        have heq : (dst : ℤ)+(J : ℤ)-1-(i : ℤ)=((dst+offset J i : ℕ) : ℤ) := by simp only [offset,if_pos hd']; omega
        light_store (dst+offset J i) (f i) using heq,hr
        exact ⟨by simp,by simpa using finish _ rfl⟩
      · intro hd
        have hd' : ¬i < J := by exact_mod_cast (show ¬(i : ℤ)<(J : ℤ) from hd)
        have heq : offset J i=i := by simp [offset,hd']
        light_store (dst+i) (f i) using hr
        exact ⟨by simp,by simpa only [heq,Nat.cast_add,Nat.cast_one] using finish (f i) rfl⟩
  case done =>
    rintro σ _ ⟨hloc,written,kept⟩
    refine ⟨?_,kept⟩
    intro i hi
    have hh := written (offset J i) (offset_lt hi)
    rwa [offset_involutive hi] at hh
  case bound =>
    rintro i σ hi _ ⟨hloc,_,_⟩
    cases σ with
    | mk loc ν =>
      dsimp only at hloc ⊢
      subst loc
      light_side

end ThreeSum.LightSignedCoefficientLayout
