import Submission.ThreeSum.LightArray

namespace ThreeSum.LightTernaryTensorScatter
open Light
set_option maxHeartbeats 1800000

theorem address_injective {W a b q r : ℕ} (hq : q<W) (hr : r<W)
    (h : a*W+q=b*W+r) : a=b ∧ q=r := by
  have hw : 0<W := by omega
  have ha : a*W+q<(a+1)*W := by nlinarith
  have hb : b*W+r<(b+1)*W := by nlinarith
  have hab : a=b := by
    by_contra hh
    rcases lt_or_gt_of_ne hh with hh | hh
    · have := Nat.mul_le_mul_right W (by omega : a+1≤b)
      omega
    · have := Nat.mul_le_mul_right W (by omega : b+1≤a)
      omega
  exact ⟨hab,by subst b; omega⟩

def body : Stmt := .for 5 (v 2) (.store (v 1 +' v 5 *' v 3 +' v 4) (M (v 0 +' v 5)))
def time (n : ℕ) : ℕ := 60*n+6

def Inv (μ : ℕ→ℤ) (src dst n W q i : ℕ) (σ : State) : Prop :=
  ∃ ν : ℕ→ℤ, σ=⟨frame [src,dst,n,W,q,i],ν⟩ ∧
    (∀ j<i, ν (dst+j*W+q)=μ (src+j)) ∧
    (∀ x, (∀ j<i, x≠dst+j*W+q)→ν x=μ x)

theorem meets {lim : Limits} {P : Program} {p d src dst n W q : ℕ}
    (hmain : P[p]?=some body) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hW : 0<W) (hq : q<W)
    (hsrc : src+n≤lim.space) (hdst : dst+n*W≤lim.space)
    (hsep : Apart src n dst (n*W))
    (hWWord : (W : ℤ)≤lim.word) (hnWord : (n : ℤ)≤lim.word) :
    Meets lim P p d [src,dst,n,W,q] μ (time n)
      (fun _ ν => (∀ j<n, ν (dst+j*W+q)=μ (src+j)) ∧
        (∀ x, (∀ j<n, x≠dst+j*W+q)→ν x=μ x)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ src dst n W q) n 52 ?_ ?_ ?_ ?_
  · refine ⟨μ,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro j hj; omega
    · intro x hx; rfl
  · rintro i _ hi _ ⟨ν,rfl,hwrite,hkeep⟩
    have hiW : i*W+q<n*W := by
      have := Nat.mul_le_mul_right W (by omega : i+1≤n)
      nlinarith
    have hread : ν (src+i)=μ (src+i) := by
      apply hkeep
      intro j hj
      have hjW : j*W+q<n*W := by
        have := Nat.mul_le_mul_right W (by omega : j+1≤n)
        nlinarith
      omega
    have hprodNonneg : 0≤(i : ℤ)*W := by positivity
    have hprodWord : (i : ℤ)*W≤lim.word := by
      have hh : i*W≤lim.space := by omega
      exact (by exact_mod_cast hh : (i : ℤ)*W≤lim.space).trans hw
    light_store (dst+i*W+q) (μ (src+i)) using hread
    refine ⟨by simp,Function.update ν (dst+i*W+q) (μ (src+i)),by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne]
        · exact hwrite j hj
        · intro he
          have := (address_injective hq hq (by omega : j*W+q=i*W+q)).1
          omega
      · simp
    · intro x hx
      rw [Function.update_of_ne (hx i (by omega))]
      exact hkeep x (by intro j hj; exact hx j (by omega))
  · rintro σ hcounter ⟨ν,rfl,hwrite,hkeep⟩
    exact ⟨hwrite,hkeep⟩
  · rintro i _ hi _ ⟨ν,rfl,hwrite,hkeep⟩
    light_side

def program : Program := [body]
end ThreeSum.LightTernaryTensorScatter
