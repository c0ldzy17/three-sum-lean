import Submission.ThreeSum.TernarySignedLayout
import Submission.ThreeSum.LightTernaryProductChannel

/-! Logical original digit/tag channel coordinates become actual row offsets. -/
namespace ThreeSum.LightTernaryTaggedChannel
open Light TernarySignedLayout

def offsetBody : Stmt := .ite (v 0 <' v 1)
  (.set 0 (v 1 -' k 1 -' v 0)) (.set 0 (v 0))

variable {lim : Limits} {P : Program} {d : ℕ}

theorem offset_meets {p J i : ℕ} (hmain : P[p]?=some offsetBody) (μ : ℕ→ℤ)
    (hi : i<J+2) (hword : ((J+3 : ℕ) : ℤ)≤lim.word) :
    Meets lim P p d [i,J] μ 20
      (fun r ν => r=(offset J i : ℤ) ∧ ν=μ) := by
  apply Meets.of_body hmain
  unfold offsetBody
  light_if hlt hge : (i : ℤ)<(J : ℤ)
  · have h : i<J := by exact_mod_cast hlt
    have he : (J : ℤ)-1-(i : ℤ)=((J-1-i : ℕ) : ℤ) := by omega
    light_set (J-1-i : ℕ) using he
    exact ⟨by simp [offset,h],rfl⟩
  · have h : ¬i<J := by exact_mod_cast hge
    light_set (i : ℕ)
    exact ⟨by simp [offset,h],rfl⟩

def body (pOffset pProduct : ℕ) : Stmt :=
  .call pOffset [v 3,v 2] 6 ;;
  .call pOffset [v 4,v 2] 7 ;;
  .call pProduct [v 0,v 1,v 2 +' k 2,v 6,v 7,v 5] 0

def time (n : ℕ) : ℕ := LightTernaryProductChannel.time n+120

theorem meets {pMain pOffset pProduct src n J a b dst U : ℕ}
    (hmain : P[pMain]?=some (body pOffset pProduct))
    (hoffset : P[pOffset]?=some offsetBody)
    (hproduct : P[pProduct]?=some LightTernaryProductChannel.body)
    (μ : ℕ→ℤ) (F : ℕ→ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (ha : a<J+2) (hb : b<J+2)
    (hsrc : src+n*(J+2)≤dst) (hdst : dst+n≤lim.space)
    (hread : ∀ i<n, ∀ j<J+2, μ (src+i*(J+2)+offset J j)=F i j)
    (hf : ∀ i<n, ∀ j<J+2, |F i j|≤(U : ℤ))
    (hword : ((U : ℤ)+1)^2≤lim.word)
    (hindex : ((J+3 : ℕ) : ℤ)≤lim.word) :
    Meets lim P pMain d [src,n,J,a,b,dst] μ (time n)
      (fun _ ν => (∀ i<n, ν (dst+i)=F i a*F i b) ∧ SameOutside μ ν dst n) := by
  let G : ℕ→ℕ→ℤ := fun i j => F i (offset J j)
  have hr : ∀ i<n, ∀ j<J+2, μ (src+i*(J+2)+j)=G i j := by
    intro i hi j hj
    have hh := hread i hi (offset J j) (offset_lt hj)
    rwa [offset_involutive hj] at hh
  have hg : ∀ i<n, ∀ j<J+2, |G i j|≤(U : ℤ) := by
    intro i hi j hj
    exact hf i hi (offset J j) (offset_lt hj)
  apply Meets.of_body hmain
  unfold body time
  light_call (offset_meets (d := d+1) hoffset μ ha hindex)
    using LightTernaryProductChannel.time with ra ν ⟨hra,hma⟩
  subst ν
  light_call (offset_meets (d := d+1) hoffset μ hb hindex)
    using LightTernaryProductChannel.time with rb ν ⟨hrb,hmb⟩
  subst ν
  light_call (LightTernaryProductChannel.meets (d := d+1) (a := offset J a) (b := offset J b)
    (width := J+2) hproduct μ G hw (offset_lt ha) (offset_lt hb) hsrc hdst hr hg hword)
    using hra,hrb,LightTernaryProductChannel.time with r ξ ⟨hweights,hkeep⟩
  refine ⟨?_,hkeep⟩
  intro i hi
  have hh := hweights i hi
  simpa only [G,offset_involutive ha,offset_involutive hb] using hh

def program : Program := [body 1 2,offsetBody,LightTernaryProductChannel.body]

end ThreeSum.LightTernaryTaggedChannel
