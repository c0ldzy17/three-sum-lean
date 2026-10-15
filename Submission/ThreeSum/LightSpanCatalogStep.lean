import Submission.ThreeSum.LightSpanAxpy

/-! Actual coefficient-by-old-row expansion of a span catalog, without coefficient-code division. -/
namespace ThreeSum.LightSpanCatalogBlock
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

def roundBody (pAxpy : ℕ) : Stmt :=
  .call pAxpy [v 0 +' v 4 *' v 7,v 2,v 3 +' v 4 *' v 7,v 4,v 5,v 6] 8

def body (pAxpy : ℕ) : Stmt := .for 7 (v 1) (roundBody pAxpy)
def time (J p n : ℕ) : ℕ := n*(LightSpanAxpy.time J p+150)+20

def Inv (μ : ℕ → ℤ) (src n rowBase dst J a p : ℕ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (k : ℕ) (σ : State) : Prop := ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,n,rowBase,dst,J,a,p,k,result],ν⟩ ∧ SameOutside μ ν dst (J*n) ∧
      ∀ t<k, ∀ i<J, ν (dst+J*t+i)=LightSpanAxpy.values (f t) row a p i

variable {lim : Limits} {P : Program}

theorem meets {pMain pAxpy pMulAdd pDivide src n rowBase dst J a p d : ℕ}
    (hmain : P[pMain]?=some (body pAxpy))
    (haxpy : P[pAxpy]?=some (LightSpanAxpy.body pMulAdd))
    (hmul : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+J*n≤dst) (hrow : rowBase+J≤dst)
    (hdst : dst+J*n≤lim.space) (hp : 0<p) (ha : a<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, f k i<p) (hr : ∀ i<J, row i<p)
    (hread : ∀ k<n, ∀ i<J, μ (src+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀ i<J, μ (rowBase+i)=(row i : ℤ))
    (hd : d+3≤lim.depth) :
    Meets lim P pMain d [src,n,rowBase,dst,J,a,p] μ (time J p n)
      (fun _ ν => (∀ k<n, ∀ i<J, ν (dst+J*k+i)=LightSpanAxpy.values (f k) row a p i) ∧ SameOutside μ ν dst (J*n)) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ src n rowBase dst J a p f row) n (LightSpanAxpy.time J p+120)
    ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(src : ℤ),n,rowBase,dst,J,a,p,0]=frame ([(src : ℤ),n,rowBase,dst,J,a,p,0]++[0])
      exact (frame_append_zeros _ 1).symm
    · intro t ht; omega
  case round =>
    rintro k _ hk _ ⟨result,ν,rfl,H,hrdone⟩
    have hkn : J*k+J≤J*n := by
      have hh := Nat.mul_le_mul_left J (show k+1≤n by omega)
      simpa only [Nat.mul_add,Nat.mul_one] using hh
    have hRead : ∀ i<J, ν (src+J*k+i)=(f k i : ℤ) := by
      intro i hi; rw [H _ (Or.inl (by omega)),hread k hk i hi]
    have hRowRead : ∀ i<J, ν (rowBase+i)=(row i : ℤ) := by
      intro i hi; rw [H _ (Or.inl (by omega)),hreadRow i hi]
    have hc := LightSpanAxpy.meets (d := d+1) (src := src+J*k) (rowBase := rowBase) (dst := dst+J*k) (J := J) haxpy hmul hdivide ν (f k) row hw
      (by omega) (by omega) (by omega) hp ha hword (hf k hk) hr hRead hRowRead (by omega)
    unfold roundBody
    light_call hc using LightSpanAxpy.time
      with out ξ ⟨hNew,hOutside⟩
    refine ⟨by simp,out,ξ,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro x hx
      rw [hOutside x (by rcases hx with hx | hx <;> omega),H x hx]
    · intro t ht i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp ht with ht | he
      · have htk : J*t+J≤J*k := by
          have hh := Nat.mul_le_mul_left J (show t+1≤k by omega)
          simpa only [Nat.mul_add,Nat.mul_one] using hh
        rw [hOutside _ (Or.inl (by omega))]
        exact hrdone t ht i hi
      · subst t
        exact hNew i hi
  case done =>
    rintro _ _ ⟨result,ν,rfl,H,hdone⟩
    exact ⟨hdone,H⟩
  case bound =>
    rintro k _ hk _ ⟨result,ν,rfl,H,hdone⟩
    light_side

end ThreeSum.LightSpanCatalogBlock

namespace ThreeSum.LightSpanCatalogStep
open Light
set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

def roundBody (pBlock : ℕ) : Stmt :=
  .call pBlock [v 0,v 1,v 2,v 3 +' v 4 *' v 1 *' v 6,v 4,v 6,v 5] 7

def body (pBlock : ℕ) : Stmt := .for 6 (v 5) (roundBody pBlock)
def time (J p n : ℕ) : ℕ := p*(LightSpanCatalogBlock.time J p n+150)+20

def Inv (μ : ℕ → ℤ) (src n rowBase dst J p : ℕ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (a : ℕ) (σ : State) : Prop := ∃ result : ℤ, ∃ ν : ℕ → ℤ,
    σ=⟨frame [src,n,rowBase,dst,J,p,a,result],ν⟩ ∧ SameOutside μ ν dst (J*n*p) ∧
      ∀ u<a, ∀ k<n, ∀ i<J, ν (dst+J*n*u+J*k+i)=LightSpanAxpy.values (f k) row u p i

variable {lim : Limits} {P : Program}

theorem meets {pMain pBlock pAxpy pMulAdd pDivide src n rowBase dst J p d : ℕ}
    (hmain : P[pMain]?=some (body pBlock))
    (hblock : P[pBlock]?=some (LightSpanCatalogBlock.body pAxpy))
    (haxpy : P[pAxpy]?=some (LightSpanAxpy.body pMulAdd))
    (hmul : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+J*n≤dst) (hrow : rowBase+J≤dst)
    (hdst : dst+J*n*p≤lim.space) (hp : 0<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word)
    (hf : ∀ k<n, ∀ i<J, f k i<p) (hr : ∀ i<J, row i<p)
    (hread : ∀ k<n, ∀ i<J, μ (src+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀ i<J, μ (rowBase+i)=(row i : ℤ))
    (hd : d+4≤lim.depth) :
    Meets lim P pMain d [src,n,rowBase,dst,J,p] μ (time J p n)
      (fun _ ν => (∀ u<p, ∀ k<n, ∀ i<J, ν (dst+J*n*u+J*k+i)=LightSpanAxpy.values (f k) row u p i) ∧
        SameOutside μ ν dst (J*n*p)) := by
  have hpp : (p : ℤ)≤lim.word := by
    have hh : p≤LightPrimeCoefficient.word p := by unfold LightPrimeCoefficient.word; nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ src n rowBase dst J p f row) p (LightSpanCatalogBlock.time J p n+120)
    ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,μ,?_,SameOn.refl,?_⟩
    · simp [update_frame_setLocal]
      change frame [(src : ℤ),n,rowBase,dst,J,p,0]=frame ([(src : ℤ),n,rowBase,dst,J,p,0]++[0])
      exact (frame_append_zeros _ 1).symm
    · intro u hu; omega
  case round =>
    rintro a _ ha _ ⟨result,ν,rfl,H,hdone⟩
    have hap : J*n*a+J*n≤J*n*p := by
      have hh := Nat.mul_le_mul_left (J*n) (show a+1≤p by omega)
      simpa only [Nat.mul_add,Nat.mul_one] using hh
    have hRead : ∀ k<n, ∀ i<J, ν (src+J*k+i)=(f k i : ℤ) := by
      intro k hk i hi
      have hkn : J*k+J≤J*n := by
        have hh := Nat.mul_le_mul_left J (show k+1≤n by omega)
        simpa only [Nat.mul_add,Nat.mul_one] using hh
      rw [H _ (Or.inl (by omega)),hread k hk i hi]
    have hRowRead : ∀ i<J, ν (rowBase+i)=(row i : ℤ) := by
      intro i hi; rw [H _ (Or.inl (by omega)),hreadRow i hi]
    have hc := LightSpanCatalogBlock.meets (d := d+1) (dst := dst+J*n*a) hblock haxpy hmul hdivide
      ν f row hw (by omega) (by omega) (by omega) hp ha hword hcontrols hf hr hRead hRowRead (by omega)
    have hproductWord : (J : ℤ)*(n : ℤ)*(a : ℤ)≤lim.word := by
      have hh : J*n*a≤lim.space := by omega
      exact (by exact_mod_cast hh : (J : ℤ)*(n : ℤ)*(a : ℤ)≤(lim.space : ℤ)).trans hw
    have hdestProductWord : (dst : ℤ)+(J : ℤ)*(n : ℤ)*(a : ℤ)≤lim.word := by
      have hh : dst+J*n*a≤lim.space := by omega
      exact (by exact_mod_cast hh : (dst : ℤ)+(J : ℤ)*(n : ℤ)*(a : ℤ)≤(lim.space : ℤ)).trans hw
    have hproductNonneg : 0≤(J : ℤ)*(n : ℤ)*(a : ℤ) := by positivity
    unfold roundBody
    light_call hc using LightSpanCatalogBlock.time
      with out ξ ⟨hNew,hOutside⟩
    refine ⟨by simp,out,ξ,?_,?_,?_⟩
    · simp [update_frame_setLocal]
    · intro x hx
      rw [hOutside x (by rcases hx with hx | hx <;> omega),H x hx]
    · intro u hu k hk i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hu with hu | he
      · have hua : J*n*u+J*n≤J*n*a := by
          have hh := Nat.mul_le_mul_left (J*n) (show u+1≤a by omega)
          simpa only [Nat.mul_add,Nat.mul_one] using hh
        have hkn : J*k+J≤J*n := by
          have hh := Nat.mul_le_mul_left J (show k+1≤n by omega)
          simpa only [Nat.mul_add,Nat.mul_one] using hh
        rw [hOutside _ (Or.inl (by omega))]
        exact hdone u hu k hk i hi
      · subst u
        exact hNew k hk i hi
  case done =>
    rintro _ _ ⟨result,ν,rfl,H,hdone⟩
    exact ⟨hdone,H⟩
  case bound =>
    rintro a _ ha _ ⟨result,ν,rfl,H,hdone⟩
    light_side

theorem time_bound (J p n : ℕ) :
    time J p n≤(p+1)*(n+1)*(J+1)*(LightPrimeCoefficient.mulAddTime p+500) := by
  let M := LightPrimeCoefficient.mulAddTime p
  let X := (J+1)*(M+500)
  have hinner : J*(M+150)+170≤X := by dsimp [X]; nlinarith
  have hx : 170≤X := by dsimp [X]; nlinarith
  have hb : n*(J*(M+150)+170)+170≤(n+1)*X := by
    calc
      _≤n*X+X := Nat.add_le_add (Nat.mul_le_mul_left n hinner) hx
      _=(n+1)*X := by ring
  have hy : 20≤(n+1)*X := by
    have hh := Nat.mul_le_mul_right X (show 1≤n+1 by omega)
    omega
  unfold time LightSpanCatalogBlock.time LightSpanAxpy.time
  change p*(n*(J*(M+150)+170)+170)+20≤(p+1)*(n+1)*(J+1)*(M+500)
  calc
    _≤p*((n+1)*X)+(n+1)*X := Nat.add_le_add (Nat.mul_le_mul_left p hb) hy
    _=_ := by dsimp [X]; ring

def program : Program := [body 1,LightSpanCatalogBlock.body 2,LightSpanAxpy.body 3,
  LightPrimeCoefficient.mulAddBody 4,LightSmallDivide.body]

end ThreeSum.LightSpanCatalogStep
