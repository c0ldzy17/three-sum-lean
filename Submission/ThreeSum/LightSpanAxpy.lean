import Submission.ThreeSum.LightPrimeCoefficient
import Submission.ThreeSum.LightTernaryPass

/-! Actual vector axpy over stored prime-field representatives. -/
namespace ThreeSum.LightSpanAxpy
open Light
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

def roundBody (pMulAdd : ℕ) : Stmt :=
  .set 7 (M (v 0 +' v 6)) ;;
  .set 8 (M (v 1 +' v 6)) ;;
  .call pMulAdd [v 7,v 4,v 8,v 5] 9 ;;
  .store (v 2 +' v 6) (v 9)

def body (pMulAdd : ℕ) : Stmt := .for 6 (v 3) (roundBody pMulAdd)
def time (J p : ℕ) : ℕ := J*(LightPrimeCoefficient.mulAddTime p+150)+20

def values (f row : ℕ → ℕ) (a p i : ℕ) : ℤ := ((f i+a*row i)%p : ℕ)

def Inv (μ : ℕ → ℤ) (src rowBase dst J a p : ℕ) (f row : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ x y z : ℤ, σ=⟨frame [src,rowBase,dst,J,a,p,j,x,y,z],wrote μ dst (values f row a p) j⟩

variable {lim : Limits} {P : Program}

theorem meets {pMain pMulAdd pDivide src rowBase dst J a p d : ℕ}
    (hmain : P[pMain]?=some (body pMulAdd))
    (hmul : P[pMulAdd]?=some (LightPrimeCoefficient.mulAddBody pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f row : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+J≤dst) (hrow : rowBase+J≤dst)
    (hdst : dst+J≤lim.space) (hp : 0<p) (ha : a<p)
    (hword : (LightPrimeCoefficient.word p : ℤ)≤lim.word)
    (hf : ∀ i<J, f i<p) (hr : ∀ i<J, row i<p)
    (hread : ∀ i<J, μ (src+i)=(f i : ℤ))
    (hreadRow : ∀ i<J, μ (rowBase+i)=(row i : ℤ))
    (hd : d+2≤lim.depth) :
    Meets lim P pMain d [src,rowBase,dst,J,a,p] μ (time J p)
      (fun _ ν => (∀ i<J, ν (dst+i)=values f row a p i) ∧ SameOutside μ ν dst J) := by
  have hsmall (x : ℕ) (hx : x<p) : (x : ℤ)≤lim.word := by
    have hh : x≤LightPrimeCoefficient.word p := by unfold LightPrimeCoefficient.word; nlinarith
    exact (Int.ofNat_le.mpr hh).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ src rowBase dst J a p f row) J (LightPrimeCoefficient.mulAddTime p+120)
    ?start ?round ?done ?bound (hT := by light_time)
  case start =>
    refine ⟨0,0,0,?_⟩
    simp [Inv,update_frame_setLocal,wrote_zero]
    change frame [(src : ℤ),rowBase,dst,J,a,p,0]=
      frame ([(src : ℤ),rowBase,dst,J,a,p,0]++[0,0,0])
    exact (frame_append_zeros _ 3).symm
  case round =>
    rintro i _ hi _ ⟨x,y,z,rfl⟩
    let ν := wrote μ dst (values f row a p) i
    have hRead : ν (src+i)=(f i : ℤ) := by dsimp only [ν]; rw [wrote_rest (Or.inl (by omega)),hread i hi]
    have hRowRead : ν (rowBase+i)=(row i : ℤ) := by dsimp only [ν]; rw [wrote_rest (Or.inl (by omega)),hreadRow i hi]
    have hF := hsmall (f i) (hf i hi)
    have hR := hsmall (row i) (hr i hi)
    have hMod := hsmall ((f i+a*row i)%p) (Nat.mod_lt _ hp)
    have hc := LightPrimeCoefficient.mulAdd_meets (d := d+1) hmul hdivide ν (by omega) hp (hf i hi) ha (hr i hi) hword
    unfold roundBody
    light_set (f i : ℕ) using ν,hRead,LightPrimeCoefficient.mulAddTime
    light_set (row i : ℕ) using ν,hRowRead,LightPrimeCoefficient.mulAddTime
    light_call hc using ν,LightPrimeCoefficient.mulAddTime
      with out ξ ⟨hout,hmem⟩
    subst ξ
    light_store (dst+i) (values f row a p i) using hout,values,LightPrimeCoefficient.mulAddTime
    refine ⟨by simp,(f i : ℤ),(row i : ℤ),out,?_⟩
    simp [Inv,ν,update_frame_setLocal,wrote_succ]
  case done =>
    rintro _ _ ⟨x,y,z,rfl⟩
    exact ⟨fun i hi => wrote_done hi,fun x hx => wrote_rest hx⟩
  case bound =>
    rintro i _ hi _ ⟨x,y,z,rfl⟩
    light_side

end ThreeSum.LightSpanAxpy
