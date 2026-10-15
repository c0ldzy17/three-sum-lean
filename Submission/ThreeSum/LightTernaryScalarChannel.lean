import Submission.ThreeSum.TernaryWeightChannels
import Submission.ThreeSum.LightArray

/-! Fixed signed polynomial weights are initialized from original source cells. -/
namespace ThreeSum.LightTernaryScalarChannel
open Light LightFixedArithmetic TernaryWeightChannels

def atoms : ℕ→Expr := fun _ => M (v 0 +' v 3)
def body (e : Circuit) : Stmt := pass 3 (v 1) (v 2) (e.compile atoms)
def time (e : Circuit) (n : ℕ) : ℕ := n*((e.compile atoms).cost+12)+6

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets (e : Circuit) {p src n dst U : ℕ}
    (hmain : P[p]?=some (body e)) (μ : ℕ→ℤ) (f : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=f i) (hf : ∀ i<n, |f i|≤(U : ℤ))
    (hword : max (U : ℤ) (e.bound U)≤lim.word) :
    Meets lim P p d [src,n,dst] μ (time e n)
      (fun _ ν => (∀ i<n, ν (dst+i)=e.eval (fun _ => f i)) ∧ SameOutside μ ν dst n) := by
  have hU : (U : ℤ)≤lim.word := (le_max_left _ _).trans hword
  have he : e.bound U≤lim.word := (le_max_right _ _).trans hword
  apply Meets.of_body hmain
  unfold body time
  refine Ends.pass (fun i => e.eval (fun _ => f i)) ?round
    ⟨fun i hi => by dsimp only; exact wrote_done hi,by light_keep⟩ hw hdst rfl rfl
  case round =>
    intro j hj
    let σ : State := ⟨Function.update (frame [src,n,dst]) 3 (j : ℤ),
      wrote μ dst (fun i => e.eval (fun _ => f i)) j⟩
    have hr := LightArray.source_read (μ := μ) (f := fun i => e.eval (fun _ => f i)) hsep hj
    have hv := hread j hj
    have hf' := abs_le.mp (hf j hj)
    have hsa : ∀ i, (atoms i).Safe lim σ := by
      intro i
      dsimp [σ,atoms]
      light_side [hr,hv]
    have hva : ∀ i, (atoms i).val σ=f j := by
      intro i
      dsimp [σ,atoms]
      light_side [hr,hv]
    have hbounds : ∀ i, |(atoms i).val σ|≤(U : ℤ) := by intro i; rw [hva]; exact hf j hj
    refine ⟨Circuit.compile_safe e atoms σ (Int.natCast_nonneg U) hsa hbounds he,?_⟩
    rw [Circuit.compile_val]
    apply congrArg (fun x : ℕ→ℤ => e.eval x)
    funext i
    exact hva i

theorem fixed_polynomial_word_bound (e : Circuit) (U : ℕ) :
    max (U : ℤ) (e.bound U)≤(e.coefficient+1)*((U : ℤ)+1)^(e.degree+1) := by
  have hU : (0 : ℤ)≤U := by positivity
  have hb : (1 : ℤ)≤U+1 := by omega
  have hc := e.coefficient_pos
  have hp : ((U : ℤ)+1)^e.degree≤((U : ℤ)+1)^(e.degree+1) :=
    pow_le_pow_right₀ hb (by omega)
  have hp1 : (U : ℤ)+1≤((U : ℤ)+1)^(e.degree+1) := by
    simpa using (pow_le_pow_right₀ hb (show 1≤e.degree+1 by omega))
  have hpow0 : (0 : ℤ)≤((U : ℤ)+1)^(e.degree+1) := by positivity
  apply max_le
  · nlinarith
  · exact (e.bound_polynomial hU).trans
      ((mul_le_mul_of_nonneg_left hp (by omega)).trans (by nlinarith))

theorem power_meets {k p src n dst U : ℕ}
    (hmain : P[p]?=some (body (scalarPower k))) (μ : ℕ→ℤ) (f : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hsrc : src+n≤lim.space) (hdst : dst+n≤lim.space)
    (hsep : LightArray.SourceSafe src dst n)
    (hread : ∀ i<n, μ (src+i)=f i) (hf : ∀ i<n, |f i|≤(U : ℤ))
    (hword : max (U : ℤ) ((scalarPower k).bound U)≤lim.word) :
    Meets lim P p d [src,n,dst] μ (time (scalarPower k) n)
      (fun _ ν => (∀ i<n, ν (dst+i)=(f i)^k) ∧ SameOutside μ ν dst n) := by
  simpa only [scalarPower_eval] using meets (scalarPower k) hmain μ f hw hsrc hdst hsep hread hf hword

def program (e : Circuit) : Program := [body e]

end ThreeSum.LightTernaryScalarChannel
