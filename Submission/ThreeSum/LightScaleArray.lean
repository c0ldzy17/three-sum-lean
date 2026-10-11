import Submission.ThreeSum.LightArray

/-! # A costed array scaling pass -/

namespace ThreeSum.LightScaleArray

open Light ThreeSum.LightArray

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt := pass 4 (v 2) (v 1) (v 3 *' M (v 0 +' v 4))

def time (n : ℕ) : ℕ := 18*n+6

theorem meets {p src dst n : ℕ} {c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hword : ∀ i < n, |c*μ (src+i)| ≤ lim.word) :
    Meets lim P p d [src,dst,n,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = c*μ (src+i)) ∧ SameOutside μ μ' dst n) := by
  refine .of_body hp (Ends.pass (fun i => c*μ (src+i))
    (fun i hi => ?_) ⟨fun i hi => wrote_done (f := fun i => c*μ (src+i)) hi,
      by light_keep⟩ hw hdst rfl rfl (hT := by light_time [time]))
  have hr := source_read (μ := μ) (f := fun i => c*μ (src+i)) hsep hi
  have hv := abs_le.mp (hword i hi)
  light_side [hr]

def program : Program := [body]

theorem program_meets {src dst n : ℕ} {c : ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hword : ∀ i < n, |c*μ (src+i)| ≤ lim.word) :
    Meets lim program 0 d [src,dst,n,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = c*μ (src+i)) ∧ SameOutside μ μ' dst n) :=
  meets rfl hw hsrc hdst hsep hword

end ThreeSum.LightScaleArray
