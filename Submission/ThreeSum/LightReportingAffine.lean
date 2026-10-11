import Submission.ThreeSum.LightArray

/-! # Costed affine scans used to form reporting child-prefix masks -/

namespace ThreeSum.LightReportingAffine

open Light ThreeSum.LightArray

variable {lim : Limits} {P : Program} {d : ℕ}

def body : Stmt :=
  pass 5 (v 2) (v 1) (v 3 +' v 4 *' M (v 0 +' v 5))

def time (n : ℕ) : ℕ := 23*n+6

theorem meets {p src dst n : ℕ} {b c : ℤ} {μ : ℕ → ℤ}
    (hp : P[p]? = some body)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hmul : ∀ i < n, |c*μ (src+i)| ≤ lim.word)
    (hsum : ∀ i < n, |b+c*μ (src+i)| ≤ lim.word) :
    Meets lim P p d [src,dst,n,b,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = b+c*μ (src+i)) ∧ SameOutside μ μ' dst n) := by
  refine .of_body hp (Ends.pass (fun i => b+c*μ (src+i))
    (fun i hi => ?_) ⟨fun i hi => wrote_done (f := fun i => b+c*μ (src+i)) hi,
      by light_keep⟩ hw hdst rfl rfl (hT := by light_time [time]))
  have hr := source_read (μ := μ) (f := fun i => b+c*μ (src+i)) hsep hi
  have hm := abs_le.mp (hmul i hi)
  have hs := abs_le.mp (hsum i hi)
  light_side [hr]

def program : Program := [body]

theorem program_meets {src dst n : ℕ} {b c : ℤ} {μ : ℕ → ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hsrc : src+n ≤ lim.space) (hdst : dst+n ≤ lim.space)
    (hsep : SourceSafe src dst n)
    (hmul : ∀ i < n, |c*μ (src+i)| ≤ lim.word)
    (hsum : ∀ i < n, |b+c*μ (src+i)| ≤ lim.word) :
    Meets lim program 0 d [src,dst,n,b,c] μ (time n)
      (fun _ μ' => (∀ i < n, μ' (dst+i) = b+c*μ (src+i)) ∧ SameOutside μ μ' dst n) :=
  meets rfl hw hsrc hdst hsep hmul hsum

end ThreeSum.LightReportingAffine
