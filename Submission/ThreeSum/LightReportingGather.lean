import Submission.ThreeSum.LightReportingFilter

/-!
# Actual indexed gathering of selected reporting masks

The index array and source array can lie on either side of the destination.
This supports reusable high-address child scratch and low-address frontier
storage without scanning discarded children or overwriting retained input.
-/

namespace ThreeSum.LightReportingGather

open Light

variable {lim : Limits} {P : Program}

def body : Stmt := pass 5 (v 3) (v 2) (M (v 1 +' M (v 0 +' v 5)))
def program : Program := [body]
def time (t : ℕ) : ℕ := 40*t+10

theorem meets {μ : ℕ → ℤ} {p indices src dst t n d : ℕ}
    (hp : P[p]? = some body) (index : ℕ → ℕ) (value : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrc : src+n ≤ lim.space) (hdst : dst+t ≤ lim.space)
    (hsepI : Apart indices t dst t) (hsepS : Apart src n dst t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadS : ∀ i < n, μ (src+i) = value i)
    (hword : ∀ i < n, |value i| ≤ lim.word) :
    Meets lim P p d [indices,src,dst,t,n] μ (time t)
      (fun _ ν => (∀ i < t, ν (dst+i) = value (index i)) ∧ SameOutside μ ν dst t) := by
  refine .of_body hp (Ends.pass (fun i => value (index i))
    (fun i hi => ?_) ⟨fun i hi => wrote_done (f := fun i => value (index i)) hi,by light_keep⟩
    hw hdst rfl rfl (hT := by light_time [time]))
  have hidx := hindex i hi
  have hreadIdx : wrote μ dst (fun i => value (index i)) i (indices+i) = (index i : ℤ) :=
    (wrote_rest (by rcases hsepI with h | h <;> omega)).trans (hreadI i hi)
  have hreadVal : wrote μ dst (fun i => value (index i)) i (src+index i) = value (index i) :=
    (wrote_rest (by rcases hsepS with h | h <;> omega)).trans (hreadS _ hidx)
  have hv := abs_le.mp (hword _ hidx)
  light_side [hreadIdx,hreadVal]

theorem program_meets {μ : ℕ → ℤ} {indices src dst t n d : ℕ}
    (index : ℕ → ℕ) (value : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrc : src+n ≤ lim.space) (hdst : dst+t ≤ lim.space)
    (hsepI : Apart indices t dst t) (hsepS : Apart src n dst t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadS : ∀ i < n, μ (src+i) = value i)
    (hword : ∀ i < n, |value i| ≤ lim.word) :
    Meets lim program 0 d [indices,src,dst,t,n] μ (time t)
      (fun _ ν => Seg ν dst (List.ofFn fun i : Fin t => value (index i.val)) ∧
        SameOutside μ ν dst t) := by
  apply (meets rfl index value hw hindices hsrc hdst hsepI hsepS hindex hreadI hreadS hword).mono le_rfl
  rintro r ν ⟨hout,hkeep⟩
  refine ⟨?_,hkeep⟩
  intro i hi
  have hi' : i < t := by simpa only [List.length_ofFn] using hi
  simpa only [List.getElem_ofFn] using hout i hi'

end ThreeSum.LightReportingGather
