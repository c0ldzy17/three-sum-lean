import Submission.ThreeSum.LightReportingGather

/-! # Actual aligned gathering of both selected reporting-prefix mask arrays -/

namespace ThreeSum.LightReportingGatherPair

open Light

variable {lim : Limits}

def body (pGather : ℕ) : Stmt :=
  .call pGather [v 0,v 1,v 5,v 3,v 4] 7 ;;
  .call pGather [v 0,v 2,v 6,v 3,v 4] 0

def program : Program := LightReportingGather.program ++ [body 0]
def time (t : ℕ) : ℕ := 2*LightReportingGather.time t+60

theorem program_meets {μ : ℕ → ℤ} {indices srcL srcR dstL dstR t n d : ℕ}
    (index : ℕ → ℕ) (left right : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hindices : indices+t ≤ lim.space) (hsrcL : srcL+n ≤ lim.space) (hsrcR : srcR+n ≤ lim.space)
    (hdstL : dstL+t ≤ lim.space) (hdstR : dstR+t ≤ lim.space)
    (hsepIL : Apart indices t dstL t) (hsepIR : Apart indices t dstR t)
    (hsepLL : Apart srcL n dstL t) (hsepRL : Apart srcR n dstL t)
    (hsepRR : Apart srcR n dstR t) (hsepOut : Apart dstL t dstR t)
    (hindex : ∀ i < t, index i < n)
    (hreadI : ∀ i < t, μ (indices+i) = (index i : ℤ))
    (hreadL : ∀ i < n, μ (srcL+i) = left i) (hreadR : ∀ i < n, μ (srcR+i) = right i)
    (hwordL : ∀ i < n, |left i| ≤ lim.word) (hwordR : ∀ i < n, |right i| ≤ lim.word)
    (hd : d < lim.depth) :
    Meets lim program 1 d [indices,srcL,srcR,t,n,dstL,dstR] μ (time t)
      (fun _ ν => Seg ν dstL (List.ofFn fun i : Fin t => left (index i.val)) ∧
        Seg ν dstR (List.ofFn fun i : Fin t => right (index i.val)) ∧
        SameOutside2 μ ν dstL t dstR t) := by
  apply Meets.of_body (p := 1) (by rfl : program[1]? = some (body 0))
  unfold body time
  have hl := (LightReportingGather.program_meets (d := d+1) (μ := μ)
    index left hw hindices hsrcL hdstL hsepIL hsepLL hindex hreadI hreadL hwordL).append [body 0]
  light_call hl using LightReportingGather.time with ret μ₁ ⟨hleft,hkeepL⟩
  have hiRead (i : ℕ) (hi : i < t) : μ₁ (indices+i) = (index i : ℤ) :=
    (hkeepL _ (by rcases hsepIL with h | h <;> omega)).trans (hreadI i hi)
  have hrRead (i : ℕ) (hi : i < n) : μ₁ (srcR+i) = right i :=
    (hkeepL _ (by rcases hsepRL with h | h <;> omega)).trans (hreadR i hi)
  have hr := (LightReportingGather.program_meets (d := d+1) (μ := μ₁)
    index right hw hindices hsrcR hdstR hsepIR hsepRR hindex hiRead hrRead hwordR).append [body 0]
  light_call hr using LightReportingGather.time with ret₂ μ₂ ⟨hright,hkeepR⟩
  refine ⟨hleft.of_sameOutside hkeepR (by simpa only [List.length_ofFn] using hsepOut),hright,?_⟩
  intro i hi
  exact (hkeepR i hi.2).trans (hkeepL i hi.1)

theorem time_bound (t : ℕ) : time t ≤ 80*t+80 := by
  unfold time LightReportingGather.time
  omega

end ThreeSum.LightReportingGatherPair
