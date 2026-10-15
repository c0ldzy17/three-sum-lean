import Submission.ThreeSum.LightTernaryMomentSourceProgram
import Submission.ThreeSum.LightTernaryFixedChannelLoop
import Submission.ThreeSum.TernaryMomentMatrixInvariant

/-! A concrete full channel program, with fresh source/count execution in
each channel and an actual zero-initialized k-major moment matrix. -/
noncomputable section
namespace ThreeSum.LightTernaryMomentDriver
open Light TernaryMomentSchedule
set_option maxHeartbeats 2000000

def library (xl yl zl xr yr zr : List ℤ) : List (ℕ×ℕ)→Program
  | [] => []
  | c::cs => ReportingHostRelocation.program
      (LightTernaryMomentSourceProgram.program xl yl zl xr yr zr c.1 c.2)
      (library xl yl zl xr yr zr cs)

@[simp] theorem library_length (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ)) :
    (library xl yl zl xr yr zr steps).length=127*steps.length := by
  induction steps with
  | nil => simp [library]
  | cons c cs ih =>
    simp only [library,ReportingHostRelocation.program,List.length_append,List.length_map,
      LightTernaryMomentSourceProgram.program_length,ih,List.length_cons]
    omega

def labels (steps : List (ℕ×ℕ)) : List (ℕ×ℕ) :=
  (List.range steps.length).map (fun i => (i,0))

def entry (c : ℕ×ℕ) : ℕ :=127*c.1+126

def body (steps : List (ℕ×ℕ)) (terms arity : ℕ) : Stmt :=
  .call (127*steps.length) [v 6,k terms *' v 7,k 0] arity ;;
  LightTernaryFixedChannelLoop.body (labels steps) entry arity

def program (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ)) (terms arity : ℕ) : Program :=
  library xl yl zl xr yr zr steps++[fillBody,body steps terms arity]

def time (steps : List (ℕ×ℕ)) (cost : (ℕ×ℕ)→ℕ) (terms count arity : ℕ) : ℕ :=
  fillTime (terms*count)+
    LightTernaryFixedChannelLoop.time (labels steps)
      (fun c => cost (steps.getD c.1 (0,0))) arity+100

theorem library_meets {lim : Limits} {d i T : ℕ} {vals : List ℤ} {μ : ℕ→ℤ}
    {R : ℤ→(ℕ→ℤ)→Prop} (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ))
    (hi : i<steps.length)
    (h : Meets lim (LightTernaryMomentSourceProgram.program xl yl zl xr yr zr
      (steps.getD i (0,0)).1 (steps.getD i (0,0)).2) 126 d vals μ T R) :
    Meets lim (library xl yl zl xr yr zr steps) (127*i+126) d vals μ T R := by
  induction steps generalizing i with
  | nil => simp at hi
  | cons c cs ih =>
    cases i with
    | zero =>
      simpa only [library,ReportingHostRelocation.program,List.getD_cons_zero,
        LightTernaryMomentSourceProgram.program_length,Nat.mul_zero,Nat.zero_add] using
        h.append ((library xl yl zl xr yr zr cs).map (ReportingHostRelocation.relocate 127))
    | succ i =>
      have hi' : i<cs.length := by simpa using hi
      have hh := ih hi' (by simpa only [List.getD_cons_succ] using h)
      have hr := ReportingHostRelocation.meets hh
        (LightTernaryMomentSourceProgram.program xl yl zl xr yr zr c.1 c.2)
      convert hr using 1 <;>
        simp only [library,LightTernaryMomentSourceProgram.program_length] <;> omega

variable {lim : Limits} {d : ℕ}

/-- Every step receipt refers to the actual included 127-procedure source
channel program. Those receipts come from `MomentChannelStep.Procs.meets`
and `MomentSourceProgram.host_meets`, which execute both original-source
weight initializers and the full source/count frontend. -/
theorem program_meets {originalB nB originalC nC leftWeight rightWeight
      matrix count out terms : ℕ} {backend : List ℤ}
    (xl yl zl xr yr zr : List ℤ) (steps : List (ℕ×ℕ))
    (cost : (ℕ×ℕ)→ℕ) (score : ℕ→ℕ→ℕ→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hwindow : matrix+terms*count≤leftWeight) (hspace : leftWeight≤lim.space)
    (htermsWord : (terms : ℤ)≤lim.word)
    (hstep : ∀ i<steps.length, ∀ ν,
      TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight
        (steps.take i) score ν →
      Meets lim (LightTernaryMomentSourceProgram.program xl yl zl xr yr zr
        (steps.getD i (0,0)).1 (steps.getD i (0,0)).2) 126 (d+1)
        (LightTernaryMomentChannelStep.args originalB nB originalC nC leftWeight rightWeight
          matrix count out backend) ν (cost (steps.getD i (0,0)))
        (fun _ ξ => TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight
          (steps.take (i+1)) score ξ)) :
    Meets lim (program xl yl zl xr yr zr steps terms (9+backend.length))
      (127*steps.length+1) d
      (LightTernaryMomentChannelStep.args originalB nB originalC nC leftWeight rightWeight
        matrix count out backend) μ
      (time steps cost terms count (9+backend.length))
      (fun _ ν => TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight steps score ν) := by
  let vals := LightTernaryMomentChannelStep.args originalB nB originalC nC leftWeight rightWeight
    matrix count out backend
  have hlen : vals.length=9+backend.length := by simp [vals,LightTernaryMomentChannelStep.args]; omega
  have hmain : (program xl yl zl xr yr zr steps terms (9+backend.length))[127*steps.length+1]?=
      some (body steps terms (9+backend.length)) := by
    unfold program
    rw [List.getElem?_append_right (by simp),library_length]
    have he : 127*steps.length+1-127*steps.length=1 := by omega
    rw [he]
    rfl
  have hfill : (program xl yl zl xr yr zr steps terms (9+backend.length))[127*steps.length]?=
      some fillBody := by
    unfold program
    rw [List.getElem?_append_right (by simp),library_length,Nat.sub_self]
    rfl
  have hmulWord : (terms : ℤ)*(count : ℤ)≤lim.word := by
    have hh : terms*count≤lim.space := by omega
    have hz : (terms : ℤ)*(count : ℤ)≤(lim.space : ℤ) := by exact_mod_cast hh
    exact hz.trans hw
  have hcountWord : (count : ℤ)≤lim.word ∨ terms=0 := by
    by_cases ht : 0<terms
    · left
      have hm : count≤terms*count := by nlinarith
      exact (Int.ofNat_le.mpr (show count≤lim.space by omega)).trans hw
    · exact Or.inr (by omega)
  -- Variable reads themselves are safe; multiplication is charged and bounded.
  apply Meets.of_body hmain
  unfold body time
  refine Ends.callThen (LightTernaryMomentAccumulate.zero_meets hfill μ hw (hwindow.trans hspace))
    ?_ (ha := by light_side [LightTernaryMomentChannelStep.args]) (hd := hd) (hT := by light_time)
  intro r ν ⟨hzero,hkeep⟩
  have hI : TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight [] score ν :=
    TernaryMomentMatrixInvariant.zero score hzero hkeep
  let I : ℕ→(ℕ→ℤ)→Prop := fun i ξ =>
    TernaryMomentMatrixInvariant.Holds μ matrix count terms leftWeight (steps.take i) score ξ
  have hloc : ∀ i<vals.length,
      Function.update (frame vals) (9+backend.length) r i=frame vals i := by
    intro i hi
    rw [Function.update_of_ne (by omega)]
  have hs : ∀ i<(labels steps).length, ∀ ξ, I i ξ →
      Meets lim (program xl yl zl xr yr zr steps terms (9+backend.length))
        (entry ((labels steps).getD i (0,0))) (d+1) vals ξ
        (cost (steps.getD ((labels steps).getD i (0,0)).1 (0,0))) (fun _ ζ => I (i+1) ζ) := by
    intro i hi ξ hξ
    have hi' : i<steps.length := by simpa [labels] using hi
    have hl : (labels steps).getD i (0,0)=(i,0) := by
      rw [List.getD_eq_getElem _ _ hi]
      simp [labels]
    rw [hl]
    exact (library_meets xl yl zl xr yr zr steps hi' (hstep i hi' ξ hξ)).append
      [fillBody,body steps terms (9+backend.length)]
  have hh := LightTernaryFixedChannelLoop.ends (labels steps) entry
    (fun c => cost (steps.getD c.1 (0,0))) vals
    (Function.update (frame vals) (9+backend.length) r) ν I hd hloc (by simpa [I] using hI) hs
  rw [hlen] at hh
  apply hh.mono (by light_time)
  intro σ hσ
  simpa only [I,labels,List.length_map,List.length_range,List.take_length] using hσ

end ThreeSum.LightTernaryMomentDriver
