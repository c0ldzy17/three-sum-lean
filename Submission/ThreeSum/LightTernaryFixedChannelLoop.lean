import Submission.ThreeSum.LightTernaryMomentChannelStep
import Submission.ThreeSum.TernaryMomentSchedule

/-! Actual fixed-program traversal of the finitely many moment channels.
The degree is fixed in program text, rather than interpreted as a power oracle. -/
namespace ThreeSum.LightTernaryFixedChannelLoop
open Light
set_option maxHeartbeats 1500000

abbrev Channel := ℕ×ℕ

def arguments (arity : ℕ) : List Expr := LightTernaryMomentChannelStep.callArgs (List.range arity)

theorem arguments_spec {lim : Limits} {loc μ : ℕ→ℤ} (vals : List ℤ)
    (hloc : ∀ i<vals.length, loc i=frame vals i) :
    (∀ e∈arguments vals.length, e.Safe lim ⟨loc,μ⟩) ∧
      (arguments vals.length).map (·.val ⟨loc,μ⟩)=vals := by
  have hv : LightTernaryMomentChannelStep.values (List.range vals.length) vals=vals := by
    apply List.ext_getElem (by simp [LightTernaryMomentChannelStep.values])
    intro i hi hi'
    simp only [LightTernaryMomentChannelStep.values,List.getElem_map,List.getElem_range,frame]
    exact List.getD_eq_getElem _ _ hi'
  constructor
  · intro e he
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
    simp [v,Expr.Safe]
  · calc
      _=LightTernaryMomentChannelStep.values (List.range vals.length) vals := by
        simp only [arguments,LightTernaryMomentChannelStep.callArgs,
          LightTernaryMomentChannelStep.values,List.map_map,Function.comp_def,v,Expr.val]
        apply List.map_congr_left
        intro i hi
        exact hloc i (List.mem_range.mp hi)
      _=vals := hv

@[simp] theorem arguments_cost (arity : ℕ) :
    ((arguments arity).map Expr.cost).sum=arity := by
  simp [arguments]

def body (steps : List Channel) (entry : Channel→ℕ) (arity : ℕ) : Stmt :=
  match steps with
  | [] => .skip
  | c::cs => .call (entry c) (arguments arity) arity ;; body cs entry arity

def time (steps : List Channel) (cost : Channel→ℕ) (arity : ℕ) : ℕ :=
  match steps with
  | [] => 0
  | c::cs => arity+2+cost c+time cs cost arity

variable {lim : Limits} {P : Program} {d : ℕ}

/-- The finite traversal executes each registered concrete channel procedure.
Its only callee premise is the ordinary `Meets` execution theorem at that
procedure's program index; the theorem introduces no abstract operation. -/
theorem ends (steps : List Channel) (entry : Channel→ℕ) (cost : Channel→ℕ)
    (vals : List ℤ) (loc μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop)
    (hd : d<lim.depth) (hloc : ∀ i<vals.length, loc i=frame vals i)
    (hI : I 0 μ)
    (hstep : ∀ i<steps.length, ∀ ν, I i ν →
      Meets lim P (entry (steps.getD i (0,0))) (d+1) vals ν
        (cost (steps.getD i (0,0))) (fun _ ξ => I (i+1) ξ)) :
    Ends lim P d (body steps entry vals.length) ⟨loc,μ⟩
      (time steps cost vals.length) (fun σ => I steps.length σ.mem) := by
  induction steps generalizing loc μ I with
  | nil => exact Ends.skip hI
  | cons c cs ih =>
    have hc := hstep 0 (by simp) μ hI
    simp only [List.getD_cons_zero] at hc
    unfold body time
    refine Ends.callThen hc ?_ (ha := arguments_spec vals hloc) (hd := hd)
      (hT := by rw [arguments_cost]; omega)
    intro r ν hν
    have hloc' : ∀ i<vals.length, Function.update loc vals.length r i=frame vals i := by
      intro i hi
      rw [Function.update_of_ne (by omega)]
      exact hloc i hi
    have htail : ∀ i<cs.length, ∀ ξ, I (i+1) ξ →
        Meets lim P (entry (cs.getD i (0,0))) (d+1) vals ξ
          (cost (cs.getD i (0,0))) (fun _ ζ => I (i+1+1) ζ) := by
      intro i hi ξ hξ
      have hh := hstep (i+1) (by simp; omega) ξ hξ
      simpa only [List.getD_cons_succ] using hh
    have hh := ih (Function.update loc vals.length r) ν (fun i => I (i+1)) hloc' hν htail
    have ht : time cs cost vals.length≤
        vals.length+2+cost c+time cs cost vals.length-
          (((arguments vals.length).map Expr.cost).sum+2+cost c) := by
      rw [arguments_cost]
      omega
    apply hh.mono ht
    intro σ hσ
    simpa only [List.length_cons] using hσ

theorem meets {steps : List Channel} {entry cost : Channel→ℕ} {vals : List ℤ}
    {pMain : ℕ} (hmain : P[pMain]?=some (body steps entry vals.length))
    (μ : ℕ→ℤ) (I : ℕ→(ℕ→ℤ)→Prop) (hd : d<lim.depth) (hI : I 0 μ)
    (hstep : ∀ i<steps.length, ∀ ν, I i ν →
      Meets lim P (entry (steps.getD i (0,0))) (d+1) vals ν
        (cost (steps.getD i (0,0))) (fun _ ξ => I (i+1) ξ)) :
    Meets lim P pMain d vals μ (time steps cost vals.length)
      (fun _ ν => I steps.length ν) := by
  exact Meets.of_body hmain (ends steps entry cost vals (frame vals) μ I hd (by simp) hI hstep)

/-- The number of complete source-count calls is a fixed quadratic in the
chosen moment count, independent of the original input size. -/
theorem time_le_length (steps : List Channel) (arity C : ℕ) (cost : Channel→ℕ)
    (hcost : ∀ c∈steps, cost c≤C) :
    time steps cost arity≤steps.length*(arity+2+C) := by
  induction steps with
  | nil => simp [time]
  | cons c cs ih =>
    have ht := ih (fun e he => hcost e (by simp [he]))
    have hc := hcost c (by simp)
    simp only [time,List.length_cons,Nat.add_mul,one_mul]
    omega

theorem time_le (terms arity C : ℕ) (cost : Channel→ℕ)
    (hcost : ∀ c∈TernaryMomentSchedule.channels terms, cost c≤C) :
    time (TernaryMomentSchedule.channels terms) cost arity≤terms^2*(arity+2+C) := by
  exact (time_le_length _ arity C cost hcost).trans
    (Nat.mul_le_mul_right _ (TernaryMomentSchedule.length_le terms))

end ThreeSum.LightTernaryFixedChannelLoop
