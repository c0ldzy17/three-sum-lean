import Submission.ThreeSum.LightArray

namespace ThreeSum.LightTernaryCommitKeys
open Light
set_option maxHeartbeats 2000000

def body : Stmt :=
  .call 0 [v 0,v 1,v 2] 9 ;;
  .call 0 [v 3,v 4,v 5] 9 ;;
  .call 0 [v 6,v 7,v 8] 9 ;;
  .set 0 (k 0)

def program : Program :=[copyBody,body]
def time (nB nC nO : ℕ) : ℕ :=copyTime nB+copyTime nC+copyTime nO+100

/-- Copy the selected candidate's actual packed keys into the three retained
old-prefix buffers. All three source arrays are above the retained buffers,
so committing one side cannot change another side's source. -/
theorem program_meets {lim : Limits} {Bnew Bold nB Cnew Cold nC Onew Oold nO d : ℕ}
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ)≤lim.word)
    (hBC : Bold+nB≤Cold) (hCO : Cold+nC≤Oold)
    (hOB : Oold+nO≤Bnew) (hOC : Oold+nO≤Cnew) (hOO : Oold+nO≤Onew)
    (hB : Bnew+nB≤lim.space) (hC : Cnew+nC≤lim.space) (hO : Onew+nO≤lim.space)
    (hd : d<lim.depth) :
    Meets lim program 1 d [Bnew,Bold,nB,Cnew,Cold,nC,Onew,Oold,nO] μ (time nB nC nO)
      (fun r ν => r=0 ∧ Kept μ ν Bold ∧
        (∀ i<nB, ν (Bold+i)=μ (Bnew+i)) ∧
        (∀ i<nC, ν (Cold+i)=μ (Cnew+i)) ∧
        (∀ i<nO, ν (Oold+i)=μ (Onew+i)) ∧
        (∀ x, Oold+nO≤x → ν x=μ x)) := by
  have hBold : Bold+nB≤lim.space := by omega
  have hCold : Cold+nC≤lim.space := by omega
  have hOold : Oold+nO≤lim.space := by omega
  have h0 := copy_meets (P := program) (μ := μ) (p := 0) (d := d+1)
    (src := Bnew) (dst := Bold) (n := nB) rfl hw hB hBold (Or.inr (by omega))
  apply Meets.of_body (by rfl)
  unfold body time
  light_call h0 with rb μb ⟨hb,kb⟩
  have h1 := copy_meets (P := program) (μ := μb) (p := 0) (d := d+1)
    (src := Cnew) (dst := Cold) (n := nC) rfl hw hC hCold (Or.inr (by omega))
  light_call h1 with rc μc ⟨hc,kc⟩
  have h2 := copy_meets (P := program) (μ := μc) (p := 0) (d := d+1)
    (src := Onew) (dst := Oold) (n := nO) rfl hw hO hOold (Or.inr (by omega))
  light_call h2 with ro ν ⟨ho,ko⟩
  light_set (0 : ℕ)
  refine ⟨by simp,?_,?_,?_,?_,?_⟩
  · intro x hx
    change ν x=μ x
    rw [ko x (by omega),kc x (by omega),kb x (by omega)]
  · intro i hi
    change ν (Bold+i)=μ (Bnew+i)
    rw [ko _ (by omega),kc _ (by omega),hb i hi]
  · intro i hi
    change ν (Cold+i)=μ (Cnew+i)
    rw [ko _ (by omega),hc i hi,kb _ (by omega)]
  · intro i hi
    change ν (Oold+i)=μ (Onew+i)
    rw [ho i hi,kc _ (by omega),kb _ (by omega)]
  · intro x hx
    change ν x=μ x
    rw [ko x (by omega),kc x (by omega),kb x (by omega)]

theorem time_eq (nB nC nO : ℕ) : time nB nC nO=16*(nB+nC+nO)+118 := by
  simp [time,copyTime]
  omega

end ThreeSum.LightTernaryCommitKeys
