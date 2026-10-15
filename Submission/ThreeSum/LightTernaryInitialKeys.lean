import Submission.ThreeSum.LightArray

namespace ThreeSum.LightTernaryInitialKeys
open Light
set_option maxHeartbeats 2000000

def body : Stmt :=
  .call 0 [v 0,v 1,k 0] 6 ;;
  .call 0 [v 2,v 3,k 0] 6 ;;
  .call 0 [v 4,v 5,k 0] 6 ;;
  .set 0 (k 0)

def program : Program :=[fillBody,body]
def time (nB nC nO : ℕ) : ℕ :=fillTime nB+fillTime nC+fillTime nO+100

/-- The empty-prefix original keys are constructed by real zero fills. -/
theorem program_meets {lim : Limits} {B nB C nC O nO d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word) (hBC : B+nB≤C) (hCO : C+nC≤O)
    (hO : O+nO≤lim.space) (hd : d<lim.depth) :
    Meets lim program 1 d [B,nB,C,nC,O,nO] μ (time nB nC nO)
      (fun r ν => r=0 ∧ Kept μ ν B ∧
        (∀ i<nB, ν (B+i)=0) ∧ (∀ i<nC, ν (C+i)=0) ∧ (∀ i<nO, ν (O+i)=0)) := by
  have hBspace : B+nB≤lim.space := by omega
  have hCspace : C+nC≤lim.space := by omega
  have h0 := fill_meets (P := program) (μ := μ) (p := 0) (d := d+1) (dst := B) (n := nB) (x := (0 : ℤ)) rfl hw hBspace
  apply Meets.of_body (by rfl)
  unfold body time
  light_call h0 with rb μb ⟨hb,kb⟩
  have h1 := fill_meets (P := program) (μ := μb) (p := 0) (d := d+1) (dst := C) (n := nC) (x := (0 : ℤ)) rfl hw hCspace
  light_call h1 with rc μc ⟨hc,kc⟩
  have h2 := fill_meets (P := program) (μ := μc) (p := 0) (d := d+1) (dst := O) (n := nO) (x := (0 : ℤ)) rfl hw hO
  light_call h2 with ro ν ⟨ho,ko⟩
  light_set (0 : ℕ)
  refine ⟨by simp,?_,?_,?_,?_⟩
  · intro x hx
    change ν x=μ x
    rw [ko x (by omega),kc x (by omega),kb x (by omega)]
  · intro i hi
    change ν (B+i)=0
    rw [ko _ (by omega),kc _ (by omega)]
    exact (hb i (by simpa using hi)).trans (List.getElem_replicate _)
  · intro i hi
    change ν (C+i)=0
    rw [ko _ (by omega)]
    exact (hc i (by simpa using hi)).trans (List.getElem_replicate _)
  · intro i hi
    exact (ho i (by simpa using hi)).trans (List.getElem_replicate _)

theorem time_eq (nB nC nO : ℕ) : time nB nC nO=13*(nB+nC+nO)+118 := by
  simp [time,fillTime]
  omega

end ThreeSum.LightTernaryInitialKeys
