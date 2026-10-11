import Submission.ThreeSum.LightSwitch
import Submission.ThreeSum.LightSmallDivide

/-! # Actual computation of the terminal reporting depth -/

namespace ThreeSum.LightSwitchDepth

open Light

def depth (J : ℕ) : ℕ := 13*J/20

def body (pDiv : ℕ) : Stmt :=
  .call pDiv [k 13 *' v 0,k 20] 1 ;;
  .set 0 (v 1)

def time (J : ℕ) : ℕ := LightSmallDivide.time (13*J) 20+50
def word (J : ℕ) : ℕ := 13*J+22

variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J d : ℕ}

theorem meets {p pDiv : ℕ} (hp : P[p]?=some (body pDiv))
    (hdiv : P[pDiv]?=some LightSmallDivide.body)
    (hword : (word J : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim P p d [J] μ (time J)
      (fun result ν => result=(depth J : ℤ) ∧ ν=μ) := by
  unfold word at hword
  apply Meets.of_body hp
  unfold body time
  have hc := LightSmallDivide.meets (d := d+1) (a := 13*J) (b := 20) hdiv μ hword
  light_call hc using word,LightSmallDivide.time with result ν ⟨hresult,rfl⟩
  light_set (depth J) using depth,word,LightSmallDivide.time,hresult
  exact ⟨rfl,rfl⟩

def program : Program := [body 1,LightSmallDivide.body]

theorem program_meets (hword : (word J : ℤ) ≤ lim.word) (hd : d < lim.depth) :
    Meets lim program 0 d [J] μ (time J)
      (fun result ν => result=(depth J : ℤ) ∧ ν=μ) := meets rfl rfl hword hd

theorem depth_eq_terminalDepth (n : ℕ) :
    depth (Scales.blockCount (Scales.inputBits n))=Switch.terminalDepth n := rfl

theorem time_bound (J : ℕ) : time J ≤ 260*J+90 := by
  have hh := LightSmallDivide.time_bound (13*J) 20
  unfold time
  omega

end ThreeSum.LightSwitchDepth
