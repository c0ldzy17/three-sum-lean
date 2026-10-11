import Submission.ThreeSum.LightPascal

/-! # Actual Pascal lookup for reporting child and terminal candidate counts -/

namespace ThreeSum.LightReportingBinomial

open Light LightPascal

set_option maxHeartbeats 1000000
set_option maxRecDepth 8000

/-- Arguments are n, k, and a polynomial Pascal scratch region. -/
def body (pPascal : ℕ) : Stmt :=
  .call pPascal [v 2,v 0] 3 ;;
  .set 4 (v 2 +' v 0 *' (v 0 +' k 1) +' v 1) ;;
  .set 0 (M (v 4))

def program : Program := [fillBody,LightArray.linearBody,rowBody 1,buildBody 0 2,body 3]
def time (n : ℕ) : ℕ := buildTime n+100

variable {lim : Limits}

theorem program_meets {μ : ℕ→ℤ} {n k work d : ℕ}
    (hk : k≤n) (hw : (lim.space : ℤ)≤lim.word)
    (hspace : work+tableSize n≤lim.space)
    (hword : ((2^(n+1) : ℕ) : ℤ)≤lim.word) (hd : d+3≤lim.depth) :
    Meets lim program 4 d [n,k,work] μ (time n)
      (fun r ν => r=(n.choose k : ℤ) ∧ SameOutside μ ν work (tableSize n)) := by
  let address := work+n*(n+1)+k
  have hsize : n+1≤tableSize n := by unfold tableSize; nlinarith
  have haddr : address<lim.space := by unfold address tableSize at *; nlinarith
  have hcalc : (work : ℤ)+(n : ℤ)*((n : ℤ)+1)+(k : ℤ)=(address : ℤ) := by
    simp only [address,Nat.cast_add,Nat.cast_mul,Nat.cast_one]
  have hchoose : (n.choose k : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr ((Nat.choose_le_two_pow n k).trans
      (Nat.pow_le_pow_right (by decide) (by omega)))).trans hword
  apply Meets.of_body (p := 4) (by rfl : program[4]?=some (body 3))
  unfold body time
  have hrun := LightPascal.build_meets (P := program) (d := d+1) (μ := μ)
    (pBuild := 3) (pFill := 0) (pRow := 2) (pLinear := 1)
    (dst := work) (L := n) rfl rfl rfl rfl hw (by omega) hspace hword
  light_call hrun using LightPascal.buildTime with unused ν ⟨htable,hkept⟩
  light_set (address : ℕ) using hcalc,LightPascal.buildTime
  have hread : ν address=(n.choose k : ℤ) := htable n le_rfl k hk
  light_set (n.choose k : ℕ) using hread,LightPascal.buildTime
  exact ⟨by simp,hkept⟩

theorem time_bound (n : ℕ) : time n≤1100*(n+1)^2 := by
  have hh := LightPascal.buildTime_bound n
  have hp : 1≤(n+1)^2 := by
    have hp0 : 0<(n+1)^2 := by positivity
    omega
  unfold time
  nlinarith

end ThreeSum.LightReportingBinomial
