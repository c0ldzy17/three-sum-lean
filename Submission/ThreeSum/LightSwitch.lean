import Submission.ThreeSum.LightSwitchBounds
import Submission.ThreeSum.LightSwitchScalar

/-!
# Execute the exact cubic switch in the benchmark language

The fixed procedure increases q from zero until the first accepted integer.
At every prescribed reporting depth that integer exists, including when
the residual is zero. Memory is unchanged and all scalar intermediates fit
the explicit polynomial word bound.
-/

namespace ThreeSum.LightSwitch

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def test : Cond :=
  (k 10 *' (v 0 -' v 1) *'
    (v 3 *' (k 799 *' v 2 *' v 2 +' v 3 *' (k 72 *' v 2 +' k 24 *' v 3)))) <'
    ((k 291 *' v 0 +' k 1000 *' v 1) *' v 2 *' v 2 *' v 2)

def body : Stmt :=
  .set 3 (k 0) ;;
  .while test (.set 3 (v 3 +' k 1)) ;;
  .set 0 (v 3)

def time (r : ℕ) : ℕ := 100*(r+1)+50

variable {lim : Limits} {P : Program} {μ : ℕ→ℤ} {J j r q d : ℕ}

theorem frame_vars_bound (hj : j ≤ J) (hq : q ≤ r) :
    ∀ i, |(frame [(J : ℤ),j,r,q]) i| ≤ ((J+r+1001 : ℕ) : ℤ) := by
  intro i
  rcases i with _ | _ | _ | _ | i <;> simp [frame] <;> omega

theorem test_safe (hj : j ≤ J) (hq : q ≤ r)
    (hword : (word J r : ℤ) ≤ lim.word) :
    test.Safe lim ⟨frame [(J : ℤ),j,r,q],μ⟩ := by
  have hv := frame_vars_bound hj hq
  have hB : 2 ≤ J+r+1001 := by omega
  unfold test Cond.Safe
  constructor
  · apply LightSwitchScalar.scalar_safe hB _ hv
      _ (by simp [LightSwitchScalar.Small])
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : (k 10 *' (v 0 -' v 1) *'
        (v 3 *' (k 799 *' v 2 *' v 2 +' v 3 *' (k 72 *' v 2 +' k 24 *' v 3)))).cost ≤ 64))).trans hword
  · apply LightSwitchScalar.scalar_safe hB _ hv
      _ (by simp [LightSwitchScalar.Small])
    exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by omega)
      (by decide : ((k 291 *' v 0 +' k 1000 *' v 1) *' v 2 *' v 2 *' v 2).cost ≤ 64))).trans hword

theorem test_holds_iff (hj : j ≤ J) :
    test.Holds ⟨frame [(J : ℤ),j,r,q],μ⟩ ↔ factor J j*cubic r q < left J j r := by
  simp only [test,Cond.Holds,Expr.val,Op.eval,frame,List.getD_cons_zero,
    List.getD_cons_succ,Nat.cast_add,Nat.cast_ofNat]
  unfold factor cubic left
  exact_mod_cast (Iff.rfl :
    10*(J-j)*(q*(799*r*r+q*(72*r+24*q))) < (291*J+1000*j)*r*r*r ↔
    10*(J-j)*(q*(799*r*r+q*(72*r+24*q))) < (291*J+1000*j)*r*r*r)

theorem meets {p : ℕ} (hp : P[p]?=some body) (hj : j ≤ J)
    (hne : (Switch.candidates J j r).Nonempty)
    (hword : (word J r : ℤ) ≤ lim.word) :
    Meets lim P p d [J,j,r] μ (time r)
      (fun result ν => result=(Switch.switchIndex J j r : ℤ) ∧ ν=μ) := by
  have hindex := index_le_residual hne
  have hbase : J+r+1001 ≤ word J r :=
    Nat.le_self_pow (by decide : (64 : ℕ) ≠ 0) _
  have hlinear : ((J+r+1001 : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hbase).trans hword
  apply Meets.of_body hp
  unfold body time
  light_set (0 : ℕ)
  refine Ends.next (50*Switch.switchIndex J j r+60) (Ends.whileBlock
    (fun i σ => σ=⟨frame [(J : ℤ),j,r,i],μ⟩)
    (Switch.switchIndex J j r) (by simp) ?round ?done (by light_time [test]))
    (hT := by light_time [test])
  case round =>
    rintro i _ hi rfl
    have hle : i ≤ r := by omega
    refine ⟨test_safe hj hle hword,
      (test_holds_iff hj).mpr (before_rejects hne hi),by light_side,?_⟩
    simp [update_frame_setLocal]
  case done =>
    rintro _ rfl
    refine ⟨test_safe hj hindex hword,?_,?_⟩
    · rw [test_holds_iff hj]
      exact not_lt_of_ge (at_accepts hne)
    · light_set (Switch.switchIndex J j r)
      exact ⟨rfl,rfl⟩

def program : Program := [body]

theorem program_meets (hj : j ≤ J) (hne : (Switch.candidates J j r).Nonempty)
    (hword : (word J r : ℤ) ≤ lim.word) :
    Meets lim program 0 d [J,j,r] μ (time r)
      (fun result ν => result=(Switch.switchIndex J j r : ℤ) ∧ ν=μ) :=
  meets rfl hj hne hword

theorem actual_meets {n j : ℕ} (hj : j ≤ Switch.terminalDepth n)
    (hword : (word (Scales.blockCount (Scales.inputBits n))
      (Switch.residualSize n j) : ℤ) ≤ lim.word) :
    Meets lim program 0 d
      [Scales.blockCount (Scales.inputBits n),j,Switch.residualSize n j] μ
      (time (Switch.residualSize n j))
      (fun result ν => result=(Switch.actualSwitch n j : ℤ) ∧ ν=μ) := by
  have hdepth := Switch.actual_depth_condition hj
  exact program_meets (by omega) (actual_candidates_nonempty hj) hword

end ThreeSum.LightSwitch
