import Submission.ThreeSum.TernaryArenaPrefixFootprints

noncomputable section
namespace ThreeSum.TernaryArenaAllocation
open TernaryArenaPrefixFootprints TernaryArenaLayout
open TernaryCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]

/-- Fixed data compiled into the actual capacity initializer. Every guard is
proved for the concrete source, tensor, near and seed arithmetic footprints. -/
structure Allocation (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ) where
  D : ℕ
  E : ℕ
  exponentPositive : 1≤E
  exponentConstant : E≤D
  bound : ∀ n U j, j≤Nat.clog M (n^2) →
    envelope maps τ cap M b K H drift scale n U j≤capacity D E (n+U)

/-- Universal parameters are selected once from proved concrete bounds.
They are not input words, guessed memory layouts or runtime advice. -/
def allocation (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (hM : 1<M) (hb : 1<b) : Allocation maps τ cap M b K H drift scale := by
  let hex := fixed_capacity_all maps τ cap K H drift scale hM hb
  let D := Classical.choose hex
  have hD := Classical.choose_spec hex
  let E := Classical.choose hD
  have hE := Classical.choose_spec hD
  refine ⟨D+E+1,E+1,by omega,by omega,fun n U j hj=>?_⟩
  have hOld : envelope maps τ cap M b K H drift scale n U j≤capacity D E (n+U) := hE n U j hj
  apply hOld.trans
  change 256*(D+1)*(n+U+1)^E≤256*(D+E+1+1)*(n+U+1)^(E+1)
  exact Nat.mul_le_mul (Nat.mul_le_mul_left 256 (by omega : D+1≤D+E+1+1))
    (Nat.pow_le_pow_right (by omega : 1≤n+U+1) (by omega : E≤E+1))

theorem Allocation.fits {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U j : ℕ)
    (hj : j≤Nat.clog M (n^2)) :
    Fits (capacity A.D A.E (n+U)) (numbers maps τ cap M b K H drift scale n U j) := by
  intro v hv
  have hs := List.le_sum_of_mem hv
  have hp : total maps τ cap M b K H drift scale n U j+1≤
      (total maps τ cap M b K H drift scale n U j+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (by omega : 1≤total maps τ cap M b K H drift scale n U j+1) (by decide : 1≤4)
  exact hs.trans ((Nat.le_succ _).trans (hp.trans (A.bound n U j hj)))

theorem Allocation.total_le {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U j : ℕ)
    (hj : j≤Nat.clog M (n^2)) :
    total maps τ cap M b K H drift scale n U j≤capacity A.D A.E (n+U) := by
  have hp : total maps τ cap M b K H drift scale n U j+1≤
      (total maps τ cap M b K H drift scale n U j+1)^4 := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (by omega : 1≤total maps τ cap M b K H drift scale n U j+1) (by decide : 1≤4)
  exact (Nat.le_succ _).trans (hp.trans (A.bound n U j hj))

theorem capacity_coefficient (D E x : ℕ) : 256*(D+1)≤capacity D E x := by
  have hh : 1≤(x+1)^E := Nat.one_le_pow _ _ (by omega)
  unfold capacity
  exact Nat.le_mul_of_pos_right _ hh

theorem Allocation.constants {maps : Fin F→Weight m p} {τ cap M b K H drift scale : ℕ}
    (A : Allocation maps τ cap M b K H drift scale) (n U : ℕ) :
    A.D≤capacity A.D A.E (n+U) ∧ A.E≤capacity A.D A.E (n+U) ∧
      n+U+1≤capacity A.D A.E (n+U) := by
  have hc := capacity_coefficient A.D A.E (n+U)
  have hD : A.D≤capacity A.D A.E (n+U) := by omega
  have hp : n+U+1≤(n+U+1)^A.E := by
    simpa only [pow_one] using Nat.pow_le_pow_right
      (by omega : 1≤n+U+1) A.exponentPositive
  refine ⟨hD,A.exponentConstant.trans hD,?_⟩
  exact hp.trans (Nat.le_mul_of_pos_left _ (by positivity))

end ThreeSum.TernaryArenaAllocation
