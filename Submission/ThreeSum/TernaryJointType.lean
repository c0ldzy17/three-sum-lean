import Mathlib.Data.Fin.VecNotation
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-!
# Fixed-type ternary addition and its forced joint type

The local objects are genuine trit words. `PointwiseSum` is ordinary integer
addition, so sums three and four are forbidden. All finite statements are
parametric in the word length and in the source/output marginal counts.
-/

namespace ThreeSum.TernaryJointType

open Finset

abbrev TritWord (L : ℕ) := Fin L → Fin 3
abbrev DigitType := Fin 3 → ℕ

def digitCount {L : ℕ} (w : TritWord L) (d : Fin 3) : ℕ :=
  ∑ i : Fin L, if w i = d then 1 else 0

def HasType {L : ℕ} (w : TritWord L) (t : DigitType) : Prop :=
  ∀ d, digitCount w d = t d

def PointwiseSum {L : ℕ} (a b q : TritWord L) : Prop :=
  ∀ i, (a i).val + (b i).val = (q i).val

def Edge {L : ℕ} (α π : DigitType) (a b q : TritWord L) : Prop :=
  HasType a α ∧ HasType b α ∧ HasType q π ∧ PointwiseSum a b q

def jointCount {L : ℕ} (a b : TritWord L) (u v : Fin 3) : ℕ :=
  ∑ i : Fin L, if a i = u ∧ b i = v then 1 else 0

theorem jointCount_row {L : ℕ} (a b : TritWord L) (u : Fin 3) :
    ∑ v : Fin 3, jointCount a b u v = digitCount a u := by
  unfold jointCount digitCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases ha : a i = u <;> simp [ha]

theorem jointCount_col {L : ℕ} (a b : TritWord L) (v : Fin 3) :
    ∑ u : Fin 3, jointCount a b u v = digitCount b v := by
  unfold jointCount digitCount
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  by_cases hb : b i = v <;> simp [hb]

theorem jointCount_forbidden {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) (u v : Fin 3) (hlarge : 2 < u.val + v.val) :
    jointCount a b u v = 0 := by
  unfold jointCount
  apply Finset.sum_eq_zero
  intro i hi
  have hnot : ¬ (a i = u ∧ b i = v) := by
    intro h
    have hq := (q i).isLt
    have hs := hsum i
    rw [h.1, h.2] at hs
    omega
  simp [hnot]

private theorem sum_indicator_zero (a b q : Fin 3)
    (h : a.val + b.val = q.val) :
    (if q = 0 then 1 else 0 : ℕ) = (if a = 0 ∧ b = 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases q <;> norm_num at h <;> decide

private theorem sum_indicator_one (a b q : Fin 3)
    (h : a.val + b.val = q.val) :
    (if q = 1 then 1 else 0 : ℕ) =
      (if a = 0 ∧ b = 1 then 1 else 0) +
        (if a = 1 ∧ b = 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases q <;> norm_num at h <;> decide

private theorem sum_indicator_two (a b q : Fin 3)
    (h : a.val + b.val = q.val) :
    (if q = 2 then 1 else 0 : ℕ) =
      (if a = 0 ∧ b = 2 then 1 else 0) +
        (if a = 1 ∧ b = 1 then 1 else 0) +
          (if a = 2 ∧ b = 0 then 1 else 0) := by
  fin_cases a <;> fin_cases b <;> fin_cases q <;> norm_num at h <;> decide

theorem output_zero {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    digitCount q 0 = jointCount a b 0 0 := by
  unfold digitCount jointCount
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_indicator_zero (a i) (b i) (q i) (hsum i)

theorem output_one {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    digitCount q 1 = jointCount a b 0 1 + jointCount a b 1 0 := by
  unfold digitCount jointCount
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_indicator_one (a i) (b i) (q i) (hsum i)

theorem output_two {L : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    digitCount q 2 = jointCount a b 0 2 + jointCount a b 1 1 +
      jointCount a b 2 0 := by
  unfold digitCount jointCount
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact sum_indicator_two (a i) (b i) (q i) (hsum i)

/-- Pure marginal arithmetic; no joint type is selected or assumed. -/
theorem joint_type_unique_nat
    (x00 x01 x02 x10 x11 x20 p0 p1 p2 a1 a2 : ℕ)
    (h00 : x00 = p0) (h02 : x02 = a2) (h20 : x20 = a2)
    (hrow1 : x10 + x11 = a1) (hcol1 : x01 + x11 = a1)
    (hout1 : x01 + x10 = p1) (hout2 : x02 + x11 + x20 = p2)
    (hthirds : p2 = 3 * a2) :
    x00 = p0 ∧ x01 = p1 / 2 ∧ x10 = p1 / 2 ∧
      x02 = p2 / 3 ∧ x11 = p2 / 3 ∧ x20 = p2 / 3 := by
  omega

/-- The same uniqueness identity over the rationals. -/
theorem joint_type_unique_rat
    (x00 x01 x02 x10 x11 x20 p0 p1 p2 a1 a2 : ℚ)
    (h00 : x00 = p0) (h02 : x02 = a2) (h20 : x20 = a2)
    (hrow1 : x10 + x11 = a1) (hcol1 : x01 + x11 = a1)
    (hout1 : x01 + x10 = p1) (hout2 : x02 + x11 + x20 = p2)
    (hthirds : p2 = 3 * a2) :
    x00 = p0 ∧ x01 = p1 / 2 ∧ x10 = p1 / 2 ∧
      x02 = p2 / 3 ∧ x11 = p2 / 3 ∧ x20 = p2 / 3 := by
  refine ⟨h00, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

/-- The six joint cells are forced for every actual edge of these types. -/
theorem edge_joint_type {L : ℕ} {α π : DigitType} {a b q : TritWord L}
    (hedge : Edge α π a b q) (hthirds : π 2 = 3 * α 2) :
    jointCount a b 0 0 = π 0 ∧
      jointCount a b 0 1 = π 1 / 2 ∧
      jointCount a b 1 0 = π 1 / 2 ∧
      jointCount a b 0 2 = π 2 / 3 ∧
      jointCount a b 1 1 = π 2 / 3 ∧
      jointCount a b 2 0 = π 2 / 3 := by
  rcases hedge with ⟨ha, hb, hq, hs⟩
  have hz12 := jointCount_forbidden hs (1 : Fin 3) (2 : Fin 3) (by decide)
  have hz21 := jointCount_forbidden hs (2 : Fin 3) (1 : Fin 3) (by decide)
  have hz22 := jointCount_forbidden hs (2 : Fin 3) (2 : Fin 3) (by decide)
  have hr2 : jointCount a b 2 0 = α 2 := by
    have h := (jointCount_row a b (2 : Fin 3)).trans (ha 2)
    simpa [Fin.sum_univ_three, hz21, hz22] using h
  have hc2 : jointCount a b 0 2 = α 2 := by
    have h := (jointCount_col a b (2 : Fin 3)).trans (hb 2)
    simpa [Fin.sum_univ_three, hz12, hz22] using h
  have hr1 : jointCount a b 1 0 + jointCount a b 1 1 = α 1 := by
    have h := (jointCount_row a b (1 : Fin 3)).trans (ha 1)
    simpa [Fin.sum_univ_three, hz12] using h
  have hc1 : jointCount a b 0 1 + jointCount a b 1 1 = α 1 := by
    have h := (jointCount_col a b (1 : Fin 3)).trans (hb 1)
    simpa [Fin.sum_univ_three, hz21] using h
  have ho0 : jointCount a b 0 0 = π 0 := (output_zero hs).symm.trans (hq 0)
  have ho1 : jointCount a b 0 1 + jointCount a b 1 0 = π 1 :=
    (output_one hs).symm.trans (hq 1)
  have ho2 : jointCount a b 0 2 + jointCount a b 1 1 + jointCount a b 2 0 = π 2 :=
    (output_two hs).symm.trans (hq 2)
  exact joint_type_unique_nat _ _ _ _ _ _ _ _ _ _ _
    ho0 hc2 hr2 hr1 hc1 ho1 ho2 hthirds

def fieldWord {L : ℕ} (p : ℕ) (w : TritWord L) : Fin L → ZMod p :=
  fun i => ((w i).val : ZMod p)

theorem trit_cast_injective {p : ℕ} (hp : 2 < p) :
    Function.Injective (fun x : Fin 3 => (x.val : ZMod p)) := by
  intro a b hab
  apply Fin.ext
  have ha : a.val < p := lt_of_lt_of_le a.isLt (by omega)
  have hb : b.val < p := lt_of_lt_of_le b.isLt (by omega)
  have hv := congrArg ZMod.val hab
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hb] using hv

theorem fieldWord_injective {L p : ℕ} (hp : 2 < p) :
    Function.Injective (fieldWord (L := L) p) := by
  intro a b hab
  funext i
  exact trit_cast_injective hp (congrFun hab i)

theorem fieldWord_sum {L p : ℕ} {a b q : TritWord L}
    (hsum : PointwiseSum a b q) :
    ∀ i, fieldWord p a i + fieldWord p b i = fieldWord p q i := by
  intro i
  unfold fieldWord
  rw [← Nat.cast_add, hsum i]

namespace CertifiedParameters

def pi0 : ℚ := 81204903 / 100000000
def pi1 : ℚ := 15860350 / 100000000
def pi2 : ℚ := 2934747 / 100000000

def alpha0 : ℚ := 90113327 / 100000000
def alpha1 : ℚ := 8908424 / 100000000
def alpha2 : ℚ := 978249 / 100000000

def deficit : ℚ := 268969 / 20000000
def bankY : ℚ := 3632479 / 20000000
def queryZ : ℚ := 7523953 / 100000000
def target192028 : ℚ := 48007 / 25000
def target1921 : ℚ := 1921 / 1000

theorem pi_sum : pi0 + pi1 + pi2 = 1 := by
  norm_num [pi0, pi1, pi2]

theorem alpha_sum : alpha0 + alpha1 + alpha2 = 1 := by
  norm_num [alpha0, alpha1, alpha2]

theorem endpoint_marginals :
    alpha0 = pi0 + pi1 / 2 + pi2 / 3 ∧
    alpha1 = pi1 / 2 + pi2 / 3 ∧ alpha2 = pi2 / 3 := by
  norm_num [alpha0, alpha1, alpha2, pi0, pi1, pi2]

theorem pi_positive : 0 < pi0 ∧ 0 < pi1 ∧ 0 < pi2 := by
  norm_num [pi0, pi1, pi2]

theorem alpha_positive : 0 < alpha0 ∧ 0 < alpha1 ∧ 0 < alpha2 := by
  norm_num [alpha0, alpha1, alpha2]

theorem cutoff_guard : 0 < deficit ∧ deficit < (pi1 + 2 * pi2) / 2 := by
  norm_num [deficit, pi1, pi2]

theorem tilt_guards : 0 < bankY ∧ bankY < 1 ∧ 0 < queryZ ∧ queryZ < 1 := by
  norm_num [bankY, queryZ]

theorem milestone_margin : target192028 < target1921 := by
  norm_num [target192028, target1921]

end CertifiedParameters
end ThreeSum.TernaryJointType
