import Submission.ThreeSum.LightOutputDecodeDivide
import Mathlib.Data.Int.Order.Lemmas

/-! # Actual logarithmic signed exact division for homogeneous Euler recovery -/

namespace ThreeSum.LightTernaryDivide

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def body (pDivide : ℕ) : Stmt :=
  .ite (v 0 <' k 0)
    (.call pDivide [k 0 -' v 0,v 1,v 2] 3 ;;
      .set 0 (k 0 -' v 3))
    (.call pDivide [v 0,v 1,v 2] 0)

def time (V : ℕ) : ℕ := LightOutputDecodeDivide.budget V + 50

theorem meets {pMain pDivide Mo V fr : ℕ} {a q : ℤ}
    (hmain : P[pMain]? = some (body pDivide))
    (hdivide : P[pDivide]? = some LightOutputDecodeDivide.body)
    (μ : ℕ → ℤ) (F : Light.Emod.Pre lim Mo V fr)
    (ha : a.natAbs ≤ V) (heq : a = (Mo : ℤ) * q) (hd : d+1 ≤ lim.depth) :
    Meets lim P pMain d [a,Mo,fr] μ (time V)
      (fun r μ' => r = q ∧ Kept μ μ' fr) := by
  light_facts F
  have hM : (0 : ℤ) < (Mo : ℤ) := by exact_mod_cast F.mod_pos
  have hn : (Mo : ℤ) ≠ 0 := ne_of_gt hM
  have habs : |a| ≤ (V : ℤ) := by
    rw [← Int.natCast_natAbs]
    exact_mod_cast ha
  apply Meets.of_body hmain
  unfold body time
  light_if hneg hnonneg : a < 0 using LightOutputDecodeDivide.budget
  · have hna : ((-a).toNat : ℤ) = -a := Int.toNat_of_nonneg (by omega)
    have hnav : (-a).toNat ≤ V := by
      have hab : -a ≤ (V : ℤ) := by omega
      omega
    have hc := LightOutputDecodeDivide.bounded_meets (d := d+1)
      (a := (-a).toNat) (μ := μ) hdivide F hnav
    have hquot : (((-a).toNat / Mo : ℕ) : ℤ) = -q := by
      rw [Int.natCast_ediv, hna, heq]
      rw [show -((Mo : ℤ)*q) = (Mo : ℤ)*(-q) by ring,
        Int.mul_ediv_cancel_left _ hn]
    have hqabs : |q| ≤ |a| := by
      rw [heq, abs_mul]
      have hMp : 1 ≤ |(Mo : ℤ)| := by rw [abs_of_pos hM]; exact_mod_cast F.mod_pos
      nlinarith [abs_nonneg q]
    light_call hc using hna,LightOutputDecodeDivide.budget with r μ' ⟨hr,hkeep⟩
    have hrq : r = -q := hr.trans hquot
    have hqb := abs_le.mp (hqabs.trans habs)
    have hrb : |r| ≤ (V : ℤ) := by
      rw [hrq,abs_neg]
      exact hqabs.trans habs
    have hrbounds := abs_le.mp hrb
    light_set q using hrq,LightOutputDecodeDivide.budget
    exact ⟨rfl,hkeep⟩
  · have ha0 : 0 ≤ a := by omega
    have hpa : (a.toNat : ℤ) = a := Int.toNat_of_nonneg ha0
    have hpav : a.toNat ≤ V := by
      have hab : a ≤ (V : ℤ) := by omega
      omega
    have hc := LightOutputDecodeDivide.bounded_meets (d := d+1)
      (a := a.toNat) (μ := μ) hdivide F hpav
    have hquot : ((a.toNat / Mo : ℕ) : ℤ) = q := by
      rw [Int.natCast_ediv, hpa, heq, Int.mul_ediv_cancel_left _ hn]
    light_call hc using hpa,LightOutputDecodeDivide.budget with r μ' ⟨hr,hkeep⟩
    exact ⟨hr.trans hquot,hkeep⟩

def program : Program := [body 1,LightOutputDecodeDivide.body]

theorem time_bound (V : ℕ) : time V ≤ 200*(Nat.log 2 (V+1)+2) := by
  unfold time LightOutputDecodeDivide.budget
  omega

end ThreeSum.LightTernaryDivide
