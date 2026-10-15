import Submission.ThreeSum.TernaryCoverLocal
import Mathlib.Data.Finset.Powerset

/-! # The exceptional difference-projection fiber

Within the six admissible trinary cells, the difference projection merges
only `(0,0)` and `(1,1)`.  Every edge in one prescribed difference fiber is
therefore determined by its set of `(1,1)` positions.  The forced joint type
fixes the cardinality of that set, giving an actual binomial fiber bound.
-/

noncomputable section
namespace ThreeSum.TernaryCoverProjection

open Finset TernaryJointType TernaryCoverLocal

def differenceCode (a b : Fin 3) : ℕ := a.val + (2 - b.val)

theorem differenceCode_lt (a b : Fin 3) : differenceCode a b < 5 := by
  have ha := a.isLt
  unfold differenceCode
  omega

theorem differenceCode_cast (p : ℕ) (a b : Fin 3) :
    (differenceCode a b : ZMod p) = (a.val : ZMod p) - (b.val : ZMod p) + 2 := by
  have hb : b.val ≤ 2 := by have h := b.isLt; omega
  unfold differenceCode
  rw [Nat.cast_add, Nat.cast_sub hb]
  norm_num
  ring

theorem differenceCode_eq_of_field {p : ℕ} (hp : 4 < p) (a b c d : Fin 3)
    (heq : (a.val : ZMod p) - (b.val : ZMod p) =
      (c.val : ZMod p) - (d.val : ZMod p)) :
    differenceCode a b = differenceCode c d := by
  have ha : differenceCode a b < p := (differenceCode_lt a b).trans_le (by omega)
  have hc : differenceCode c d < p := (differenceCode_lt c d).trans_le (by omega)
  have he : (differenceCode a b : ZMod p) = (differenceCode c d : ZMod p) := by
    rw [differenceCode_cast, differenceCode_cast, heq]
  have hv := congrArg ZMod.val he
  simpa only [ZMod.val_natCast_of_lt ha, ZMod.val_natCast_of_lt hc] using hv

/-- Apart from the merged zero-difference cells, the difference identifies
each admissible ordered digit pair. -/
theorem cell_unique (a b c d : Fin 3)
    (hab : a.val + b.val ≤ 2) (hcd : c.val + d.val ≤ 2)
    (heq : differenceCode a b = differenceCode c d)
    (hmark : (a = 1 ∧ b = 1) ↔ (c = 1 ∧ d = 1)) :
    a = c ∧ b = d := by
  fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [differenceCode] at *

def marked {L : ℕ} {α π : DigitType} (e : LocalEdge L α π) : Finset (Fin L) :=
  univ.filter fun i => left e i = 1 ∧ right e i = 1

theorem marked_card {L : ℕ} {α π : DigitType} (e : LocalEdge L α π)
    (hthirds : π 2 = 3 * α 2) :
    (marked e).card = π 2 / 3 := by
  have hcount := (edge_joint_type (edge_data e) hthirds).2.2.2.2.1
  have he : (marked e).card = jointCount (left e) (right e) 1 1 := by
    unfold marked
    rw [card_eq_sum_ones, sum_filter]
    rfl
  exact he.trans hcount

def differenceFiber {L p : ℕ} (α π : DigitType) (q : Fin L → ZMod p) :
    Finset (LocalEdge L α π) :=
  univ.filter fun e => ∀ i, fieldLeft (p := p) e i - fieldRight e i = q i

theorem differenceFiber_card_le {L p : ℕ} (α π : DigitType)
    (hthirds : π 2 = 3 * α 2) (hp : 4 < p) (q : Fin L → ZMod p) :
    (differenceFiber α π q).card ≤ L.choose (π 2 / 3) := by
  classical
  have hcount : (differenceFiber α π q).card ≤
      ((univ : Finset (Fin L)).powersetCard (π 2 / 3)).card := by
    apply card_le_card_of_injOn marked
    · intro e _
      exact mem_powersetCard.mpr ⟨subset_univ _, marked_card e hthirds⟩
    · intro e he f hf hmark
      apply endpoint_injective α π
      apply Prod.ext
      · funext i
        have hproj := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
        have hcode := differenceCode_eq_of_field hp (left e i) (right e i)
          (left f i) (right f i) hproj
        have hmarked : (left e i = 1 ∧ right e i = 1) ↔
            (left f i = 1 ∧ right f i = 1) := by
          have hi := congrArg (fun s : Finset (Fin L) => i ∈ s) hmark
          simpa [marked] using hi
        have hs := (edge_data e).2.2.2 i
        have ht := (edge_data f).2.2.2 i
        exact (cell_unique (left e i) (right e i) (left f i) (right f i)
          (by have h := (output e i).isLt; omega)
          (by have h := (output f i).isLt; omega) hcode hmarked).1
      · funext i
        have hproj := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
        have hcode := differenceCode_eq_of_field hp (left e i) (right e i)
          (left f i) (right f i) hproj
        have hmarked : (left e i = 1 ∧ right e i = 1) ↔
            (left f i = 1 ∧ right f i = 1) := by
          have hi := congrArg (fun s : Finset (Fin L) => i ∈ s) hmark
          simpa [marked] using hi
        have hs := (edge_data e).2.2.2 i
        have ht := (edge_data f).2.2.2 i
        exact (cell_unique (left e i) (right e i) (left f i) (right f i)
          (by have h := (output e i).isLt; omega)
          (by have h := (output f i).isLt; omega) hcode hmarked).2
  simpa [card_powersetCard] using hcount

def doubledCode (swap : Bool) (a b : Fin 3) : ℕ :=
  if swap then a.val + 2 * b.val else 2 * a.val + b.val

def doubledMark (swap : Bool) (a b : Fin 3) : Prop :=
  if swap then a = 2 ∧ b = 0 else a = 0 ∧ b = 2

theorem doubledCode_lt (swap : Bool) (a b : Fin 3) (hab : a.val + b.val ≤ 2) :
    doubledCode swap a b < 5 := by
  cases swap <;> simp only [doubledCode, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem doubled_cell_unique (swap : Bool) (a b c d : Fin 3)
    (hab : a.val + b.val ≤ 2) (hcd : c.val + d.val ≤ 2)
    (heq : doubledCode swap a b = doubledCode swap c d)
    (hmark : doubledMark swap a b ↔ doubledMark swap c d) :
    a = c ∧ b = d := by
  cases swap <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    norm_num [doubledCode, doubledMark, Fin.ext_iff] at *

private theorem doubled_indicator (swap : Bool) (a b : Fin 3)
    (hab : a.val + b.val ≤ 2) :
    (if doubledCode swap a b = 2 then 1 else 0 : ℕ) =
      if swap then (if a = 0 ∧ b = 1 then 1 else 0) + (if a = 2 ∧ b = 0 then 1 else 0)
      else (if a = 1 ∧ b = 0 then 1 else 0) + (if a = 0 ∧ b = 2 then 1 else 0) := by
  cases swap <;> fin_cases a <;> fin_cases b <;> norm_num [doubledCode, Fin.ext_iff] at *

def doubledMarked {L : ℕ} {α π : DigitType} (swap : Bool) (e : LocalEdge L α π) : Finset (Fin L) := by
  classical
  exact univ.filter fun i => doubledMark swap (left e i) (right e i)

def doubledAmbiguous {L : ℕ} {α π : DigitType} (swap : Bool) (e : LocalEdge L α π) : Finset (Fin L) :=
  univ.filter fun i => doubledCode swap (left e i) (right e i) = 2

theorem doubledAmbiguous_card {L : ℕ} {α π : DigitType} (swap : Bool) (e : LocalEdge L α π)
    (hthirds : π 2 = 3 * α 2) :
    (doubledAmbiguous swap e).card = π 1 / 2 + π 2 / 3 := by
  have htype := edge_joint_type (edge_data e) hthirds
  have hind (i : Fin L) := doubled_indicator swap (left e i) (right e i)
    (by have hs := (edge_data e).2.2.2 i; have hq := (output e i).isLt; omega)
  unfold doubledAmbiguous
  rw [card_eq_sum_ones, sum_filter]
  simp_rw [hind]
  cases swap
  · simp only [Bool.false_eq_true, ite_false, sum_add_distrib]
    change jointCount (left e) (right e) 1 0 + jointCount (left e) (right e) 0 2 = _
    rw [htype.2.2.1, htype.2.2.2.1]
  · simp only [ite_true, sum_add_distrib]
    change jointCount (left e) (right e) 0 1 + jointCount (left e) (right e) 2 0 = _
    rw [htype.2.1, htype.2.2.2.2.2]

def doubledFiber {L p : ℕ} (swap : Bool) (α π : DigitType) (q : Fin L → ZMod p) :
    Finset (LocalEdge L α π) :=
  univ.filter fun e => ∀ i, (doubledCode swap (left e i) (right e i) : ZMod p) = q i

theorem doubledFiber_card_le {L p : ℕ} (swap : Bool) (α π : DigitType)
    (hthirds : π 2 = 3 * α 2) (hp : 4 < p) (q : Fin L → ZMod p) :
    (doubledFiber swap α π q).card ≤ 2 ^ (π 1 / 2 + π 2 / 3) := by
  classical
  have hcode {e f : LocalEdge L α π} (he : e ∈ doubledFiber swap α π q)
      (hf : f ∈ doubledFiber swap α π q) (i : Fin L) :
      doubledCode swap (left e i) (right e i) = doubledCode swap (left f i) (right f i) := by
    have heq := ((mem_filter.mp he).2 i).trans ((mem_filter.mp hf).2 i).symm
    have hlo (g : LocalEdge L α π) : doubledCode swap (left g i) (right g i) < p := by
      apply (doubledCode_lt swap _ _ ?_).trans_le (by omega)
      have hs := (edge_data g).2.2.2 i
      have hq := (output g i).isLt
      omega
    have hv := congrArg ZMod.val heq
    simpa only [ZMod.val_natCast_of_lt (hlo e), ZMod.val_natCast_of_lt (hlo f)] using hv
  by_cases hz : (doubledFiber swap α π q).card = 0
  · simp [hz]
  obtain ⟨e0, he0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
  have hcount : (doubledFiber swap α π q).card ≤ (doubledAmbiguous swap e0).powerset.card := by
    apply card_le_card_of_injOn (doubledMarked swap)
    · intro e he
      apply mem_powerset.mpr
      intro i hi
      have hm := (mem_filter.mp hi).2
      have hc : doubledCode swap (left e i) (right e i) = 2 := by
        cases swap <;> simp_all [doubledMark, doubledCode]
      exact mem_filter.mpr ⟨mem_univ _, (hcode he he0 i).symm.trans hc⟩
    · intro e he f hf hmarked
      apply endpoint_injective α π
      have hpair (i : Fin L) : left e i = left f i ∧ right e i = right f i := by
        have hm : doubledMark swap (left e i) (right e i) ↔
            doubledMark swap (left f i) (right f i) := by
          have hi := congrArg (fun s : Finset (Fin L) => i ∈ s) hmarked
          simpa [doubledMarked] using hi
        apply doubled_cell_unique swap _ _ _ _ ?_ ?_ (hcode he hf i) hm
        · have hs := (edge_data e).2.2.2 i; have hq := (output e i).isLt; omega
        · have hs := (edge_data f).2.2.2 i; have hq := (output f i).isLt; omega
      exact Prod.ext (funext fun i => (hpair i).1) (funext fun i => (hpair i).2)
  simpa [card_powerset, doubledAmbiguous_card swap e0 hthirds] using hcount

end ThreeSum.TernaryCoverProjection
