import Submission.ThreeSum.TernaryCoverGenericProjection
import Submission.ThreeSum.TernaryCoverProjection
import Submission.ThreeSum.TernaryTypeLowerBound
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryCoverUniformProjection
open Finset TernaryJointType TernaryCoverLocal TernaryCoverGenericProjection
open TernaryCoverRegularity TernaryCoverOutputCap TernaryCoverProjection TernaryTypeLowerBound
variable {L p : ℕ} [Fact p.Prime]

private theorem mixed_left_cap (α π : DigitType) {a : ZMod p} (ha : a ≠ 0)
    (hp : 2 < p) (q : Fin L → ZMod p)
    (hP : (vertices L π).card*(2^(π 1)*3^(π 2)) ≤ p^2) :
    (mixedFiber α π a 0 q).card ≤ p := by
  classical
  by_cases hz : (mixedFiber α π a 0 q).card = 0
  · simp [hz]
  obtain ⟨e0, he0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
  have hs : mixedFiber α π a 0 q ⊆ univ.filter (fun e => left e = left e0) := by
    intro e he
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    apply fieldWord_injective hp
    funext i
    have h := ((mem_filter.mp he).2 i).trans ((mem_filter.mp he0).2 i).symm
    simp only [zero_mul, add_zero] at h
    exact mul_left_cancel₀ ha h
  calc
    _ ≤ (univ.filter (fun e : LocalEdge L α π => left e = left e0)).card := card_le_card hs
    _ = Fintype.card (sourceFiber α π (left e0)) := (Fintype.card_subtype _).symm
    _ ≤ p := source_degree_cap (edge_data e0).1 p hP

private theorem mixed_right_cap (α π : DigitType) {b : ZMod p} (hb : b ≠ 0)
    (hp : 2 < p) (q : Fin L → ZMod p)
    (hP : (vertices L π).card*(2^(π 1)*3^(π 2)) ≤ p^2) :
    (mixedFiber α π 0 b q).card ≤ p := by
  classical
  have h : (mixedFiber α π 0 b q).card ≤ (mixedFiber α π b 0 q).card := by
    apply card_le_card_of_injOn swapEdge
    · intro e he
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      intro i
      have h := (mem_filter.mp he).2 i
      change b*fieldRight (p := p) e i + 0*fieldLeft e i = q i
      simpa [zero_mul] using h
    · exact fun _ _ _ _ h => swapEdge_injective α π h
  exact h.trans (mixed_left_cap α π hb hp q hP)

private theorem mixed_sum_cap (α π : DigitType) {a : ZMod p} (ha : a ≠ 0)
    (hp : 2 < p) (q : Fin L → ZMod p)
    (hR : 2^(π 1)*3^(π 2) ≤ p) :
    (mixedFiber α π a a q).card ≤ p := by
  classical
  by_cases hz : (mixedFiber α π a a q).card = 0
  · simp [hz]
  obtain ⟨e0, he0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
  have hs : mixedFiber α π a a q ⊆ univ.filter (fun e => output e = output e0) := by
    intro e he
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    apply fieldWord_injective hp
    funext i
    have h := ((mem_filter.mp he).2 i).trans ((mem_filter.mp he0).2 i).symm
    have heq : fieldLeft (p := p) e i+fieldRight e i =
        fieldLeft e0 i+fieldRight e0 i := by
      apply mul_left_cancel₀ ha
      simpa [mul_add] using h
    simpa [fieldLeft,fieldRight,← fieldWord_sum (p := p) (edge_data e).2.2.2 i,
      ← fieldWord_sum (p := p) (edge_data e0).2.2.2 i] using heq
  calc
    _ ≤ (univ.filter (fun e : LocalEdge L α π => output e = output e0)).card := card_le_card hs
    _ = Fintype.card (outputFiber α π (output e0)) := (Fintype.card_subtype _).symm
    _ ≤ 2^(π 1)*3^(π 2) := outputFiber_card_le α π _ (edge_data e0).2.2.1
    _ ≤ p := hR

private theorem mixed_difference_cap (α π : DigitType)
    (hthirds : π 2 = 3*α 2) (hp : 4 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hab : a+b = 0) (q : Fin L → ZMod p)
    (hchoose : L.choose (π 2/3) ≤ p) :
    (mixedFiber α π a b q).card ≤ p := by
  have hb : b = -a := by linear_combination hab
  have hs : mixedFiber α π a b q ⊆ differenceFiber α π (fun i => q i/a) := by
    intro e he
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    apply (eq_div_iff ha).mpr
    have h := (mem_filter.mp he).2 i
    rw [hb] at h
    linear_combination h
  exact (card_le_card hs).trans ((differenceFiber_card_le α π hthirds hp _).trans hchoose)

private theorem doubled_cap_le_partition (π : DigitType) :
    2^(π 1/2+π 2/3) ≤ 2^(π 1)*3^(π 2) := by
  calc
    _ ≤ 2^(π 1+π 2) := Nat.pow_le_pow_right (by decide) (by omega)
    _ = 2^(π 1)*2^(π 2) := pow_add _ _ _
    _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide) _)

private theorem mixed_double_cap (α π : DigitType)
    (hthirds : π 2 = 3*α 2) (hp : 4 < p) {a b : ZMod p}
    (hb : b ≠ 0) (hab : a = 2*b) (q : Fin L → ZMod p)
    (hR : 2^(π 1)*3^(π 2) ≤ p) :
    (mixedFiber α π a b q).card ≤ p := by
  have hs : mixedFiber α π a b q ⊆ doubledFiber false α π (fun i => q i/b) := by
    intro e he
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    apply (eq_div_iff hb).mpr
    have h := (mem_filter.mp he).2 i
    rw [hab] at h
    simp only [doubledCode, Bool.false_eq_true, ite_false, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    change (2*fieldLeft (p := p) e i+fieldRight e i)*b = q i
    linear_combination h
  exact (card_le_card hs).trans ((doubledFiber_card_le false α π hthirds hp _).trans
    ((doubled_cap_le_partition π).trans hR))

private theorem mixed_half_cap (α π : DigitType)
    (hthirds : π 2 = 3*α 2) (hp : 4 < p) {a b : ZMod p}
    (ha : a ≠ 0) (hab : 2*a = b) (q : Fin L → ZMod p)
    (hR : 2^(π 1)*3^(π 2) ≤ p) :
    (mixedFiber α π a b q).card ≤ p := by
  have hs : mixedFiber α π a b q ⊆ doubledFiber true α π (fun i => q i/a) := by
    intro e he
    apply mem_filter.mpr
    refine ⟨mem_univ _, ?_⟩
    intro i
    apply (eq_div_iff ha).mpr
    have h := (mem_filter.mp he).2 i
    rw [← hab] at h
    simp only [doubledCode, ite_true, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    change (fieldLeft (p := p) e i+2*fieldRight e i)*a = q i
    linear_combination h
  exact (card_le_card hs).trans ((doubledFiber_card_le true α π hthirds hp _).trans
    ((doubled_cap_le_partition π).trans hR))

/-- Uniform full-word scalar projection cap for the actual trinary edge graph.
All combinatorial premises are discharged except the explicit prime-size
and difference-binomial inequalities. -/
theorem mixedFiber_uniform_card_le (α π : DigitType)
    (hthirds : π 2 = 3*α 2) (htotal : π 0+π 1+π 2 = L)
    (hspace : 2*(π 1)+3*(π 2) ≤ L) (hp : 4 < p)
    (hP : (vertices L π).card*(2^(π 1)*3^(π 2)) ≤ p^2)
    (hchoose : L.choose (π 2/3) ≤ p) {a b : ZMod p} (hab : a ≠ 0 ∨ b ≠ 0)
    (q : Fin L → ZMod p) : (mixedFiber α π a b q).card ≤ p := by
  have hR := partition_cap_le_prime π htotal hspace p hP
  by_cases ha : a = 0
  · subst a
    exact mixed_right_cap α π (hab.resolve_left (not_not.mpr rfl)) (by omega) q hP
  by_cases hb : b = 0
  · subst b
    exact mixed_left_cap α π ha (by omega) q hP
  by_cases heq : a = b
  · subst b
    exact mixed_sum_cap α π ha (by omega) q hR
  by_cases hsum : a+b = 0
  · exact mixed_difference_cap α π hthirds hp ha hsum q hchoose
  by_cases hhalf : 2*a = b
  · exact mixed_half_cap α π hthirds hp ha hhalf q hR
  by_cases hdouble : a = 2*b
  · exact mixed_double_cap α π hthirds hp hb hdouble q hR
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have ht : (2 : Fin 3) = 0 := trit_cast_injective (show 2 < p by omega)
      (by norm_num; exact h)
    exact (by decide : (2 : Fin 3) ≠ 0) ht
  exact (mixedFiber_generic_card_le_one α π ha hb h2 hsum heq hhalf hdouble q).trans (by omega)

end ThreeSum.TernaryCoverUniformProjection
