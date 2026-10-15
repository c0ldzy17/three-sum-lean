import Submission.ThreeSum.TernaryParameters
import Submission.ThreeSum.TernaryJointType
import Submission.ThreeSum.TernaryCoverHashes
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Analysis.Convex.Slope
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryProjectionEntropy
open Finset

variable {Ω : Type*} [DecidableEq Ω]

/-- The three sum levels contain respectively one, two, and three cells. -/
structure SixKeys (Ω : Type*) where
  zero : Ω
  one0 : Ω
  one1 : Ω
  two0 : Ω
  two1 : Ω
  two2 : Ω

def atom (w : ℝ) (k q : Ω) : ℝ := if k = q then w else 0

def law (k : SixKeys Ω) (w0 w1 w2 : ℝ) (q : Ω) : ℝ :=
  atom w0 k.zero q + (atom w1 k.one0 q + atom w1 k.one1 q) +
  (atom w2 k.two0 q + atom w2 k.two1 q + atom w2 k.two2 q)

def DistinctLevels (k : SixKeys Ω) : Prop :=
  k.one0 ≠ k.one1 ∧ k.two0 ≠ k.two1 ∧ k.two0 ≠ k.two2 ∧ k.two1 ≠ k.two2

private theorem atom_nonneg {w : ℝ} (hw : 0 ≤ w) (k q : Ω) : 0 ≤ atom w k q := by
  unfold atom
  split <;> positivity

private theorem one_mass_le {w : ℝ} (hw : 0 ≤ w) (k q : Ω) : atom w k q ≤ w := by
  unfold atom
  split <;> simp_all

private theorem two_mass_le {w : ℝ} (hw : 0 ≤ w) {k l : Ω} (hkl : k ≠ l) (q : Ω) :
    atom w k q + atom w l q ≤ w := by
  unfold atom
  split_ifs <;> simp_all

private theorem three_mass_le {w : ℝ} (hw : 0 ≤ w) {k l m : Ω}
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) (q : Ω) :
    atom w k q + atom w l q + atom w m q ≤ w := by
  unfold atom
  split_ifs <;> simp_all

private theorem atom_pair_le {w : ℝ} (hw : 0 ≤ w) (k : Ω) {q r : Ω} (hqr : q ≠ r) :
    atom w k q + atom w k r ≤ w := by
  unfold atom
  split_ifs <;> simp_all

private theorem three_pair_le {w : ℝ} (hw : 0 ≤ w) {k l m : Ω}
    (hkl : k ≠ l) (hkm : k ≠ m) (hlm : l ≠ m) {q r : Ω} (hqr : q ≠ r) :
    (atom w k q + atom w l q + atom w m q) +
    (atom w k r + atom w l r + atom w m r) ≤ 2 * w := by
  unfold atom
  split_ifs <;> simp_all <;> linarith

theorem law_nonneg (k : SixKeys Ω) {w0 w1 w2 : ℝ}
    (h0 : 0 ≤ w0) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) (q : Ω) :
    0 ≤ law k w0 w1 w2 q := by
  unfold law
  exact add_nonneg (add_nonneg (atom_nonneg h0 _ _)
    (add_nonneg (atom_nonneg h1 _ _) (atom_nonneg h1 _ _)))
    (add_nonneg (add_nonneg (atom_nonneg h2 _ _) (atom_nonneg h2 _ _))
      (atom_nonneg h2 _ _))

theorem law_one_bin (k : SixKeys Ω) (hk : DistinctLevels k) {w0 w1 w2 : ℝ}
    (h0 : 0 ≤ w0) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) (q : Ω) :
    law k w0 w1 w2 q ≤ w0 + w1 + w2 := by
  unfold law
  linarith [one_mass_le h0 k.zero q, two_mass_le h1 hk.1 q,
    three_mass_le h2 hk.2.1 hk.2.2.1 hk.2.2.2 q]

theorem law_two_bins (k : SixKeys Ω) (hk : DistinctLevels k) {w0 w1 w2 : ℝ}
    (h0 : 0 ≤ w0) (h1 : 0 ≤ w1) (h2 : 0 ≤ w2) {q r : Ω} (hqr : q ≠ r) :
    law k w0 w1 w2 q + law k w0 w1 w2 r ≤ w0 + 2*w1 + 2*w2 := by
  unfold law
  linarith [atom_pair_le h0 k.zero hqr, atom_pair_le h1 k.one0 hqr,
    atom_pair_le h1 k.one1 hqr,
    three_pair_le h2 hk.2.1 hk.2.2.1 hk.2.2.2 hqr]

theorem law_total [Fintype Ω] (k : SixKeys Ω) (w0 w1 w2 : ℝ) :
    ∑ q, law k w0 w1 w2 q = w0 + 2*w1 + 3*w2 := by
  simp [law, atom, sum_add_distrib, eq_comm]
  ring


private theorem chord_le {f : ℝ → ℝ} (hf : ConcaveOn ℝ (Set.Ici 0) f)
    {u v x : ℝ} (hu : 0 ≤ u) (huv : u < v) (hux : u ≤ x) (hxv : x ≤ v) :
    f u + (f v - f u) / (v-u) * (x-u) ≤ f x := by
  have hd : 0 < v-u := sub_pos.mpr huv
  have ha : 0 ≤ (v-x)/(v-u) := div_nonneg (sub_nonneg.mpr hxv) hd.le
  have hb : 0 ≤ (x-u)/(v-u) := div_nonneg (sub_nonneg.mpr hux) hd.le
  have hab : (v-x)/(v-u) + (x-u)/(v-u) = 1 := by field_simp; ring
  have harg : (v-x)/(v-u)*u + (x-u)/(v-u)*v = x := by field_simp; ring
  have h := hf.2 hu (by change 0 ≤ v; linarith : v ∈ Set.Ici 0) ha hb hab
  simp only [smul_eq_mul] at h
  rw [harg] at h
  have he : f u + (f v-f u)/(v-u)*(x-u) =
      (v-x)/(v-u)*f u + (x-u)/(v-u)*f v := by
    field_simp
    ring
  rw [he]
  exact h

private theorem sum_hockey_eq [Fintype Ω] (p : Ω → ℝ) (t : ℝ) :
    ∑ q, max 0 (p q-t) =
      (∑ q ∈ univ.filter (fun q => t < p q), p q) -
      ((univ.filter (fun q => t < p q)).card : ℝ)*t := by
  have h (q : Ω) : max 0 (p q-t) = if t < p q then p q-t else 0 := by
    split_ifs with h
    · exact max_eq_right (by linarith)
    · exact max_eq_left (by linarith)
  simp_rw [h]
  rw [← sum_filter]
  simp [sum_sub_distrib]

private theorem subset_sum_le [Fintype Ω] {p : Ω → ℝ} (hp : ∀ q, 0 ≤ p q)
    (S : Finset Ω) : ∑ q ∈ S, p q ≤ ∑ q, p q :=
  sum_le_sum_of_subset_of_nonneg (subset_univ _) (by intros; exact hp _)

private theorem cap_one [Fintype Ω] {p : Ω → ℝ} {a : ℝ}
    (hp : ∀ q, p q ≤ a) {S : Finset Ω} (hc : S.card = 1) : ∑ q ∈ S, p q ≤ a := by
  obtain ⟨q, rfl⟩ := card_eq_one.mp hc
  simpa using hp q

private theorem cap_two [Fintype Ω] {p : Ω → ℝ} {a : ℝ}
    (hp : ∀ q r, q ≠ r → p q+p r ≤ a) {S : Finset Ω} (hc : S.card = 2) :
    ∑ q ∈ S, p q ≤ a := by
  obtain ⟨q, r, hqr, rfl⟩ := card_eq_two.mp hc
  simpa [hqr] using hp q r hqr

/-- The two nontrivial hockey-stick inequalities for three-point majorization. -/
theorem hockey_bounds [Fintype Ω] {p : Ω → ℝ} {a0 a1 a2 : ℝ}
    (hp : ∀ q, 0 ≤ p q) (htotal : ∑ q, p q = a0+a1+a2)
    (hmax : ∀ q, p q ≤ a0) (hpair : ∀ q r, q ≠ r → p q+p r ≤ a0+a1)
    (h2 : 0 ≤ a2) (h21 : a2 ≤ a1) (h10 : a1 ≤ a0) :
    (∑ q, max 0 (p q-a2)) ≤ a0+a1-2*a2 ∧
    (∑ q, max 0 (p q-a1)) ≤ a0-a1 := by
  have hsub (S : Finset Ω) : ∑ q ∈ S, p q ≤ a0+a1+a2 := by
    simpa [htotal] using subset_sum_le hp S
  have hc2 (S : Finset Ω) : ∑ q ∈ S, p q ≤ a0+a1-2*a2+(S.card : ℝ)*a2 := by
    by_cases hz : S.card = 0
    · have hs : S = ∅ := card_eq_zero.mp hz
      simp [hs]
      linarith
    by_cases ho : S.card = 1
    · have h := cap_one hmax ho
      norm_num [ho]
      linarith
    by_cases ht : S.card = 2
    · have h := cap_two hpair ht
      norm_num [ht]
      linarith
    have hn : 3 ≤ S.card := by omega
    have hn' : (3 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hn
    nlinarith [hsub S]
  have hc1 (S : Finset Ω) : ∑ q ∈ S, p q ≤ a0-a1+(S.card : ℝ)*a1 := by
    by_cases hz : S.card = 0
    · have hs : S = ∅ := card_eq_zero.mp hz
      simp [hs]
      linarith
    by_cases ho : S.card = 1
    · have h := cap_one hmax ho
      norm_num [ho]
      linarith
    by_cases ht : S.card = 2
    · have h := cap_two hpair ht
      norm_num [ht]
      linarith
    have hn : 3 ≤ S.card := by omega
    have hn' : (3 : ℝ) ≤ (S.card : ℝ) := by exact_mod_cast hn
    nlinarith [hsub S]
  constructor
  · rw [sum_hockey_eq]
    linarith [hc2 (univ.filter (fun q => a2 < p q))]
  · rw [sum_hockey_eq]
    linarith [hc1 (univ.filter (fun q => a1 < p q))]


/-- A self-contained three-point form of Schur concavity. -/
theorem sum_concave_three [Fintype Ω] {f : ℝ → ℝ}
    (hf : ConcaveOn ℝ (Set.Ici 0) f) (hf0 : f 0 = 0)
    {p : Ω → ℝ} {a0 a1 a2 : ℝ}
    (hp : ∀ q, 0 ≤ p q) (htotal : ∑ q, p q = a0+a1+a2)
    (hmax : ∀ q, p q ≤ a0) (hpair : ∀ q r, q ≠ r → p q+p r ≤ a0+a1)
    (ha2 : 0 < a2) (ha21 : a2 < a1) (ha10 : a1 < a0) :
    f a0 + f a1 + f a2 ≤ ∑ q, f (p q) := by
  let s0 := f a2 / a2
  let s1 := (f a1-f a2)/(a1-a2)
  let s2 := (f a0-f a1)/(a0-a1)
  have hs10 : s1 ≤ s0 := by
    have h := hf.slope_anti_adjacent (by simp) (by change 0 ≤ a1; linarith) ha2 ha21
    simpa [s0, s1, hf0] using h
  have hs21 : s2 ≤ s1 :=
    hf.slope_anti_adjacent ha2.le (by change 0 ≤ a0; linarith) ha21 ha10
  have hn2 : a2 ≠ 0 := ne_of_gt ha2
  have hn21 : a1-a2 ≠ 0 := ne_of_gt (sub_pos.mpr ha21)
  have hn10 : a0-a1 ≠ 0 := ne_of_gt (sub_pos.mpr ha10)
  have hpoint (x : ℝ) (hx0 : 0 ≤ x) (hx : x ≤ a0) :
      s0*x-(s0-s1)*max 0 (x-a2)-(s1-s2)*max 0 (x-a1) ≤ f x := by
    by_cases hx2 : x ≤ a2
    · have h := chord_le hf (u := 0) (by norm_num) ha2 hx0 hx2
      rw [max_eq_left (by linarith), max_eq_left (by linarith)]
      simpa [s0, hf0] using h
    by_cases hx1 : x ≤ a1
    · have h := chord_le hf ha2.le ha21 (by linarith) hx1
      rw [max_eq_right (by linarith), max_eq_left (by linarith)]
      have he : s0*x-(s0-s1)*(x-a2)-(s1-s2)*0 =
          f a2+(f a1-f a2)/(a1-a2)*(x-a2) := by
        dsimp [s0, s1, s2]
        field_simp
        ring
      rw [he]
      exact h
    · have h := chord_le hf (by linarith) ha10 (by linarith) hx
      rw [max_eq_right (by linarith), max_eq_right (by linarith)]
      have he : s0*x-(s0-s1)*(x-a2)-(s1-s2)*(x-a1) =
          f a1+(f a0-f a1)/(a0-a1)*(x-a1) := by
        dsimp [s0, s1, s2]
        field_simp
        ring
      rw [he]
      exact h
  have hsum := sum_le_sum (fun q (_ : q ∈ (univ : Finset Ω)) => hpoint (p q) (hp q) (hmax q))
  simp only [sum_sub_distrib, ← mul_sum] at hsum
  rw [htotal] at hsum
  obtain ⟨hh2, hh1⟩ := hockey_bounds hp htotal hmax hpair ha2.le ha21.le ha10.le
  have hm2 := mul_le_mul_of_nonneg_left hh2 (sub_nonneg.mpr hs10)
  have hm1 := mul_le_mul_of_nonneg_left hh1 (sub_nonneg.mpr hs21)
  have he : s0*(a0+a1+a2)-(s0-s1)*(a0+a1-2*a2)-(s1-s2)*(a0-a1) =
      f a0+f a1+f a2 := by
    dsimp [s0, s1, s2]
    field_simp
    ring
  rw [← he]
  linarith

/-- Entropy cannot decrease below the nested-level endpoint marginal. -/
theorem six_cell_entropy [Fintype Ω] (k : SixKeys Ω) (hk : DistinctLevels k)
    {w0 w1 w2 : ℝ} (h0 : 0 < w0) (h1 : 0 < w1) (h2 : 0 < w2) :
    Real.negMulLog (w0+w1+w2) + Real.negMulLog (w1+w2) + Real.negMulLog w2 ≤
      ∑ q, Real.negMulLog (law k w0 w1 w2 q) := by
  apply sum_concave_three Real.concaveOn_negMulLog Real.negMulLog_zero
    (law_nonneg k h0.le h1.le h2.le)
  · rw [law_total]
    ring
  · exact law_one_bin k hk h0.le h1.le h2.le
  · intro q r hqr
    have h := law_two_bins k hk h0.le h1.le h2.le hqr
    linarith
  · exact h2
  · linarith
  · linarith


section Projection
variable {K : Type*} [Field K] [DecidableEq K]

def projectionKeys (a b : K) : SixKeys K := ⟨0,b,a,2*b,a+b,2*a⟩

theorem projection_distinct_levels {a b : K} (hab : a ≠ b) (h2 : (2 : K) ≠ 0) :
    DistinctLevels (projectionKeys a b) := by
  constructor
  · exact Ne.symm hab
  constructor
  · intro h
    apply hab
    change 2*b = a+b at h
    linear_combination -h
  constructor
  · intro h
    apply hab
    change 2*b = 2*a at h
    exact (mul_left_cancel₀ h2 h).symm
  · intro h
    apply hab
    change a+b = 2*a at h
    linear_combination -h

open TernaryParameters

def projectionLaw (a b : K) : K → ℝ := law (projectionKeys a b) pi0 (pi1/2) (pi2/3)

def projectionEntropy [Fintype K] (a b : K) : ℝ :=
  (∑ q, Real.negMulLog (projectionLaw a b q)) / Real.log 2

theorem projection_entropy_ge_endpoint [Fintype K] {a b : K}
    (hab : a ≠ b) (h2 : (2 : K) ≠ 0) : Halpha ≤ projectionEntropy a b := by
  have h := six_cell_entropy (projectionKeys a b) (projection_distinct_levels hab h2)
    pi_positive.1 (div_pos pi_positive.2.1 (by norm_num : (0 : ℝ) < 2))
    (div_pos pi_positive.2.2 (by norm_num : (0 : ℝ) < 3))
  rw [← alpha_formulas.1, ← alpha_formulas.2.1, ← alpha_formulas.2.2] at h
  unfold Halpha projectionEntropy projectionLaw
  apply (div_le_div_iff_of_pos_right log_two_pos).mpr
  simpa [Real.negMulLog, sub_eq_add_neg, add_assoc, ← alpha_formulas.2.2] using h

/-- The concrete entropy threshold used in the paired rank increment bound. -/
theorem unequal_projection_entropy [Fintype K] {a b : K}
    (hab : a ≠ b) (h2 : (2 : K) ≠ 0) :
    (Hpi+partitionEntropy)/2 < projectionEntropy a b :=
  lt_of_lt_of_le analytic_admissibility.2.2.2.2.1 (projection_entropy_ge_endpoint hab h2)

private theorem sparse_three_entropy [Fintype Ω] {k0 k1 k2 : Ω}
    (h01 : k0 ≠ k1) (h02 : k0 ≠ k2) (h12 : k1 ≠ k2) (w0 w1 w2 : ℝ) :
    (∑ q, Real.negMulLog (atom w0 k0 q + atom w1 k1 q + atom w2 k2 q)) =
    Real.negMulLog w0 + Real.negMulLog w1 + Real.negMulLog w2 := by
  have he (q : Ω) : Real.negMulLog (atom w0 k0 q + atom w1 k1 q + atom w2 k2 q) =
      atom (Real.negMulLog w0) k0 q + atom (Real.negMulLog w1) k1 q +
      atom (Real.negMulLog w2) k2 q := by
    unfold atom
    split_ifs <;> simp_all
  simp_rw [he]
  simp [sum_add_distrib, atom, eq_comm]

theorem equal_projection_entropy [Fintype K] {a : K}
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) : projectionEntropy a a = Hpi := by
  have h02 : (0 : K) ≠ 2*a := by
    intro h
    exact ha ((mul_eq_zero.mp h.symm).resolve_left h2)
  have h12 : a ≠ 2*a := by
    intro h
    apply ha
    linear_combination -h
  have he (q : K) : projectionLaw a a q =
      atom pi0 0 q + atom pi1 a q + atom pi2 (2*a) q := by
    unfold projectionLaw law projectionKeys atom
    simp only [SixKeys.zero, SixKeys.one0, SixKeys.one1, SixKeys.two0, SixKeys.two1, SixKeys.two2]
    have htwice : a+a = 2*a := by ring
    rw [htwice]
    split_ifs <;> ring
  unfold projectionEntropy
  simp_rw [he]
  rw [sparse_three_entropy (Ne.symm ha) h02 h12]
  simp [Hpi, Real.negMulLog, sub_eq_add_neg, add_assoc]

theorem equal_nonzero_projection_entropy [Fintype K] {a : K}
    (ha : a ≠ 0) (h2 : (2 : K) ≠ 0) :
    (Hpi+partitionEntropy)/2 < projectionEntropy a a := by
  rw [equal_projection_entropy ha h2]
  linarith [analytic_admissibility.2.2.1]

/-- Every nonzero scalar projection satisfies the concrete paired-rank threshold. -/
theorem nonzero_projection_entropy [Fintype K] {a b : K}
    (hab : a ≠ 0 ∨ b ≠ 0) (h2 : (2 : K) ≠ 0) :
    (Hpi+partitionEntropy)/2 < projectionEntropy a b := by
  by_cases heq : a = b
  · subst b
    have ha : a ≠ 0 := hab.elim id id
    exact equal_nonzero_projection_entropy ha h2
  · exact unequal_projection_entropy heq h2

end Projection
end ThreeSum.TernaryProjectionEntropy
