import Submission.ThreeSum.KaratsubaBounds
import Submission.ThreeSum.LightArray
import Submission.ThreeSumApsp.Lang.Lib.Logs

/-!
# Karatsuba as a fixed program in the benchmark language

The procedure below is a finite `Light.Stmt`, independent of the input
capacity. Recursive products share an eight-capacity scratch area. The
linear-time `half` routine avoids an additional persistent power table.
-/

namespace ThreeSum.LightKaratsuba

open Light
open ThreeSum.Karatsuba
open Polynomial

abbrev Len : ℕ := 0
abbrev Left : ℕ := 1
abbrev Right : ℕ := 2
abbrev Out : ℕ := 3
abbrev Work : ℕ := 4
abbrev Half : ℕ := 5
abbrev Unused : ℕ := 6

def joinBody (pLinear pFill : ℕ) : Stmt :=
  .call pLinear [v Work +' k 2 *' v Len, v Work, v Work +' k 2 *' v Len,
    v Len, k 0 -' k 1] Unused ;;
  .call pLinear [v Work +' k 2 *' v Len, v Work +' v Len,
    v Work +' k 2 *' v Len, v Len, k 0 -' k 1] Unused ;;
  .call pFill [v Out, k 2 *' v Len, k 0] Unused ;;
  .call pLinear [v Out, v Work, v Out, v Len, k 1] Unused ;;
  .call pLinear [v Out +' v Half, v Work +' k 2 *' v Len,
    v Out +' v Half, v Len, k 1] Unused ;;
  .call pLinear [v Out +' v Len, v Work +' v Len,
    v Out +' v Len, v Len, k 1] Unused

def recurseBody (pSelf pHalf pLinear pFill : ℕ) : Stmt :=
  .call pHalf [v Len] Half ;;
  .call pLinear [v Left, v Left +' v Half, v Work +' k 3 *' v Len,
    v Half, k 1] Unused ;;
  .call pLinear [v Right, v Right +' v Half,
    v Work +' k 3 *' v Len +' v Half, v Half, k 1] Unused ;;
  .call pSelf [v Half, v Left, v Right, v Work,
    v Work +' k 4 *' v Len] Unused ;;
  .call pSelf [v Half, v Left +' v Half, v Right +' v Half,
    v Work +' v Len, v Work +' k 4 *' v Len] Unused ;;
  .call pSelf [v Half, v Work +' k 3 *' v Len,
    v Work +' k 3 *' v Len +' v Half, v Work +' k 2 *' v Len,
    v Work +' k 4 *' v Len] Unused ;;
  joinBody pLinear pFill

def baseBody : Stmt :=
  .store (v Out) (M (v Left) *' M (v Right)) ;;
  .store (v Out +' k 1) (k 0)

def body (pSelf pHalf pLinear pFill : ℕ) : Stmt :=
  .ite (k 1 <' v Len) (recurseBody pSelf pHalf pLinear pFill) baseBody

structure Procs (P : Program) (pSelf pHalf pLinear pFill : ℕ) : Prop where
  self : P[pSelf]? = some (body pSelf pHalf pLinear pFill)
  half : P[pHalf]? = some halfBody
  linear : P[pLinear]? = some LightArray.linearBody
  fill : P[pFill]? = some fillBody

/-- The conservative recurrence has ample space for all expression and call
costs; a proof of a procedure must discharge this bound through `Ends`. -/
def time : ℕ → ℕ
  | 0 => 30
  | k + 1 => 3 * time k + 2500 * 2 ^ k

theorem time_bound (k : ℕ) : time k + 2500 * 2 ^ k ≤ 2530 * 3 ^ k := by
  induction k with
  | zero => norm_num [time]
  | succ k ih =>
    simp only [time, pow_succ]
    nlinarith

theorem time_le (k : ℕ) : time k ≤ 2530 * 3 ^ k :=
  (Nat.le_add_right _ _).trans (time_bound k)

theorem time_fifth_power (k : ℕ) :
    time k ^ 5 ≤ 2530 ^ 5 * (2 ^ k) ^ 8 := by
  have ht := Nat.pow_le_pow_left (time_le k) 5
  have hp : (3 : ℕ) ^ 5 ≤ 2 ^ 8 := by norm_num
  have hp' := Nat.pow_le_pow_left hp k
  calc
    _ ≤ (2530 * 3 ^ k) ^ 5 := ht
    _ = 2530 ^ 5 * (3 ^ 5) ^ k := by rw [mul_pow, ← pow_mul, Nat.mul_comm k 5, pow_mul]
    _ ≤ 2530 ^ 5 * (2 ^ 8) ^ k := Nat.mul_le_mul_left _ hp'
    _ = _ := by rw [← pow_mul, Nat.mul_comm 8 k, pow_mul]

def ProductAt (μ : ℕ → ℤ) (out n : ℕ) (as bs : List ℤ) : Prop :=
  ∀ j < 2 * n, μ (out + j) = (asPolynomial as * asPolynomial bs).coeff j

/-- Only the output cells below the scratch pointer may change. -/
def Result (μ : ℕ → ℤ) (out n work : ℕ) (as bs : List ℤ) (μ' : ℕ → ℤ) : Prop :=
  ProductAt μ' out n as bs ∧ KeptBut μ μ' work out (2 * n)

def wordBound (n U : ℕ) : ℕ := 128 * n ^ 3 * (U + 1) ^ 2

def window (f : ℕ → ℤ) (offset n j : ℕ) : ℤ :=
  if offset ≤ j ∧ j < offset + n then f (j - offset) else 0

theorem window_bound {f : ℕ → ℤ} {offset n j U : ℕ}
    (hf : ∀ i < n, |f i| ≤ U) : |window f offset n j| ≤ U := by
  unfold window
  split_ifs with hj
  · exact hf _ (by omega)
  · simpa using (Nat.cast_nonneg U : (0 : ℤ) ≤ U)

theorem linear_update_full {μ μ' : ℕ → ℤ} {out src offset n N : ℕ}
    {c : ℤ} {f g : ℕ → ℤ} (hfit : offset + n ≤ N)
    (hOld : ∀ j < N, μ (out + j) = f j)
    (hSrc : ∀ i < n, μ (src + i) = g i)
    (hWrite : ∀ i < n,
      μ' (out + offset + i) = μ (out + offset + i) + c * μ (src + i))
    (hkeep : SameOutside μ μ' (out + offset) n) :
    ∀ j < N, μ' (out + j) = f j + window (fun i => c * g i) offset n j := by
  intro j hj
  unfold window
  split_ifs with hin
  · have hi : j - offset < n := by omega
    have he : out + offset + (j - offset) = out + j := by omega
    have hr := hWrite (j - offset) hi
    rw [he, hOld j hj, hSrc _ hi] at hr
    exact hr
  · have hr := hkeep (out + j) (by omega)
    simpa only [add_zero, hOld j hj] using hr

def joined (μ : ℕ → ℤ) (work n half j : ℕ) : ℤ :=
  window (fun i => μ (work + i)) 0 n j +
  window (fun i => μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i)) half n j +
  window (fun i => μ (work + n + i)) n n j

def joinTime (n : ℕ) : ℕ := 200 * n + 300

section Join

variable {lim : Limits} {P : Program} {d pLinear pFill : ℕ}

theorem join_ends (hLinear : P[pLinear]? = some LightArray.linearBody)
    (hFill : P[pFill]? = some fillBody)
    {μ : ℕ → ℤ} {n half a b out work U : ℕ} {r : ℤ}
    (hn : 0 < n) (hhalf : 2 * half = n)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hout : out + 2 * n ≤ work) (hwork : work + 3 * n ≤ lim.space)
    (hword : 10 * (U : ℤ) ≤ lim.word)
    (hvalues : ∀ i < n, |μ (work + i)| ≤ U ∧ |μ (work + n + i)| ≤ U ∧
      |μ (work + 2 * n + i)| ≤ U)
    (hd : d < lim.depth) :
    Ends lim P d (joinBody pLinear pFill)
      ⟨frame [n, a, b, out, work, half, r], μ⟩ (joinTime n) fun σ' =>
      (∀ j < 2 * n, σ'.mem (out + j) = joined μ work n half j) ∧
        KeptBut μ σ'.mem work out (2 * n) := by
  unfold joinBody
  have hU : (0 : ℤ) ≤ U := Nat.cast_nonneg U
  have hcall1 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ) (srcA := work + 2 * n) (srcB := work) (dst := work + 2 * n)
    (n := n) (U := U) (c := -1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by omega)
    (fun i hi => ⟨(hvalues i hi).2.2, (hvalues i hi).1⟩)
  light_call hcall1 using joinTime, LightArray.linearTime with _ μ₁ ⟨hr₁, hk₁⟩
  have hz01 : ∀ i < n, μ₁ (work + i) = μ (work + i) :=
    fun i hi => hk₁ _ (by omega)
  have hz21 : ∀ i < n, μ₁ (work + n + i) = μ (work + n + i) :=
    fun i hi => hk₁ _ (by omega)
  have hm1 : ∀ i < n, |μ₁ (work + 2 * n + i)| ≤ 2 * (U : ℤ) := by
    intro i hi
    rw [hr₁ i hi]
    have hab := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have hv := hvalues i hi
    simpa only [neg_one_mul, ← sub_eq_add_neg] using
      hab.trans (by omega : |μ (work + 2 * n + i)| + |μ (work + i)| ≤ 2 * (U : ℤ))
  have hcall2 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₁) (srcA := work + 2 * n) (srcB := work + n) (dst := work + 2 * n)
    (n := n) (U := 2 * U) (c := -1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by simpa using hm1 i hi, by rw [hz21 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
  light_call hcall2 using joinTime, LightArray.linearTime with _ μ₂ ⟨hr₂, hk₂⟩
  have hz02 : ∀ i < n, μ₂ (work + i) = μ (work + i) :=
    fun i hi => (hk₂ _ (by omega)).trans (hz01 i hi)
  have hz22 : ∀ i < n, μ₂ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₂ _ (by omega)).trans (hz21 i hi)
  have hmiddle : ∀ i < n, μ₂ (work + 2 * n + i) =
      μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) := by
    intro i hi
    rw [hr₂ i hi, hr₁ i hi, hz21 i hi]
    ring
  have hm2 : ∀ i < n, |μ₂ (work + 2 * n + i)| ≤ 3 * (U : ℤ) := by
    intro i hi
    rw [hmiddle i hi]
    have h₁ := abs_sub (μ (work + 2 * n + i)) (μ (work + i))
    have h₂ := abs_sub (μ (work + 2 * n + i) - μ (work + i)) (μ (work + n + i))
    have hv := hvalues i hi
    omega
  have hfill := fill_meets (d := d + 1) hFill (μ := μ₂) (dst := out) (n := 2 * n)
    (x := 0) hw (by omega)
  light_call hfill using joinTime, LightArray.linearTime with _ μ₃ ⟨hzeroSeg, hk₃⟩
  have hzero : ∀ j < 2 * n, μ₃ (out + j) = 0 := by
    intro j hj
    rw [hzeroSeg j (by simpa using hj)]
    exact List.getElem_replicate ..
  have hz03 : ∀ i < n, μ₃ (work + i) = μ (work + i) :=
    fun i hi => (hk₃ _ (by omega)).trans (hz02 i hi)
  have hz23 : ∀ i < n, μ₃ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₃ _ (by omega)).trans (hz22 i hi)
  have hm3 : ∀ i < n, μ₃ (work + 2 * n + i) = μ₂ (work + 2 * n + i) :=
    fun i hi => hk₃ _ (by omega)
  have hcall3 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₃) (srcA := out) (srcB := work) (dst := out)
    (n := n) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by omega)
    (fun i hi => ⟨by rw [hzero i (by omega), abs_zero]; exact hU,
      by rw [hz03 i hi]; exact (hvalues i hi).1⟩)
  light_call hcall3 using joinTime, LightArray.linearTime with _ μ₄ ⟨hr₄, hk₄⟩
  have hfirst : ∀ j < 2 * n, μ₄ (out + j) = window (fun i => μ (work + i)) 0 n j := by
    have ht := linear_update_full (offset := 0) (by omega : 0 + n ≤ 2 * n)
      hzero hz03 (by simpa only [Nat.add_zero] using hr₄)
      (by simpa only [Nat.add_zero] using hk₄)
    simpa only [one_mul, zero_add] using ht
  have hz24 : ∀ i < n, μ₄ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₄ _ (by omega)).trans (hz23 i hi)
  have hm4 : ∀ i < n, μ₄ (work + 2 * n + i) = μ₂ (work + 2 * n + i) :=
    fun i hi => (hk₄ _ (by omega)).trans (hm3 i hi)
  have hcall4 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₄) (srcA := out + half) (srcB := work + 2 * n) (dst := out + half)
    (n := n) (U := 3 * U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by
      rw [show out + half + i = out + (half + i) by omega, hfirst _ (by omega)]
      have ht := window_bound (offset := 0) (j := half + i) (fun j hj => (hvalues j hj).1)
      push_cast; omega,
      by rw [hm4 i hi]; simpa using hm2 i hi⟩)
  light_call hcall4 using joinTime, LightArray.linearTime with _ μ₅ ⟨hr₅, hk₅⟩
  have hm4' : ∀ i < n, μ₄ (work + 2 * n + i) =
      μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i) :=
    fun i hi => (hm4 i hi).trans (hmiddle i hi)
  have hsecond : ∀ j < 2 * n, μ₅ (out + j) =
      window (fun i => μ (work + i)) 0 n j +
      window (fun i => μ (work + 2 * n + i) - μ (work + i) - μ (work + n + i)) half n j := by
    have ht := linear_update_full (by omega : half + n ≤ 2 * n) hfirst hm4' hr₅ hk₅
    simpa only [one_mul] using ht
  have hz25 : ∀ i < n, μ₅ (work + n + i) = μ (work + n + i) :=
    fun i hi => (hk₅ _ (by omega)).trans (hz24 i hi)
  have hcall5 := LightArray.linear_bounded_meets (d := d + 1) hLinear
    (μ := μ₅) (srcA := out + n) (srcB := work + n) (dst := out + n)
    (n := n) (U := 4 * U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inl rfl) (Or.inr (by omega)) (by norm_num) (by push_cast; omega)
    (fun i hi => ⟨by
      rw [show out + n + i = out + (n + i) by omega, hsecond _ (by omega)]
      have h₁ := window_bound (offset := 0) (j := n + i) (fun j hj => (hvalues j hj).1)
      have h₂ : |window (fun j => μ (work + 2 * n + j) - μ (work + j) -
          μ (work + n + j)) half n (n + i)| ≤ 3 * (U : ℤ) := by
        have hv := window_bound (offset := half) (j := n + i) (U := 3 * U)
          (f := fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j))
          (fun j hj => by rw [← hmiddle j hj]; simpa using hm2 j hj)
        simpa using hv
      have hs := abs_add_le
        (window (fun j => μ (work + j)) 0 n (n + i))
        (window (fun j => μ (work + 2 * n + j) - μ (work + j) - μ (work + n + j)) half n (n + i))
      push_cast; omega,
      by rw [hz25 i hi]; have := (hvalues i hi).2.1; push_cast; omega⟩)
  light_call hcall5 using joinTime, LightArray.linearTime with _ μ₆ ⟨hr₆, hk₆⟩
  constructor
  · have ht := linear_update_full (by omega : n + n ≤ 2 * n) hsecond hz25 hr₆ hk₆
    simpa only [one_mul, joined] using ht
  · intro j hj
    change μ₆ j = μ j
    rw [hk₆ j (by omega), hk₅ j (by omega), hk₄ j (by omega), hk₃ j hj.2,
      hk₂ j (by omega), hk₁ j (by omega)]

end Join

section BaseCase

variable {lim : Limits} {P : Program} {d : ℕ}

theorem base_ends {μ : ℕ → ℤ} {a b out work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a + 1 ≤ lim.space) (hb : b + 1 ≤ lim.space)
    (hout : out + 2 ≤ lim.space) (hmul : |μ a * μ b| ≤ lim.word) :
    Ends lim P d baseBody ⟨frame [1, a, b, out, work], μ⟩ 12 fun σ' =>
      σ'.mem out = μ a * μ b ∧ σ'.mem (out + 1) = 0 ∧
        SameOutside μ σ'.mem out 2 := by
  unfold baseBody
  have hm := abs_le.mp hmul
  light_store out (μ a * μ b)
  light_store (out + 1) 0
  refine ⟨?_, ?_, ?_⟩
  · simp
  · simp
  · intro j hj
    simp only [Function.update_of_ne (by omega : j ≠ out + 1),
      Function.update_of_ne (by omega : j ≠ out)]

theorem base_product {μ μ' : ℕ → ℤ} {a b out : ℕ} {as bs : List ℤ}
    (ha : Seg μ a as) (hb : Seg μ b bs)
    (hAlen : as.length = 1) (hBlen : bs.length = 1)
    (hzero : μ' out = μ a * μ b) (hone : μ' (out + 1) = 0) :
    ProductAt μ' out 1 as bs := by
  have hA := asPolynomial_head hAlen.le
  have hB := asPolynomial_head hBlen.le
  have hhead (xs : List ℤ) : xs.getD 0 0 = xs.headD 0 := by cases xs <;> rfl
  have hreadA : μ a = as.headD 0 := by
    simpa only [Nat.add_zero, hhead] using ha.getD (by omega : 0 < as.length) 0
  have hreadB : μ b = bs.headD 0 := by
    simpa only [Nat.add_zero, hhead] using hb.getD (by omega : 0 < bs.length) 0
  intro j hj
  rw [hA, hB, ← map_mul]
  have hj' : j = 0 ∨ j = 1 := by omega
  rcases hj' with rfl | rfl
  · simpa only [Nat.add_zero, Polynomial.coeff_C_zero, hreadA, hreadB] using hzero
  · simpa only [Polynomial.coeff_C, if_neg (by decide : (1 : ℕ) ≠ 0)] using hone

end BaseCase

@[simp] theorem window_sub (f g : ℕ → ℤ) (offset n j : ℕ) :
    window (fun i => f i - g i) offset n j =
      window f offset n j - window g offset n j := by
  unfold window
  split_ifs <;> simp

theorem ProductAt.window {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (offset j : ℕ) :
    window (fun i => μ (out + i)) offset (2 * n) j =
      (X ^ offset * (asPolynomial as * asPolynomial bs)).coeff j := by
  rw [Polynomial.coeff_X_pow_mul']
  unfold ThreeSum.LightKaratsuba.window
  by_cases ho : offset ≤ j
  · rw [if_pos ho]
    by_cases hj : j < offset + 2 * n
    · rw [if_pos ⟨ho, hj⟩]
      exact hp _ (by omega)
    · rw [if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]
      exact (product_coeff_zero ha hb (by omega : 2 * n ≤ j - offset)).symm
  · rw [if_neg ho, if_neg (by omega : ¬ (offset ≤ j ∧ j < offset + 2 * n))]

/-- The coefficient identity matched by the six actual joining passes. -/
theorem joined_product {μ : ℕ → ℤ} {work n half : ℕ} {as bs : List ℤ}
    (hhalf : 2 * half = n) (ha : as.length = n) (hb : bs.length = n)
    (h0 : ProductAt μ work half (as.take half) (bs.take half))
    (h2 : ProductAt μ (work + n) half (as.drop half) (bs.drop half))
    (hm : ProductAt μ (work + 2 * n) half
      (plus (as.take half) (as.drop half)) (plus (bs.take half) (bs.drop half)))
    (j : ℕ) : joined μ work n half j = (asPolynomial as * asPolynomial bs).coeff j := by
  have ha0 : (as.take half).length ≤ half := by simp
  have hb0 : (bs.take half).length ≤ half := by simp
  have ha1 : (as.drop half).length ≤ half := by simp only [List.length_drop, ha]; omega
  have hb1 : (bs.drop half).length ≤ half := by simp only [List.length_drop, hb]; omega
  have has : (plus (as.take half) (as.drop half)).length ≤ half := by
    simpa only [length_plus] using max_le ha0 ha1
  have hbs : (plus (bs.take half) (bs.drop half)).length ≤ half := by
    simpa only [length_plus] using max_le hb0 hb1
  have hw0 := h0.window ha0 hb0 0 j
  have hw0m := h0.window ha0 hb0 half j
  have hw2m := h2.window ha1 hb1 half j
  have hw2 := h2.window ha1 hb1 n j
  have hwm := hm.window has hbs half j
  rw [hhalf] at hw0 hw0m hw2m hw2 hwm
  unfold joined
  rw [window_sub, window_sub, hw0, hwm, hw0m, hw2m, hw2]
  simp only [pow_zero, one_mul]
  have hp :
      asPolynomial (as.take half) * asPolynomial (bs.take half) +
        (X ^ half * (asPolynomial (plus (as.take half) (as.drop half)) *
          asPolynomial (plus (bs.take half) (bs.drop half))) -
         X ^ half * (asPolynomial (as.take half) * asPolynomial (bs.take half)) -
         X ^ half * (asPolynomial (as.drop half) * asPolynomial (bs.drop half))) +
        X ^ n * (asPolynomial (as.drop half) * asPolynomial (bs.drop half)) =
      asPolynomial as * asPolynomial bs := by
    rw [asPolynomial_plus, asPolynomial_plus]
    conv_rhs => rw [asPolynomial_split half as, asPolynomial_split half bs]
    rw [← hhalf, two_mul, pow_add]
    ring
  simpa only [Polynomial.coeff_add, Polynomial.coeff_sub] using
    congrArg (fun p : Polynomial ℤ => p.coeff j) hp

theorem wordBound_monoU {n U V : ℕ} (hUV : U ≤ V) : wordBound n U ≤ wordBound n V := by
  unfold wordBound
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega : U + 1 ≤ V + 1) 2)

theorem wordBound_child (m U : ℕ) : wordBound m (2 * U) ≤ wordBound (2 * m) U := by
  unfold wordBound
  have hu : (2 * U + 1) ^ 2 ≤ (2 * (U + 1)) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  calc
    _ ≤ 128 * m ^ 3 * (2 * (U + 1)) ^ 2 := Nat.mul_le_mul_left _ hu
    _ ≤ _ := by ring_nf; omega

theorem wordBound_ge_twice (n U : ℕ) (hn : 0 < n) : 2 * U ≤ wordBound n U := by
  have hn3 : 1 ≤ n ^ 3 := Nat.one_le_pow _ _ hn
  have hu : U ≤ (U + 1) ^ 2 := by nlinarith
  have hm := Nat.mul_le_mul_left ((U + 1) ^ 2) hn3
  unfold wordBound
  nlinarith

theorem ten_temp_le_word (n U : ℕ) (hn : 0 < n) :
    10 * (4 * n * U ^ 2) ≤ wordBound n U := by
  have hn3 : n ≤ n ^ 3 := by nlinarith [Nat.one_le_pow 2 n hn]
  have hu : U ^ 2 ≤ (U + 1) ^ 2 := Nat.pow_le_pow_left (by omega) 2
  have hm := Nat.mul_le_mul hn3 hu
  unfold wordBound
  nlinarith

theorem linear_plus_segment {μ μ' : ℕ → ℤ} {a b out n : ℕ} {as bs : List ℤ}
    (ha : Seg μ a as) (hb : Seg μ b bs) (hAlen : as.length = n) (hBlen : bs.length = n)
    (hwrite : ∀ i < n, μ' (out + i) = μ (a + i) + 1 * μ (b + i)) :
    Seg μ' out (plus as bs) := by
  intro i hi
  have hin : i < n := by simpa only [length_plus, hAlen, hBlen, max_self] using hi
  rw [← List.getD_eq_getElem _ 0 hi, plus_getD,
    ← ha.getD (by omega : i < as.length) 0, ← hb.getD (by omega : i < bs.length) 0]
  simpa only [one_mul] using hwrite i hin

theorem ProductAt.bound {μ : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ} {U : ℤ}
    (hp : ProductAt μ out n as bs) (ha : as.length ≤ n) (hb : bs.length ≤ n)
    (hA : CoeffBound as U) (hB : CoeffBound bs U) :
    ∀ j < 2 * n, |μ (out + j)| ≤ 2 * (n : ℤ) * U ^ 2 := by
  intro j hj
  rw [hp j hj]
  exact product_coeff_bound ha hb hA hB j

theorem ProductAt.congr {μ μ' : ℕ → ℤ} {out n : ℕ} {as bs : List ℤ}
    (hp : ProductAt μ out n as bs)
    (he : ∀ j < 2 * n, μ' (out + j) = μ (out + j)) :
    ProductAt μ' out n as bs := fun j hj => (he j hj).trans (hp j hj)

section RecursiveExecution

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}

set_option maxHeartbeats 2000000 in
theorem recurse_ends (C : Procs P pSelf pHalf pLinear pFill)
    {d k m a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hmPow : m = 2 ^ k) (hw : (lim.space : ℤ) ≤ lim.word)
    (hAlen : as.length = 2 * m) (hBlen : bs.length = 2 * m)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 * m ≤ work) (hbf : b + 2 * m ≤ work)
    (hof : out + 2 * (2 * m) ≤ work) (hspace : work + 8 * (2 * m) ≤ lim.space)
    (hword : (wordBound (2 * m) U : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (ih : ∀ (a' b' out' work' U' : ℕ) (as' bs' : List ℤ) (μ' : ℕ → ℤ),
      as'.length = m → bs'.length = m → Seg μ' a' as' → Seg μ' b' bs' →
      CoeffBound as' (U' : ℤ) → CoeffBound bs' (U' : ℤ) →
      a' + m ≤ work' → b' + m ≤ work' → out' + 2 * m ≤ work' →
      work' + 8 * m ≤ lim.space → (wordBound m U' : ℤ) ≤ lim.word →
      Meets lim P pSelf (d + 1) [m, a', b', out', work'] μ' (time k)
        (fun _ μ'' => Result μ' out' m work' as' bs' μ'')) :
    Ends lim P d (recurseBody pSelf pHalf pLinear pFill)
      ⟨frame [2 * m, a, b, out, work], μ⟩ (time (k + 1) - 4)
      (fun σ' => Result μ out (2 * m) work as bs σ'.mem) := by
  have hm : 0 < m := hmPow ▸ Nat.pow_pos (by decide)
  have hAU0 := hA.take m
  have hAU1 := hA.drop m
  have hBU0 := hB.take m
  have hBU1 := hB.drop m
  have hAs : CoeffBound (plus (as.take m) (as.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hAU0.plus hAU1
  have hBs : CoeffBound (plus (bs.take m) (bs.drop m)) ((2 * U : ℕ) : ℤ) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat, two_mul, Nat.cast_add] using hBU0.plus hBU1
  have ha0 : (as.take m).length = m := by simp only [List.length_take, hAlen]; omega
  have ha1 : (as.drop m).length = m := by simp only [List.length_drop, hAlen]; omega
  have hb0 : (bs.take m).length = m := by simp only [List.length_take, hBlen]; omega
  have hb1 : (bs.drop m).length = m := by simp only [List.length_drop, hBlen]; omega
  have has : (plus (as.take m) (as.drop m)).length = m := by simp only [length_plus, ha0, ha1, max_self]
  have hbs : (plus (bs.take m) (bs.drop m)).length = m := by simp only [length_plus, hb0, hb1, max_self]
  have hword2 : 2 * (U : ℤ) ≤ lim.word := by
    have hh : 2 * (U : ℤ) ≤ wordBound (2 * m) U := by
      exact_mod_cast wordBound_ge_twice (2 * m) U (by omega)
    exact hh.trans hword
  have hchild2 : (wordBound m (2 * U) : ℤ) ≤ lim.word := by
    have hc : (wordBound m (2 * U) : ℤ) ≤ wordBound (2 * m) U := by
      exact_mod_cast wordBound_child m U
    exact hc.trans hword
  have hchild1 : (wordBound m U : ℤ) ≤ lim.word := by
    have hc : (wordBound m U : ℤ) ≤ wordBound m (2 * U) := by
      exact_mod_cast wordBound_monoU (n := m) (by omega : U ≤ 2 * U)
    exact hc.trans hchild2
  have hhalfeq : (2 * m + 1) / 2 = m := by omega
  have hhalfword : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.word := by
    have hh : ((2 * m + 1 : ℕ) : ℤ) ≤ lim.space := by exact_mod_cast (show 2 * m + 1 ≤ lim.space by omega)
    exact hh.trans hw
  have hhalf := half_meets (lim := lim) (d := d + 1) C.half μ (h := 2 * m) hhalfword
  simp only [halfTime, hhalfeq] at hhalf
  unfold recurseBody
  light_call hhalf using time with _ μ₀ ⟨rfl, hμ₀⟩
  subst μ₀
  have hsA0 := hAseg.take m
  have hsA1 := hAseg.drop m
  have hsumA := LightArray.linear_bounded_meets (d := d + 1) C.linear
    (μ := μ) (srcA := a) (srcB := a + m) (dst := work + 3 * (2 * m))
    (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (by norm_num) hword2
    (fun i hi => ⟨by rw [hsA0.getD (by omega) 0]; exact hAU0 i,
      by rw [hsA1.getD (by omega) 0]; exact hAU1 i⟩)
  light_call hsumA using time, LightArray.linearTime with _ μ₁ ⟨hrA, hkA⟩
  have hsuma := linear_plus_segment hsA0 hsA1 ha0 ha1 hrA
  have hBseg1 : Seg μ₁ b bs := hBseg.congr (fun i hi => hkA _ (by omega))
  have hsB0 := hBseg1.take m
  have hsB1 := hBseg1.drop m
  have hsumB := LightArray.linear_bounded_meets (d := d + 1) C.linear
    (μ := μ₁) (srcA := b) (srcB := b + m) (dst := work + 3 * (2 * m) + m)
    (n := m) (U := U) (c := 1) hw (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (by norm_num) hword2
    (fun i hi => ⟨by rw [hsB0.getD (by omega) 0]; exact hBU0 i,
      by rw [hsB1.getD (by omega) 0]; exact hBU1 i⟩)
  light_call hsumB using time, LightArray.linearTime with _ μ₂ ⟨hrB, hkB⟩
  have hsumb := linear_plus_segment hsB0 hsB1 hb0 hb1 hrB
  have hsuma2 : Seg μ₂ (work + 3 * (2 * m)) (plus (as.take m) (as.drop m)) :=
    hsuma.congr (fun i hi => hkB _ (by omega))
  have hAseg2 : Seg μ₂ a as := hAseg.congr (fun i hi => (hkB _ (by omega)).trans (hkA _ (by omega)))
  have hBseg2 : Seg μ₂ b bs := hBseg1.congr (fun i hi => hkB _ (by omega))
  have hprod0 := ih a b work (work + 4 * (2 * m)) U (as.take m) (bs.take m) μ₂
    ha0 hb0 (hAseg2.take m) (hBseg2.take m) hAU0 hBU0
    (by omega) (by omega) (by omega) (by omega) hchild1
  light_call hprod0 using time, LightArray.linearTime with _ μ₃ ⟨hp0, hkp0⟩
  have hAseg3 : Seg μ₃ a as := hAseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hBseg3 : Seg μ₃ b bs := hBseg2.congr (fun i hi => hkp0 _ ⟨by omega, by omega⟩)
  have hprod2 := ih (a + m) (b + m) (work + 2 * m) (work + 4 * (2 * m)) U
    (as.drop m) (bs.drop m) μ₃ ha1 hb1 (hAseg3.drop m) (hBseg3.drop m) hAU1 hBU1
    (by omega) (by omega) (by omega) (by omega) hchild1
  light_call hprod2 using time, LightArray.linearTime with _ μ₄ ⟨hp2, hkp2⟩
  have hp04 : ProductAt μ₄ work m (as.take m) (bs.take m) :=
    hp0.congr (fun j hj => hkp2 _ ⟨by omega, by omega⟩)
  have hsuma4 : Seg μ₄ (work + 3 * (2 * m)) (plus (as.take m) (as.drop m)) :=
    hsuma2.congr (fun i hi =>
      (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hsumb4 : Seg μ₄ (work + 3 * (2 * m) + m) (plus (bs.take m) (bs.drop m)) :=
    hsumb.congr (fun i hi =>
      (hkp2 _ ⟨by omega, by omega⟩).trans (hkp0 _ ⟨by omega, by omega⟩))
  have hprodm := ih (work + 3 * (2 * m)) (work + 3 * (2 * m) + m)
    (work + 2 * (2 * m)) (work + 4 * (2 * m)) (2 * U)
    (plus (as.take m) (as.drop m)) (plus (bs.take m) (bs.drop m)) μ₄
    has hbs hsuma4 hsumb4 hAs hBs
    (by omega) (by omega) (by omega) (by omega) hchild2
  light_call hprodm using time, LightArray.linearTime with _ μ₅ ⟨hpm, hkpm⟩
  have hp05 : ProductAt μ₅ work m (as.take m) (bs.take m) :=
    hp04.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have hp25 : ProductAt μ₅ (work + 2 * m) m (as.drop m) (bs.drop m) :=
    hp2.congr (fun j hj => hkpm _ ⟨by omega, by omega⟩)
  have htword : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ lim.word := by
    have hh : 10 * ((4 * (2 * m) * U ^ 2 : ℕ) : ℤ) ≤ wordBound (2 * m) U := by
      exact_mod_cast ten_temp_le_word (2 * m) U (by omega)
    exact hh.trans hword
  have htemp : ∀ i < 2 * m,
      |μ₅ (work + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
      |μ₅ (work + 2 * m + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) ∧
      |μ₅ (work + 2 * (2 * m) + i)| ≤ (4 * (2 * m) * U ^ 2 : ℕ) := by
    intro i hi
    have h₀ := hp05.bound ha0.le hb0.le hAU0 hBU0 i hi
    have h₂ := hp25.bound ha1.le hb1.le hAU1 hBU1 i hi
    have hₘ := hpm.bound has.le hbs.le hAs hBs i hi
    push_cast at hₘ ⊢
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    constructor
    · nlinarith [sq_nonneg (U : ℤ)]
    · nlinarith
  refine (join_ends C.linear C.fill (n := 2 * m) (half := m) (U := 4 * (2 * m) * U ^ 2)
    (by omega) rfl hw hof (by omega) htword htemp hd).mono
      (by light_time [time, joinTime, LightArray.linearTime]) ?_
  intro σ' hj
  constructor
  · intro j hjj
    exact (hj.1 j hjj).trans (joined_product rfl hAlen hBlen hp05 hp25 hpm j)
  · intro j hjj
    rw [hj.2 j hjj, hkpm j ⟨by omega, by omega⟩, hkp2 j ⟨by omega, by omega⟩,
      hkp0 j ⟨by omega, by omega⟩, hkB j (by omega), hkA j (by omega)]

end RecursiveExecution

section CompleteProcedure

variable {lim : Limits} {P : Program} {pSelf pHalf pLinear pFill : ℕ}

/-- Correctness, preservation, word safety, call depth, and actual Light
step count for the fixed recursive multiplication procedure. -/
theorem meets (C : Procs P pSelf pHalf pLinear pFill)
    (hw : (lim.space : ℤ) ≤ lim.word)
    {k a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (wordBound (2 ^ k) U : ℤ) ≤ lim.word) :
    ∀ d, d + k + 1 ≤ lim.depth →
      Meets lim P pSelf d [2 ^ k, a, b, out, work] μ (time k)
        (fun _ μ' => Result μ out (2 ^ k) work as bs μ') := by
  induction k generalizing a b out work U as bs μ with
  | zero =>
    simp only [pow_zero] at hAlen hBlen haf hbf hof hspace hword ⊢
    intro d hd
    have hvA : |μ a| ≤ (U : ℤ) := by
      have hr := hAseg.getD (by omega : 0 < as.length) 0
      simpa only [← hr, Nat.add_zero] using hA 0
    have hvB : |μ b| ≤ (U : ℤ) := by
      have hr := hBseg.getD (by omega : 0 < bs.length) 0
      simpa only [← hr, Nat.add_zero] using hB 0
    have hp : |μ a * μ b| ≤ (U : ℤ) ^ 2 := by
      rw [abs_mul, pow_two]
      exact mul_le_mul hvA hvB (abs_nonneg _) (Nat.cast_nonneg U)
    have hpw : (U : ℤ) ^ 2 ≤ lim.word := by
      have hh : 10 * ((4 * 1 * U ^ 2 : ℕ) : ℤ) ≤ wordBound 1 U := by
        exact_mod_cast ten_temp_le_word 1 U (by decide)
      push_cast at hh
      nlinarith only [hh, hword, sq_nonneg (U : ℤ)]
    have hbases := base_ends (P := P) (d := d) (a := a) (b := b) (out := out) (work := work)
      hw (by omega) (by omega) (by omega) (hp.trans hpw)
    refine Meets.of_body C.self ?_
    unfold body
    refine Ends.iteLast (fun hc => False.elim (by simpa using hc)) (fun _ => ?_)
      (hT := by simp [time, Cond.cost, Expr.cost])
    refine hbases.mono (by norm_num [time, Cond.cost, Expr.cost]) ?_
    intro σ' hr
    exact ⟨base_product hAseg hBseg hAlen hBlen hr.1 hr.2.1,
      fun j hj => hr.2.2 j hj.2⟩
  | succ k ih =>
    intro d hd
    have hp : 0 < (2 : ℕ) ^ k := Nat.pow_pos (by decide)
    have hpZ : (0 : ℤ) < (2 : ℤ) ^ k := pow_pos (by norm_num) k
    have he : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ, Nat.mul_comm]
    have heZ : (2 : ℤ) ^ (k + 1) = 2 * ((2 ^ k : ℕ) : ℤ) := by
      push_cast
      rw [pow_succ, mul_comm]
    rw [he] at hAlen hBlen haf hbf hof hspace hword ⊢
    rw [heZ]
    refine Meets.of_body C.self ?_
    unfold body
    refine Ends.iteLast (fun _ => ?_) (fun hc => ?_)
      (hT := by light_time [time])
    · exact recurse_ends C rfl hw hAlen hBlen hAseg hBseg hA hB
        haf hbf hof hspace hword (by omega)
        (fun a' b' out' work' U' as' bs' μ' hla hlb hsa hsb hba hbb
          hfa hfb hfo hsp hwo =>
          ih hla hlb hsa hsb hba hbb hfa hfb hfo hsp hwo (d + 1) (by omega))
    · have hfalse : ¬ (1 : ℤ) < 2 * (2 : ℤ) ^ k := by simpa using hc
      have hone : (1 : ℤ) ≤ (2 : ℤ) ^ k := hpZ
      omega

/-- One fixed finite program, independent of all input sizes and values. -/
def program : Program := [body 0 1 2 3, halfBody, LightArray.linearBody, fillBody]

theorem program_procs : Procs program 0 1 2 3 := ⟨rfl, rfl, rfl, rfl⟩

theorem program_meets (hw : (lim.space : ℤ) ≤ lim.word)
    {k a b out work U : ℕ} {as bs : List ℤ} {μ : ℕ → ℤ}
    (hAlen : as.length = 2 ^ k) (hBlen : bs.length = 2 ^ k)
    (hAseg : Seg μ a as) (hBseg : Seg μ b bs)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (haf : a + 2 ^ k ≤ work) (hbf : b + 2 ^ k ≤ work)
    (hof : out + 2 * 2 ^ k ≤ work) (hspace : work + 8 * 2 ^ k ≤ lim.space)
    (hword : (wordBound (2 ^ k) U : ℤ) ≤ lim.word)
    (d : ℕ) (hd : d + k + 1 ≤ lim.depth) :
    Meets lim program 0 d [2 ^ k, a, b, out, work] μ (time k)
      (fun _ μ' => Result μ out (2 ^ k) work as bs μ') :=
  meets program_procs hw hAlen hBlen hAseg hBseg hA hB haf hbf hof hspace hword d hd

end CompleteProcedure

end ThreeSum.LightKaratsuba
