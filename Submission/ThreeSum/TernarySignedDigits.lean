import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Finset.Card
import Mathlib.Tactic

/-! Original signed integer digits and a literal binary carry relation. -/
namespace ThreeSum.TernarySignedDigits
open Finset
open scoped BigOperators

def quotient (b x j : ℕ) : ℕ := x/b^j
def digit (b x j : ℕ) : ℕ := quotient b x j%b
def carryNat (b x y j : ℕ) : ℕ := quotient b (x+y) j-(quotient b x j+quotient b y j)

theorem digit_lt {b : ℕ} (hb : 0 < b) (x j : ℕ) : digit b x j < b := Nat.mod_lt _ hb
theorem quotient_step (b x j : ℕ) : quotient b x j/b=quotient b x (j+1) := by
  unfold quotient
  rw [Nat.div_div_eq_div_mul,pow_succ]

theorem digit_quotient (b x j : ℕ) :
    (digit b x j : ℤ)=(quotient b x j : ℤ)-(b : ℤ)*(quotient b x (j+1) : ℤ) := by
  have hh : (digit b x j : ℤ)+(b : ℤ)*((quotient b x j/b : ℕ) : ℤ)=(quotient b x j : ℤ) := by
    exact_mod_cast Nat.mod_add_div (quotient b x j) b
  rw [quotient_step] at hh
  omega

theorem carryNat_le_one (b x y j : ℕ) : carryNat b x y j ≤ 1 := by
  have h := Nat.add_div_le_div_add_div_add_one x y (b^j)
  unfold carryNat quotient
  omega

theorem carryNat_cast (b x y j : ℕ) :
    (carryNat b x y j : ℤ)=(quotient b (x+y) j : ℤ)-(quotient b x j : ℤ)-(quotient b y j : ℤ) := by
  have hl := Nat.add_div_le_add_div x y (b^j)
  change quotient b x j+quotient b y j ≤ quotient b (x+y) j at hl
  unfold carryNat
  rw [Nat.cast_sub hl,Nat.cast_add]
  ring

theorem addition_digit_carry (b x y j : ℕ) :
    (digit b x j : ℤ)+(digit b y j : ℤ)+(carryNat b x y j : ℤ)=
      (digit b (x+y) j : ℤ)+(b : ℤ)*(carryNat b x y (j+1) : ℤ) := by
  simp only [digit_quotient,carryNat_cast]
  ring

@[simp] theorem carryNat_zero (b x y : ℕ) : carryNat b x y 0=0 := by
  simp [carryNat,quotient]

theorem carryNat_terminal {b x y J : ℕ} (h : x+y < b^J) : carryNat b x y J=0 := by
  unfold carryNat quotient
  rw [Nat.div_eq_of_lt h]
  exact Nat.zero_sub _

def evaluate (b J : ℕ) (f : ℕ → ℤ) : ℤ := ∑ j ∈ range J, f j*(b : ℤ)^j

theorem evaluate_digits (b x J : ℕ) :
    evaluate b J (fun j => (digit b x j : ℤ))=(x : ℤ)-(b : ℤ)^J*(quotient b x J : ℤ) := by
  induction J with
  | zero => simp [evaluate,quotient]
  | succ J ih =>
    simp only [evaluate,sum_range_succ] at ih ⊢
    rw [ih,digit_quotient,pow_succ]
    ring

theorem evaluate_digits_of_lt {b x J : ℕ} (h : x < b^J) :
    evaluate b J (fun j => (digit b x j : ℤ))=(x : ℤ) := by
  rw [evaluate_digits]
  simp [quotient,Nat.div_eq_of_lt h]

theorem evaluate_carry (b J : ℕ) (c : ℕ → ℤ) :
    evaluate b J (fun j => (b : ℤ)*c (j+1)-c j)=(b : ℤ)^J*c J-c 0 := by
  induction J with
  | zero => simp [evaluate]
  | succ J ih =>
    simp only [evaluate,sum_range_succ] at ih ⊢
    rw [ih,pow_succ]
    ring

abbrev CarryWord (J : ℕ) := Fin (J+1) → Fin 2
def carryAt {J : ℕ} (c : CarryWord J) (j : ℕ) : ℤ :=
  if hj : j<J+1 then ((c ⟨j,hj⟩).val : ℤ) else 0
def ValidCarry {J : ℕ} (c : CarryWord J) : Prop := carryAt c 0=0 ∧ carryAt c J=0
instance {J : ℕ} (c : CarryWord J) : Decidable (ValidCarry c) := by unfold ValidCarry; infer_instance

def canonicalCarry (b x y J : ℕ) : CarryWord J := fun j =>
  ⟨carryNat b x y j,by have := carryNat_le_one b x y j; omega⟩

theorem carryAt_canonical {b x y J j : ℕ} (hj : j ≤ J) :
    carryAt (canonicalCarry b x y J) j=(carryNat b x y j : ℤ) := by
  simp [carryAt,canonicalCarry,show j<J+1 by omega]

theorem canonicalCarry_valid {b x y J : ℕ} (h : x+y < b^J) :
    ValidCarry (canonicalCarry b x y J) := by
  constructor
  · rw [carryAt_canonical (by omega),carryNat_zero]; rfl
  · rw [carryAt_canonical le_rfl,carryNat_terminal h]; rfl

def DigitRelation (b J x y z : ℕ) (c : CarryWord J) : Prop :=
  ∀ j : Fin J, (digit b x j : ℤ)+(digit b y j : ℤ)+carryAt c j=
    (digit b z j : ℤ)+(b : ℤ)*carryAt c (j+1)

theorem addition_has_carry {b J x y z : ℕ} (h : x+y=z) (hz : z<b^J) :
    ∃ c : CarryWord J, ValidCarry c ∧ DigitRelation b J x y z c := by
  refine ⟨canonicalCarry b x y J,canonicalCarry_valid (by omega),?_⟩
  intro j
  rw [carryAt_canonical (by omega),carryAt_canonical (by omega),← h]
  exact addition_digit_carry b x y j

theorem carry_implies_addition {b J x y z : ℕ} (hx : x<b^J) (hy : y<b^J) (hz : z<b^J)
    {c : CarryWord J} (hc : ValidCarry c) (hd : DigitRelation b J x y z c) : x+y=z := by
  have hs : evaluate b J (fun j => (digit b x j : ℤ)+(digit b y j : ℤ))=
      evaluate b J (fun j => (digit b z j : ℤ)+((b : ℤ)*carryAt c (j+1)-carryAt c j)) := by
    apply sum_congr rfl
    intro j hj
    have hh := hd ⟨j,mem_range.mp hj⟩
    congr 1
    dsimp at hh
    linarith
  have hadd (f g : ℕ → ℤ) : evaluate b J (fun j => f j+g j)=evaluate b J f+evaluate b J g := by
    simp only [evaluate,add_mul,sum_add_distrib]
  rw [hadd,hadd,evaluate_digits_of_lt hx,evaluate_digits_of_lt hy,evaluate_digits_of_lt hz,
    evaluate_carry,hc.1,hc.2] at hs
  norm_num at hs
  exact_mod_cast hs

theorem addition_iff_carry {b J x y z : ℕ} (hx : x<b^J) (hy : y<b^J) (hz : z<b^J) :
    x+y=z ↔ ∃ c : CarryWord J, ValidCarry c ∧ DigitRelation b J x y z c := by
  constructor
  · exact fun h => addition_has_carry h hz
  · rintro ⟨c,hc,hd⟩
    exact carry_implies_addition hx hy hz hc hd

end ThreeSum.TernarySignedDigits
