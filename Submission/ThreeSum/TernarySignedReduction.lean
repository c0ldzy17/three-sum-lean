import Submission.ThreeSum.TernarySignedDigits
import Mathlib.Data.ZMod.Basic

/-! Original colored signed values, finite carries, and both source tags. -/
namespace ThreeSum.TernarySignedReduction
open TernarySignedDigits Finset

def shiftOne (U : ℕ) (x : ℤ) : ℕ := (x+U).toNat
def shiftTwo (U : ℕ) (x : ℤ) : ℕ := (x+2*U).toNat

theorem shiftOne_cast {U : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) :
    (shiftOne U x : ℤ)=x+U := by
  have hl := (abs_le.mp hx).1
  exact Int.toNat_of_nonneg (by omega)

theorem shiftTwo_cast {U : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) :
    (shiftTwo U x : ℤ)=x+2*U := by
  have hl := (abs_le.mp hx).1
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  exact Int.toNat_of_nonneg (by omega)

theorem shiftOne_lt {U b J : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) (hcap : 4*U<b^J) :
    shiftOne U x<b^J := by
  have hu := (abs_le.mp hx).2
  have hh : (4 : ℤ)*U < (b^J : ℕ) := by exact_mod_cast hcap
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  have hc := shiftOne_cast hx
  exact_mod_cast (by omega : (shiftOne U x : ℤ)<(b^J : ℕ))

theorem shiftTwo_lt {U b J : ℕ} {x : ℤ} (hx : |x| ≤ (U : ℤ)) (hcap : 4*U<b^J) :
    shiftTwo U x<b^J := by
  have hu := (abs_le.mp hx).2
  have hh : (4 : ℤ)*U < (b^J : ℕ) := by exact_mod_cast hcap
  have hU : (0 : ℤ) ≤ U := Int.natCast_nonneg U
  have hc := shiftTwo_cast hx
  exact_mod_cast (by omega : (shiftTwo U x : ℤ)<(b^J : ℕ))

theorem shifted_addition_iff {U : ℕ} {a b c : ℤ}
    (ha : |a| ≤ (U : ℤ)) (hb : |b| ≤ (U : ℤ)) (hc : |c| ≤ (U : ℤ)) :
    shiftOne U b+shiftOne U a=shiftTwo U c ↔ c-b=a := by
  have hA := shiftOne_cast ha
  have hB := shiftOne_cast hb
  have hC := shiftTwo_cast hc
  constructor
  · intro h
    have hi : (shiftOne U b : ℤ)+(shiftOne U a : ℤ)=(shiftTwo U c : ℤ) := by exact_mod_cast h
    omega
  · intro h
    have hi : (shiftOne U b : ℤ)+(shiftOne U a : ℤ)=(shiftTwo U c : ℤ) := by omega
    exact_mod_cast hi

def carryCatalog (J : ℕ) : Finset (CarryWord J) := univ.filter ValidCarry
@[simp] theorem mem_carryCatalog {J : ℕ} (c : CarryWord J) : c ∈ carryCatalog J ↔ ValidCarry c := by
  simp [carryCatalog]

theorem valid_last {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) : c (Fin.last J)=0 := by
  have h := hc.2
  simp only [carryAt,show J<J+1 by omega,dif_pos] at h
  apply Fin.ext
  exact Int.ofNat_inj.mp h

theorem carryCatalog_card (J : ℕ) : (carryCatalog J).card ≤ 2^J := by
  let takeCarry : CarryWord J → (Fin J → Fin 2) := fun c i => c i.castSucc
  have h : (carryCatalog J).card ≤ (univ : Finset (Fin J → Fin 2)).card := by
    apply card_le_card_of_injOn takeCarry
    · intro c hc; exact mem_univ _
    · intro c hc d hd he
      funext i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · rw [valid_last (mem_carryCatalog _ |>.mp hc),valid_last (mem_carryCatalog _ |>.mp hd)]
      · exact congrFun he j
  simpa using h

abbrev Coordinate (J : ℕ) := Sum (Fin J) Bool
def leftRaw (U radix J : ℕ) (b : ℤ) : Coordinate J → ℤ
  | .inl j => -(digit radix (shiftOne U b) j : ℤ)
  | .inr false => 1
  | .inr true => 0
def rightRaw (U radix J : ℕ) (c : ℤ) : Coordinate J → ℤ
  | .inl j => (digit radix (shiftTwo U c) j : ℤ)
  | .inr false => 0
  | .inr true => 1
def requesterRaw (U radix J : ℕ) (a : ℤ) (carry : CarryWord J) : Coordinate J → ℤ
  | .inl j => (digit radix (shiftOne U a) j : ℤ)-
      ((radix : ℤ)*carryAt carry (j+1)-carryAt carry j)
  | .inr _ => 1

theorem tagged_relation_iff (U radix J : ℕ) (a b c : ℤ) (carry : CarryWord J) :
    (∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k) ↔
      DigitRelation radix J (shiftOne U b) (shiftOne U a) (shiftTwo U c) carry := by
  constructor
  · intro h j
    have hh := h (.inl j)
    simp only [leftRaw,rightRaw,requesterRaw] at hh
    linarith
  · intro h k
    cases k with
    | inl j =>
      have hh := h j
      simp only [leftRaw,rightRaw,requesterRaw]
      linarith
    | inr t => cases t <;> norm_num [leftRaw,rightRaw,requesterRaw]

/-- All original signed inputs, both directions, with literal finite carries. -/
theorem original_difference_iff {U radix J : ℕ} {a b c : ℤ}
    (ha : |a| ≤ (U : ℤ)) (hb : |b| ≤ (U : ℤ)) (hc : |c| ≤ (U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ carry ∈ carryCatalog J,
      ∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k := by
  rw [← shifted_addition_iff ha hb hc,
    addition_iff_carry (shiftOne_lt hb hcap) (shiftOne_lt ha hcap) (shiftTwo_lt hc hcap)]
  constructor
  · rintro ⟨carry,hv,hd⟩
    exact ⟨carry,mem_carryCatalog _ |>.mpr hv,(tagged_relation_iff _ _ _ _ _ _ _).mpr hd⟩
  · rintro ⟨carry,hv,hd⟩
    exact ⟨carry,mem_carryCatalog _ |>.mp hv,(tagged_relation_iff _ _ _ _ _ _ _).mp hd⟩

end ThreeSum.TernarySignedReduction
