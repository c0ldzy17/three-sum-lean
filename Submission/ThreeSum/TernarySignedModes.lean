import Submission.ThreeSum.TernarySignedReduction
import Mathlib.Data.Int.Lemmas

/-! Bounded original digit rows, exact field lifting, and physical mode soundness. -/
namespace ThreeSum.TernarySignedModes
open TernarySignedDigits TernarySignedReduction Finset

theorem carryAt_bounds {J : ℕ} (c : CarryWord J) (j : ℕ) :
    0 ≤ carryAt c j ∧ carryAt c j ≤ 1 := by
  unfold carryAt
  split_ifs with h
  · have hh := (c ⟨j,h⟩).isLt
    constructor <;> omega
  · norm_num

theorem leftRaw_abs {U radix J : ℕ} (hb : 1 < radix) (b : ℤ) (k : Coordinate J) :
    |leftRaw U radix J b k| ≤ (radix : ℤ) := by
  cases k with
  | inl j =>
    simp only [leftRaw,abs_neg,Int.abs_natCast]
    exact_mod_cast (digit_lt (by omega) _ _).le
  | inr t => cases t <;> norm_num [leftRaw] <;> omega

theorem rightRaw_abs {U radix J : ℕ} (hb : 1 < radix) (c : ℤ) (k : Coordinate J) :
    |rightRaw U radix J c k| ≤ (radix : ℤ) := by
  cases k with
  | inl j =>
    simp only [rightRaw,Int.abs_natCast]
    exact_mod_cast (digit_lt (by omega) _ _).le
  | inr t => cases t <;> norm_num [rightRaw] <;> omega

theorem requesterRaw_abs {U radix J : ℕ} (hb : 1 < radix)
    (a : ℤ) (c : CarryWord J) (k : Coordinate J) :
    |requesterRaw U radix J a c k| ≤ (radix : ℤ) := by
  cases k with
  | inl j =>
    have hd : (digit radix (shiftOne U a) j : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hd0 : (0 : ℤ) ≤ digit radix (shiftOne U a) j := by positivity
    have h0 := carryAt_bounds c j
    have h1 := carryAt_bounds c (j+1)
    simp only [requesterRaw]
    apply abs_le.mpr
    constructor <;> nlinarith
  | inr t => simp only [requesterRaw,abs_one]; exact_mod_cast (by omega : 1 ≤ radix)

def rawMode (U radix J : ℕ) (b c : ℤ) (k : Coordinate J) : ℤ :=
  leftRaw U radix J b k+rightRaw U radix J c k

theorem rawMode_abs {U radix J : ℕ} (hb : 1 < radix) (b c : ℤ) (k : Coordinate J) :
    |rawMode U radix J b c k| ≤ (radix : ℤ) := by
  cases k with
  | inl j =>
    have hx : (digit radix (shiftOne U b) j : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hy : (digit radix (shiftTwo U c) j : ℤ) < radix := by
      exact_mod_cast digit_lt (by omega : 0 < radix) _ _
    have hx0 : (0 : ℤ) ≤ digit radix (shiftOne U b) j := by positivity
    have hy0 : (0 : ℤ) ≤ digit radix (shiftTwo U c) j := by positivity
    simp only [rawMode,leftRaw,rightRaw]
    exact abs_le.mpr ⟨by omega,by omega⟩
  | inr t => cases t <;> norm_num [rawMode,leftRaw,rightRaw] <;> omega

theorem source_natAbs_bound {U radix J : ℕ} (hb : 1 < radix)
    (b c : ℤ) (k : Coordinate J) :
    (leftRaw U radix J b k).natAbs ≤ radix ∧
      (rightRaw U radix J c k).natAbs ≤ radix := by
  constructor
  · have h := leftRaw_abs (U := U) hb b k
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h
  · have h := rightRaw_abs (U := U) hb c k
    rw [← Int.natCast_natAbs] at h
    exact_mod_cast h

theorem intCast_bounded_injective {radix p : ℕ} {x y : ℤ}
    (hp : 2*radix<p) (hx : |x| ≤ (radix : ℤ)) (hy : |y| ≤ (radix : ℤ))
    (hxy : (x : ZMod p)=(y : ZMod p)) : x=y := by
  have hz : ((x-y : ℤ) : ZMod p)=0 := by simpa using sub_eq_zero.mpr hxy
  have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd (x-y) p).mp hz
  have hab : (x-y).natAbs < (p : ℤ).natAbs := by
    have hab' : |x-y| < (p : ℤ) := by
      have hh := abs_sub x y
      have hpp : 2*(radix : ℤ)<p := by exact_mod_cast hp
      linarith
    rw [← Int.natCast_natAbs] at hab'
    have hh : (x-y).natAbs < p := by exact_mod_cast hab'
    simpa only [Int.natAbs_natCast] using hh
  exact sub_eq_zero.mp (Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hd hab)

def fieldLeft (p U radix J : ℕ) (b : ℤ) (k : Coordinate J) : ZMod p := leftRaw U radix J b k
def fieldRight (p U radix J : ℕ) (c : ℤ) (k : Coordinate J) : ZMod p := rightRaw U radix J c k
def fieldRequester (p U radix J : ℕ) (a : ℤ) (carry : CarryWord J)
    (k : Coordinate J) : ZMod p := requesterRaw U radix J a carry k
def fieldMode (p U radix J : ℕ) (b c : ℤ) (k : Coordinate J) : ZMod p := rawMode U radix J b c k

theorem field_relation_iff {p U radix J : ℕ} (hb : 1 < radix) (hp : 2*radix<p)
    (a b c : ℤ) (carry : CarryWord J) :
    (∀ k, fieldLeft p U radix J b k+fieldRight p U radix J c k=
      fieldRequester p U radix J a carry k) ↔
    (∀ k, leftRaw U radix J b k+rightRaw U radix J c k=requesterRaw U radix J a carry k) := by
  constructor
  · intro h k
    apply intCast_bounded_injective hp (rawMode_abs hb b c k) (requesterRaw_abs hb a carry k)
    simpa only [rawMode,Int.cast_add,fieldLeft,fieldRight,fieldRequester] using h k
  · intro h k
    simpa only [Int.cast_add,fieldLeft,fieldRight,fieldRequester] using
      congrArg (fun x : ℤ => (x : ZMod p)) (h k)

theorem original_difference_field_iff {p U radix J : ℕ} {a b c : ℤ}
    (hb : 1 < radix) (hp : 2*radix<p)
    (ha : |a| ≤ (U : ℤ)) (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ carry ∈ carryCatalog J,
      ∀ k, fieldLeft p U radix J b k+fieldRight p U radix J c k=
        fieldRequester p U radix J a carry k := by
  rw [original_difference_iff ha hB hC hcap]
  simp only [field_relation_iff hb hp]

theorem rawMode_physical_sound {U radix J : ℕ} {b c b' c' : ℤ}
    (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hB' : |b'| ≤ (U : ℤ)) (hC' : |c'| ≤ (U : ℤ))
    (hcap : 4*U<radix^J)
    (hmode : ∀ k, rawMode U radix J b c k=rawMode U radix J b' c' k) :
    c-b=c'-b' := by
  have hd : ∀ j ∈ range J,
      (digit radix (shiftTwo U c) j : ℤ)-(digit radix (shiftOne U b) j : ℤ)=
      (digit radix (shiftTwo U c') j : ℤ)-(digit radix (shiftOne U b') j : ℤ) := by
    intro j hj
    have h := hmode (.inl ⟨j,mem_range.mp hj⟩)
    simpa only [rawMode,leftRaw,rightRaw,sub_eq_add_neg,add_comm] using h
  have he := sum_congr rfl (fun j hj => congrArg (fun z : ℤ => z*(radix : ℤ)^j) (hd j hj))
  simp only [sub_mul,sum_sub_distrib] at he
  change evaluate radix J (fun j => (digit radix (shiftTwo U c) j : ℤ))-
      evaluate radix J (fun j => (digit radix (shiftOne U b) j : ℤ))=
    evaluate radix J (fun j => (digit radix (shiftTwo U c') j : ℤ))-
      evaluate radix J (fun j => (digit radix (shiftOne U b') j : ℤ)) at he
  rw [evaluate_digits_of_lt (shiftTwo_lt hC hcap),evaluate_digits_of_lt (shiftOne_lt hB hcap),
      evaluate_digits_of_lt (shiftTwo_lt hC' hcap),evaluate_digits_of_lt (shiftOne_lt hB' hcap)] at he
  rw [shiftTwo_cast hC,shiftOne_cast hB,shiftTwo_cast hC',shiftOne_cast hB'] at he
  omega

theorem fieldMode_physical_sound {p U radix J : ℕ} {b c b' c' : ℤ}
    (hb : 1 < radix) (hp : 2*radix<p)
    (hB : |b| ≤ (U : ℤ)) (hC : |c| ≤ (U : ℤ))
    (hB' : |b'| ≤ (U : ℤ)) (hC' : |c'| ≤ (U : ℤ))
    (hcap : 4*U<radix^J)
    (hmode : ∀ k, fieldMode p U radix J b c k=fieldMode p U radix J b' c' k) :
    c-b=c'-b' := by
  apply rawMode_physical_sound hB hC hB' hC' hcap
  intro k
  exact intCast_bounded_injective hp (rawMode_abs hb b c k) (rawMode_abs hb b' c' k) (hmode k)

end ThreeSum.TernarySignedModes
