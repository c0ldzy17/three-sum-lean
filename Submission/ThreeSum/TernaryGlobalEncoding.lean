import Submission.ThreeSum.TernaryCoverLocal
import Submission.ThreeSum.Radix
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryGlobalEncoding
open Finset TernaryJointType TernaryCoverLocal TernaryCoverHashes
open scoped BigOperators

variable {L p : ℕ} [Fact p.Prime] {α π : DigitType}
variable {I Ω : Type*} [Fintype I] [Fintype Ω] [DecidableEq Ω]
variable (maps : I → Coordinate (Fin L) → ZMod p) (occ : Ω → I)
  (edge : Ω → LocalEdge L α π)

def rawSource (w : Coordinate (Fin L) → ZMod p) (tag : Bool) (a : TritWord L) : ℤ :=
  (w (Sum.inr tag)).val + ∑ i, ((w (Sum.inl i)).val : ℤ)*(a i).val

def rawLeft (c : Ω) : ℤ := -rawSource (maps (occ c)) false (left (edge c))
def rawRight (c : Ω) : ℤ := rawSource (maps (occ c)) true (right (edge c))

def rawOutput (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) : ℤ :=
  (w (Sum.inr false)).val+(w (Sum.inr true)).val+
    ∑ i, ((w (Sum.inl i)).val : ℤ)*(q i).val

theorem rawSource_cast_left (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    (rawSource w false (left e) : ZMod p) = leftHash w e := by
  simp [rawSource,leftHash,linearHash,leftVector,fieldLeft,fieldWord,Fintype.sum_sum_type,mul_comm,add_comm]

theorem rawSource_cast_right (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    (rawSource w true (right e) : ZMod p) = rightHash w e := by
  simp [rawSource,rightHash,linearHash,rightVector,fieldRight,fieldWord,Fintype.sum_sum_type,mul_comm,add_comm]

theorem raw_addition (w : Coordinate (Fin L) → ZMod p) (e : LocalEdge L α π) :
    rawSource w false (left e)+rawSource w true (right e) = rawOutput w (output e) := by
  unfold rawSource rawOutput
  have hs : (∑ i, ((w (Sum.inl i)).val : ℤ)*(left e i).val)+
      (∑ i, ((w (Sum.inl i)).val : ℤ)*(right e i).val) =
      ∑ i, ((w (Sum.inl i)).val : ℤ)*(output e i).val := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i _
    have h : ((left e i).val : ℤ)+(right e i).val = (output e i).val := by
      exact_mod_cast (edge_data e).2.2.2 i
    rw [← mul_add,h]
  linarith

abbrev OutputBlock (L : ℕ) (π : DigitType) (I : Type*) := I × {q // q ∈ vertices L π}

def blockOfChoice (c : Ω) : OutputBlock L π I := by
  classical
  exact (occ c,⟨output (edge c),mem_filter.mpr ⟨mem_univ _,(edge_data (edge c)).2.2.1⟩⟩)

def blockKey (b : OutputBlock L π I) : ℤ := rawOutput (maps b.1) b.2.val

theorem blockKey_choice (c : Ω) :
    blockKey maps (blockOfChoice occ edge c) = rawRight maps occ edge c-rawLeft maps occ edge c := by
  dsimp [blockKey,blockOfChoice,rawRight,rawLeft]
  linarith [raw_addition (maps (occ c)) (edge c)]

theorem positionalHash_difference (xs : List Ω) :
    Radix.positionalHash (p : ℤ) (rawRight maps occ edge) xs-
      Radix.positionalHash (p : ℤ) (rawLeft maps occ edge) xs =
    Radix.positionalHash (p : ℤ) (blockKey maps) (xs.map (blockOfChoice occ edge)) := by
  induction xs with
  | nil => simp [Radix.positionalHash]
  | cons c xs ih =>
    simp only [List.map_cons,Radix.positionalHash,blockKey_choice]
    rw [← ih]
    ring

theorem localFiber_hash_iff (a b : ℤ) (c : Ω) :
    c ∈ Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b ↔
      leftHash (maps (occ c)) (edge c) = (-a : ZMod p) ∧
      rightHash (maps (occ c)) (edge c) = (b : ZMod p) := by
  simp only [Radix.localFiber,mem_filter,mem_univ,true_and]
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd,← ZMod.intCast_zmod_eq_zero_iff_dvd]
  simp only [Int.cast_sub,rawLeft,rawRight,Int.cast_neg,rawSource_cast_left,rawSource_cast_right]
  constructor
  · intro h
    constructor
    · linear_combination h.1
    · linear_combination -h.2
  · intro h
    constructor
    · linear_combination h.1
    · linear_combination -h.2

def representations (J : ℕ) (a b : ℤ) : Finset (List Ω) :=
  Radix.representations (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) J a b

def wantedRepresentations (J : ℕ) (a b c : ℤ) : Finset (List Ω) :=
  (representations maps occ edge J (-a) b).filter fun xs =>
    (p : ℤ)^J ∣ c-Radix.positionalHash (p : ℤ) (blockKey maps) (xs.map (blockOfChoice occ edge))

/-- Every original modular triple's entire pair-representation fiber is
in the wanted-output dictionary.  Quotient carries remain the Radix recursion. -/
theorem wanted_eq_representations (hp : p ≠ 0) (J : ℕ) (a b c : ℤ)
    (htriple : (p : ℤ)^J ∣ a+b-c) :
    wantedRepresentations maps occ edge J a b c = representations maps occ edge J (-a) b := by
  apply filter_eq_self.mpr
  intro xs hxs
  obtain ⟨_,ha,hb⟩ := (Radix.mem_representations (p : ℤ) (by exact_mod_cast hp)
    (rawLeft maps occ edge) (rawRight maps occ edge) J (-a) b xs).mp hxs
  rw [← positionalHash_difference]
  have hc := dvd_sub (dvd_sub hb ha) htriple
  have he : (b-Radix.positionalHash (p : ℤ) (rawRight maps occ edge) xs)-
      (-a-Radix.positionalHash (p : ℤ) (rawLeft maps occ edge) xs)-(a+b-c) =
      c-(Radix.positionalHash (p : ℤ) (rawRight maps occ edge) xs-
        Radix.positionalHash (p : ℤ) (rawLeft maps occ edge) xs) := by ring
  rw [he] at hc
  exact hc

/-- Covers arbitrary original integer positions, including repeated equal
values, with positive representation multiplicity and the exact radix cap. -/
theorem original_position_cover_and_cap {A B C : Type*}
    (leftInput : A → ℤ) (rightInput : B → ℤ) (outputInput : C → ℤ)
    (hp : p ≠ 0) (cap : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ c : Ω,
      leftHash (maps (occ c)) (edge c) = a ∧ rightHash (maps (occ c)) (edge c) = b)
    (hcap : ∀ a b : ℤ,
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).card ≤ cap)
    (J : ℕ) (i : A) (j : B) (k : C)
    (htriple : (p : ℤ)^J ∣ leftInput i+rightInput j-outputInput k) :
    1 ≤ (wantedRepresentations maps occ edge J (leftInput i) (rightInput j) (outputInput k)).card ∧
    (wantedRepresentations maps occ edge J (leftInput i) (rightInput j) (outputInput k)).card ≤ cap^J := by
  have hlocal (a b : ℤ) :
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).Nonempty := by
    obtain ⟨c,hc⟩ := hcover (-a : ZMod p) (b : ZMod p)
    exact ⟨c,(localFiber_hash_iff maps occ edge a b c).mpr hc⟩
  rw [wanted_eq_representations maps occ edge hp J _ _ _ htriple]
  constructor
  · exact card_pos.mpr (Radix.representations_nonempty (p : ℤ)
      (rawLeft maps occ edge) (rawRight maps occ edge) hlocal J _ _)
  · exact Radix.representations_card_le (p : ℤ) (rawLeft maps occ edge)
      (rawRight maps occ edge) cap hcap J _ _


/-- The baseline source lookup keeps the original `b,c` labels.  Its
negative raw left key is matched at native hash `-b`; the wanted key is `a`.
The arithmetic failure class remains the original difference `c-b-a`. -/
theorem original_difference_position_cover_and_cap {A B C : Type*}
    (aInput : A → ℤ) (bInput : B → ℤ) (cInput : C → ℤ)
    (hp : p ≠ 0) (cap : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ c : Ω,
      leftHash (maps (occ c)) (edge c) = a ∧ rightHash (maps (occ c)) (edge c) = b)
    (hcap : ∀ a b : ℤ,
      (Radix.localFiber (p : ℤ) (rawLeft maps occ edge) (rawRight maps occ edge) a b).card ≤ cap)
    (J : ℕ) (i : A) (j : B) (k : C)
    (htriple : (p : ℤ)^J ∣ cInput k-bInput j-aInput i) :
    1 ≤ (wantedRepresentations maps occ edge J (-bInput j) (cInput k) (aInput i)).card ∧
    (wantedRepresentations maps occ edge J (-bInput j) (cInput k) (aInput i)).card ≤ cap^J := by
  apply original_position_cover_and_cap maps occ edge (fun j => -bInput j) cInput aInput
    hp cap hcover hcap J j k i
  convert htriple using 1 <;> ring


private theorem rawDot_upper (w : Coordinate (Fin L) → ZMod p) (a : TritWord L) :
    (∑ i, ((w (Sum.inl i)).val : ℤ)*(a i).val) ≤ (2*L : ℕ)*p := by
  calc
    _ ≤ ∑ _i : Fin L, (2 : ℤ)*(p : ℤ) := by
      apply sum_le_sum
      intro i _
      have hw : ((w (Sum.inl i)).val : ℤ) ≤ p := by
        have h := (w (Sum.inl i)).val_lt
        exact_mod_cast h.le
      have ha : ((a i).val : ℤ) ≤ 2 := by have h := (a i).isLt; omega
      have hw0 : (0 : ℤ) ≤ (w (Sum.inl i)).val := by positivity
      have ha0 : (0 : ℤ) ≤ (a i).val := by positivity
      nlinarith
    _ = _ := by simp; ring

theorem rawSource_nonnegative (w : Coordinate (Fin L) → ZMod p) (tag : Bool) (a : TritWord L) :
    0 ≤ rawSource w tag a := by
  unfold rawSource
  exact add_nonneg (by positivity) (sum_nonneg (fun i _ => by positivity))

theorem rawSource_upper (w : Coordinate (Fin L) → ZMod p) (tag : Bool) (a : TritWord L) :
    rawSource w tag a ≤ ((2*L+1)*p : ℕ) := by
  have ht : ((w (Sum.inr tag)).val : ℤ) ≤ p := by
    exact_mod_cast (w (Sum.inr tag)).val_lt.le
  have hs := rawDot_upper w a
  unfold rawSource
  push_cast at *
  nlinarith

theorem rawLeft_abs_bound (c : Ω) :
    |rawLeft maps occ edge c| ≤ ((2*L+1)*p : ℕ) := by
  unfold rawLeft
  rw [abs_neg,abs_of_nonneg (rawSource_nonnegative _ _ _)]
  exact rawSource_upper _ _ _

theorem rawRight_abs_bound (c : Ω) :
    |rawRight maps occ edge c| ≤ ((2*L+1)*p : ℕ) := by
  unfold rawRight
  rw [abs_of_nonneg (rawSource_nonnegative _ _ _)]
  exact rawSource_upper _ _ _

theorem rawOutput_nonnegative (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) :
    0 ≤ rawOutput w q := by
  unfold rawOutput
  exact add_nonneg (add_nonneg (by positivity) (by positivity))
    (sum_nonneg (fun i _ => by positivity))

theorem rawOutput_abs_bound (w : Coordinate (Fin L) → ZMod p) (q : TritWord L) :
    |rawOutput w q| ≤ ((2*L+2)*p : ℕ) := by
  rw [abs_of_nonneg (rawOutput_nonnegative w q)]
  have h0 : ((w (Sum.inr false)).val : ℤ) ≤ p := by
    exact_mod_cast (w (Sum.inr false)).val_lt.le
  have h1 : ((w (Sum.inr true)).val : ℤ) ≤ p := by
    exact_mod_cast (w (Sum.inr true)).val_lt.le
  have hs := rawDot_upper w q
  unfold rawOutput
  push_cast at *
  nlinarith

end ThreeSum.TernaryGlobalEncoding
