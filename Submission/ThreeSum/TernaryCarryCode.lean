import Submission.ThreeSum.TernarySignedReduction
import Submission.ThreeSum.TernarySignedModes
import Mathlib.Data.Nat.Digits.Lemmas
import Submission.ThreeSumApsp.Util.List

/-! Explicit integer codes for every finite carry; no carry-selection oracle. -/
namespace ThreeSum.TernaryCarryCode
open TernarySignedDigits TernarySignedReduction Finset

def carryFromCode (J q : ℕ) : CarryWord J := fun i =>
  if h : i.val<J then ⟨digit 2 q i.val,by exact digit_lt (by decide) _ _⟩ else 0

def codeOfCarry {J : ℕ} (c : CarryWord J) : ℕ :=
  Nat.ofDigits 2 (List.ofFn fun i : Fin J => (c i.castSucc).val)

private theorem head_drop (l : List ℕ) (j : ℕ) : (l.drop j).head! = l.getD j 0 := by
  induction l generalizing j with
  | nil => cases j <;> simp
  | cons a l ih => cases j with
    | zero => simp
    | succ j => simpa using ih j

theorem digit_ofDigits {b : ℕ} (hb : 1<b) (l : List ℕ)
    (hl : ∀ x∈l, x<b) (j : ℕ) :
    digit b (Nat.ofDigits b l) j=l.getD j 0 := by
  unfold digit quotient
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop j (by omega) l hl,
    Nat.ofDigits_mod_eq_head!,head_drop]
  have hget : l.getD j 0<b := by
    by_cases hj : j<l.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact hl _ (List.getElem_mem _)
    · rw [List.getD_eq_default l 0 (by omega)]
      omega
  exact Nat.mod_eq_of_lt hget

theorem codeOfCarry_lt {J : ℕ} (c : CarryWord J) : codeOfCarry c<2^J := by
  have h := Nat.ofDigits_lt_base_pow_length (by decide : 1<(2 : ℕ))
    (l := List.ofFn fun i : Fin J => (c i.castSucc).val) (by
      intro x hx
      obtain ⟨i,hi⟩ := List.mem_ofFn.mp hx
      rw [← hi]
      exact (c i.castSucc).isLt)
  simpa only [List.length_ofFn,codeOfCarry] using h

theorem codeOfCarry_digit {J : ℕ} (c : CarryWord J) (i : Fin J) :
    digit 2 (codeOfCarry c) i.val=(c i.castSucc).val := by
  unfold codeOfCarry
  rw [digit_ofDigits (by decide)]
  · rw [List.getD_eq_getElem _ _ (by simpa using i.isLt)]
    simp
  · intro x hx
    obtain ⟨j,hj⟩ := List.mem_ofFn.mp hx
    rw [← hj]
    exact (c j.castSucc).isLt

theorem carryFromCode_code {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) :
    carryFromCode J (codeOfCarry c)=c := by
  funext i
  by_cases hi : i.val<J
  · apply Fin.ext
    simp only [carryFromCode,dif_pos hi]
    have h := codeOfCarry_digit c ⟨i.val,hi⟩
    simpa using h
  · have he : i=Fin.last J := by apply Fin.ext; simp; omega
    rw [he,valid_last hc]
    simp [carryFromCode]

theorem codeOfCarry_initial {J : ℕ} {c : CarryWord J} (hc : ValidCarry c) :
    digit 2 (codeOfCarry c) 0=0 := by
  by_cases hJ : 0<J
  · have h := codeOfCarry_digit c ⟨0,hJ⟩
    have hz := hc.1
    simp only [carryAt,show 0<J+1 by omega,dif_pos] at hz
    rw [h]
    exact Int.ofNat_inj.mp hz
  · have hJ0 : J=0 := by omega
    subst J
    simp [codeOfCarry,digit,quotient]

theorem carryFromCode_valid {J q : ℕ} (hq : digit 2 q 0=0) :
    ValidCarry (carryFromCode J q) := by
  constructor
  · simp only [carryAt,show 0<J+1 by omega,dif_pos,carryFromCode]
    split_ifs <;> simp [hq]
  · simp [carryAt,carryFromCode]

def codeCatalog (J : ℕ) : Finset ℕ := (range (2^J)).filter fun q => digit 2 q 0=0

theorem codeCatalog_card (J : ℕ) : (codeCatalog J).card≤2^J := by
  exact (card_filter_le _ _).trans_eq (card_range _)

theorem carryCatalog_eq_codes (J : ℕ) :
    carryCatalog J=(codeCatalog J).image (carryFromCode J) := by
  ext c
  constructor
  · intro hc
    have hv := (mem_carryCatalog c).mp hc
    apply mem_image.mpr
    exact ⟨codeOfCarry c,mem_filter.mpr ⟨mem_range.mpr (codeOfCarry_lt c),codeOfCarry_initial hv⟩,
      carryFromCode_code hv⟩
  · intro hc
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hc
    exact (mem_carryCatalog _).mpr (carryFromCode_valid (mem_filter.mp hq).2)

/-- The exact original equation is covered by the literal bounded integer
loop over carry codes, followed by its explicit lowest-bit test. -/
theorem original_difference_code_iff {p U radix J : ℕ} {a b c : ℤ}
    (hb : 1<radix) (hp : 2*radix<p)
    (hA : |a|≤(U : ℤ)) (hB : |b|≤(U : ℤ)) (hC : |c|≤(U : ℤ))
    (hcap : 4*U<radix^J) :
    c-b=a ↔ ∃ q<2^J, digit 2 q 0=0 ∧
      ∀ k, TernarySignedModes.fieldLeft p U radix J b k+
        TernarySignedModes.fieldRight p U radix J c k=
        TernarySignedModes.fieldRequester p U radix J a (carryFromCode J q) k := by
  rw [TernarySignedModes.original_difference_field_iff hb hp hA hB hC hcap,
    carryCatalog_eq_codes]
  constructor
  · rintro ⟨carry,hcarry,hrel⟩
    obtain ⟨q,hq,rfl⟩ := mem_image.mp hcarry
    exact ⟨q,mem_range.mp (mem_filter.mp hq).1,(mem_filter.mp hq).2,hrel⟩
  · rintro ⟨q,hq,hzero,hrel⟩
    exact ⟨carryFromCode J q,mem_image.mpr ⟨q,mem_filter.mpr ⟨mem_range.mpr hq,hzero⟩,rfl⟩,hrel⟩

end ThreeSum.TernaryCarryCode
