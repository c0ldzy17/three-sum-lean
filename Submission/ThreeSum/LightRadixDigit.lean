import Submission.ThreeSum.LightSmallDivide

/-! # An actual radix digit using two local counting divisions -/

namespace ThreeSum.LightRadixDigit

open Light

def body (pDivide : ℕ) : Stmt :=
  .call pDivide [v 0,v 1] 3 ;;
  .call pDivide [v 3,v 2] 4 ;;
  .set 0 (v 3 -' v 4 *' v 2)

def time (k : ℕ) : ℕ := 40*(k+1)+100
def word (k b p : ℕ) : ℕ := 4*(k+b+p+2)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pDivide k b p : ℕ}
    (hmain : P[pMain]? = some (body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body) (μ : ℕ → ℤ)
    (hd : d < lim.depth) (hword : (word k b p : ℤ) ≤ lim.word) :
    Meets lim P pMain d [k,b,p] μ (time k)
      (fun r μ' => r = (((k/b)%p : ℕ) : ℤ) ∧ μ'=μ) := by
  have hq : k/b ≤ k := Nat.div_le_self k b
  have hq2 : (k/b)/p ≤ k/b := Nat.div_le_self (k/b) p
  have hprod : ((k/b)/p)*p ≤ k/b := Nat.div_mul_le_self (k/b) p
  have hbudget (x : ℕ) (hx : x ≤ word k b p) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hw1 := hbudget (k+b+2) (by unfold word; omega)
  have hw2 := hbudget (k/b+p+2) (by unfold word; omega)
  have hkWord := hbudget k (by unfold word; omega)
  have hbWord := hbudget b (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hqWord := hbudget (k/b) (by unfold word; omega)
  have hq2Word := hbudget ((k/b)/p) (by unfold word; omega)
  have hprodWord : (((k/b)/p : ℕ) : ℤ)*(p : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast hprod : (((k/b)/p : ℕ) : ℤ)*(p : ℤ) ≤ (k/b : ℕ)).trans hqWord
  have hprodNonneg : (0 : ℤ) ≤ (((k/b)/p : ℕ) : ℤ)*(p : ℤ) := by positivity
  have hrem : ((k/b : ℕ) : ℤ)-(((k/b)/p : ℕ) : ℤ)*p = (((k/b)%p : ℕ) : ℤ) := by
    have hh := Nat.mod_add_div (k/b) p
    have he : (k/b)%p+((k/b)/p)*p=k/b := by simpa only [Nat.mul_comm] using hh
    exact_mod_cast (by omega : k/b-((k/b)/p)*p=(k/b)%p)
  have hprodIntWord : (k : ℤ)/(b : ℤ)/(p : ℤ)*(p : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_ediv] using hprodWord
  have hprodIntNonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ)/(p : ℤ)*(p : ℤ) := by
    simpa only [Int.natCast_ediv] using hprodNonneg
  have hremInt : (k : ℤ)/(b : ℤ)-(k : ℤ)/(b : ℤ)/(p : ℤ)*p =
      (((k/b)%p : ℕ) : ℤ) := by
    simpa only [Int.natCast_ediv] using hrem
  have hqNonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ) := by
    rw [← Int.natCast_ediv]
    exact Int.natCast_nonneg _
  have hq2Nonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ)/(p : ℤ) := by
    rw [← Int.natCast_ediv,← Int.natCast_ediv]
    exact Int.natCast_nonneg _
  have hmodWord := hbudget ((k/b)%p) (by
    have hm := Nat.mod_le (k/b) p
    unfold word
    omega)
  have hmodIntNonneg : (0 : ℤ) ≤ (k : ℤ)/(b : ℤ)%(p : ℤ) := by
    exact_mod_cast Nat.zero_le ((k/b)%p)
  have hmodIntWord : (k : ℤ)/(b : ℤ)%(p : ℤ) ≤ lim.word := by
    simpa only [Int.natCast_ediv,Int.natCast_emod] using hmodWord
  have htime1 : LightSmallDivide.time k b ≤ 20*(k+1)+20 := by
    unfold LightSmallDivide.time
    omega
  have htime2 : LightSmallDivide.time (k/b) p ≤ 20*(k+1)+20 := by
    unfold LightSmallDivide.time
    omega
  apply Meets.of_body hmain
  unfold body time
  light_call (LightSmallDivide.meets (d := d+1) (a := k) (b := b) hdivide μ hw1)
    using LightSmallDivide.time with q μ₁ ⟨hqval,hmem₁⟩
  subst μ₁
  subst q
  light_call (LightSmallDivide.meets (d := d+1) (a := k/b) (b := p) hdivide μ hw2)
    using LightSmallDivide.time with q2 μ₂ ⟨hq2val,hmem₂⟩
  subst μ₂
  subst q2
  light_set ((k/b)%p : ℕ) using hrem,hremInt,LightSmallDivide.time
  exact ⟨rfl,rfl⟩

def program : Program := [body 1,LightSmallDivide.body]

theorem program_meets {k b p : ℕ} (μ : ℕ → ℤ)
    (hd : d < lim.depth) (hword : (word k b p : ℤ) ≤ lim.word) :
    Meets lim program 0 d [k,b,p] μ (time k)
      (fun r μ' => r = (((k/b)%p : ℕ) : ℤ) ∧ μ'=μ) :=
  meets rfl rfl μ hd hword

end ThreeSum.LightRadixDigit
