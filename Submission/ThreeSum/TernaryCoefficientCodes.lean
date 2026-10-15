import Submission.ThreeSum.TernaryExtensionDecoded

/-! Literal base-p coefficient codes enumerate every polynomial candidate. -/

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding

open Polynomial
variable {p : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

def coefficientCode {d : ℕ} (a : Fin d → ZMod p) : ℕ :=
  Nat.ofDigits p (List.ofFn fun i => (a i).val)

def coefficientVector (d code : ℕ) : Fin d → ZMod p :=
  fun i => ((code/p^i.val%p : ℕ) : ZMod p)

theorem coefficientCode_lt {d : ℕ} (a : Fin d → ZMod p) : coefficientCode a<p^d := by
  have h := Nat.ofDigits_lt_base_pow_length (Fact.out : p.Prime).one_lt
    (l := List.ofFn fun i => (a i).val) (by
      intro n hn
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hn
      exact ZMod.val_lt _)
  simpa only [coefficientCode,List.length_ofFn] using h

theorem coefficientCode_digit {d : ℕ} (a : Fin d → ZMod p) (i : Fin d) :
    coefficientCode a/p^i.val%p=(a i).val := by
  let xs := List.ofFn fun j => (a j).val
  have hb : ∀ n∈xs, n<p := by
    intro n hn
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hn
    exact ZMod.val_lt _
  have hh : (xs.drop i.val).head?=some ((a i).val) := by
    simp [xs,List.head?_drop,i.isLt]
  change Nat.ofDigits p xs/p^i.val%p=_
  rw [Nat.ofDigits_div_pow_eq_ofDigits_drop i.val (Fact.out : p.Prime).pos xs hb,
    Nat.ofDigits_mod_eq_head!,List.head!_of_head? hh,Nat.mod_eq_of_lt (ZMod.val_lt _)]

theorem coefficientVector_code {d : ℕ} (a : Fin d → ZMod p) :
    coefficientVector d (coefficientCode a)=a := by
  funext i
  simp only [coefficientVector,coefficientCode_digit,ZMod.natCast_zmod_val]

theorem coefficientCode_injective (d : ℕ) :
    Function.Injective (coefficientCode (p := p) (d := d)) := by
  intro a b h
  rw [← coefficientVector_code a,← coefficientVector_code b,h]

def coefficientEquiv (d : ℕ) : (Fin d → ZMod p) ≃ Fin (p^d) :=
  Equiv.ofBijective (fun a => ⟨coefficientCode a,coefficientCode_lt a⟩)
    ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨fun a b h => coefficientCode_injective d (congrArg Fin.val h),by simp⟩)

theorem code_coefficientVector {d code : ℕ} (hc : code<p^d) :
    coefficientCode (coefficientVector (p := p) d code)=code := by
  obtain ⟨a,ha⟩ := (coefficientEquiv (p := p) d).surjective ⟨code,hc⟩
  have he : coefficientCode a=code := congrArg Fin.val ha
  rw [← he,coefficientVector_code]

theorem code_high_digit_zero {d code k : ℕ} (hc : code<p^d) (hk : d≤k) :
    code/p^k%p=0 := by
  have hpow : p^d≤p^k := Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).one_lt; omega) hk
  rw [Nat.div_eq_of_lt (hc.trans_le hpow)]
  simp

def monicOfCode (d code : ℕ) : (ZMod p)[X] := monicCandidate (coefficientVector d code)

theorem exists_irreducible_code (d : ℕ) (hd : 0<d) :
    ∃ code<p^d, Irreducible (monicOfCode (p := p) d code) := by
  obtain ⟨a,ha⟩ := exists_irreducible_candidate (p := p) d hd
  refine ⟨coefficientCode a,coefficientCode_lt a,?_⟩
  simpa only [monicOfCode,coefficientVector_code] using ha

end ThreeSum.TernaryExtensionEncoding
