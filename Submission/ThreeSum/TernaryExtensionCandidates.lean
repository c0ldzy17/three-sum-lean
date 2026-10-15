import Submission.ThreeSum.TernaryExtensionEncoding
import Mathlib.Data.Nat.Log

/-! Finite monic candidates and explicit polynomial-sized row-menu field. -/

noncomputable section
namespace ThreeSum.TernaryExtensionEncoding

open Polynomial Finset

set_option maxHeartbeats 3000000

variable {p : ℕ} [Fact p.Prime]

def vectorPolynomial {d : ℕ} (a : Fin d → ZMod p) : (ZMod p)[X] :=
  ∑ i : Fin d, monomial i.val (a i)

theorem vectorPolynomial_degree_lt {d : ℕ} (a : Fin d → ZMod p) :
    (vectorPolynomial a).degree < d := by
  unfold vectorPolynomial
  simp_rw [← C_mul_X_pow_eq_monomial]
  exact degree_sum_fin_lt a

theorem vectorPolynomial_coeff {d : ℕ} (a : Fin d → ZMod p) (i : Fin d) :
    (vectorPolynomial a).coeff i.val=a i := by
  simp only [vectorPolynomial,finsetSum_coeff,coeff_monomial,Fin.val_eq_val,
    Finset.sum_ite_eq',if_pos (Finset.mem_univ i)]

def monicCandidate {d : ℕ} (a : Fin d → ZMod p) : (ZMod p)[X] :=
  X^d+vectorPolynomial a

theorem monicCandidate_monic {d : ℕ} (a : Fin d → ZMod p) : (monicCandidate a).Monic := by
  exact monic_X_pow_add (vectorPolynomial_degree_lt a)

theorem monicCandidate_degree {d : ℕ} (a : Fin d → ZMod p) :
    (monicCandidate a).natDegree=d := by
  have h := natDegree_add_eq_left_of_degree_lt
    (p := (X^d : (ZMod p)[X])) (q := vectorPolynomial a)
    (by simpa using vectorPolynomial_degree_lt a)
  simpa only [monicCandidate,natDegree_X_pow] using h

theorem monicCandidate_coeff {d : ℕ} (a : Fin d → ZMod p) (i : Fin d) :
    (monicCandidate a).coeff i.val=a i := by
  rw [monicCandidate,coeff_add,coeff_X_pow,if_neg (by omega),zero_add]
  exact vectorPolynomial_coeff a i

theorem monicCandidate_of_monic {d : ℕ} {f : (ZMod p)[X]}
    (hf : f.Monic) (hd : f.natDegree=d) :
    monicCandidate (fun i : Fin d => f.coeff i.val)=f := by
  ext k
  by_cases hk : k<d
  · simpa using monicCandidate_coeff (fun i : Fin d => f.coeff i.val) ⟨k,hk⟩
  · by_cases he : k=d
    · subst k
      have hc := (monicCandidate_monic (fun i : Fin d => f.coeff i.val)).coeff_natDegree
      rw [monicCandidate_degree] at hc
      rw [hc]
      simpa [hd] using hf.coeff_natDegree.symm
    · have hlt : d<k := by omega
      rw [coeff_eq_zero_of_natDegree_lt (by simpa [monicCandidate_degree] using hlt),
        coeff_eq_zero_of_natDegree_lt (by omega)]

theorem monicCandidate_injective (d : ℕ) :
    Function.Injective (monicCandidate (p := p) (d := d)) := by
  intro a b h
  funext i
  have hc := congrArg (fun f : (ZMod p)[X] => f.coeff i.val) h
  simpa only [monicCandidate_coeff] using hc

theorem exists_irreducible_candidate (d : ℕ) (hd : 0<d) :
    ∃ a : Fin d → ZMod p, Irreducible (monicCandidate a) := by
  obtain ⟨f,hmon,hI,hdeg⟩ := exists_monic_irreducible p d hd
  refine ⟨fun i => f.coeff i.val,?_⟩
  rw [monicCandidate_of_monic hmon hdeg]
  exact hI

theorem monic_candidate_count (d : ℕ) :
    (univ.image (monicCandidate (p := p) (d := d))).card=p^d := by
  rw [card_image_of_injective _ (monicCandidate_injective d)]
  simp

def menuDegree (p Λ K : ℕ) : ℕ := Nat.clog p (8*(Λ+1)*p^(4*K))

theorem menuDegree_pos (Λ K : ℕ) : 0<menuDegree p Λ K := by
  apply Nat.clog_pos (Fact.out : p.Prime).one_lt
  have hp : 0<p^(4*K) := pow_pos (Fact.out : p.Prime).pos _
  nlinarith

theorem menu_field_lower (Λ K : ℕ) :
    8*(Λ+1)*p^(4*K)≤p^(menuDegree p Λ K) :=
  Nat.le_pow_clog (Fact.out : p.Prime).one_lt _

theorem menu_field_upper (Λ K : ℕ) :
    p^(menuDegree p Λ K)≤8*p^(4*K+1)*(Λ+1) := by
  have hp := (Fact.out : p.Prime).one_lt
  have hpos := menuDegree_pos (p := p) Λ K
  have ht : 1<8*(Λ+1)*p^(4*K) := by
    have hh := pow_pos (Fact.out : p.Prime).pos (4*K)
    nlinarith
  have hprev := Nat.pow_pred_clog_lt_self hp ht
  have he : menuDegree p Λ K=(menuDegree p Λ K).pred+1 := Nat.succ_pred_eq_of_pos hpos |>.symm
  calc
    _ = p^(menuDegree p Λ K).pred*p := by
      conv_lhs => rw [he]
      rw [pow_succ]
    _ ≤ (8*(Λ+1)*p^(4*K))*p := Nat.mul_le_mul_right p (by simpa only [menuDegree] using hprev.le)
    _ = _ := by rw [pow_succ]; ring

end ThreeSum.TernaryExtensionEncoding
