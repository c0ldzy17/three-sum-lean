import Submission.ThreeSum.LightPairSearchProgram

namespace ThreeSum.LightPairSearch

def Result (q : ℕ) (good : ℕ → ℕ → Prop) (r : ℤ) : Prop :=
  (r=0 ↔ ∀ u<q, ∀ v<q, ¬good u v) ∧
  (0<r → ∃ u<q, ∃ v<q, good u v ∧ r=((1+u*q+v : ℕ) : ℤ) ∧
    ∀ a<q, ∀ b<q, a*q+b<u*q+v → ¬good a b)

theorem first_result (q : ℕ) (hq : 0<q) (good : ℕ → ℕ → Prop) [DecidableRel good] :
    Result q good (first (goodCode q good) (q*q) : ℤ) := by
  have hs := first_pair_spec q hq good
  constructor
  · simpa only [Nat.cast_eq_zero] using hs.1
  · intro hpos
    have hn : first (goodCode q good) (q*q)≠0 := by omega
    obtain ⟨code,hcode⟩ := Nat.exists_eq_succ_of_ne_zero hn
    obtain ⟨hu,hv,hgood,hmin⟩ := hs.2 code hcode
    refine ⟨code/q,hu,code%q,hv,hgood,?_,?_⟩
    · have he : code/q*q+code%q=code := by simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div code q
      rw [hcode]
      exact_mod_cast (show code+1=1+(code/q)*q+code%q by omega)
    · intro a ha b hb hlt
      have he : code/q*q+code%q=code := by simpa only [Nat.mul_comm,Nat.add_comm] using Nat.mod_add_div code q
      exact hmin a ha b hb (by omega)

end ThreeSum.LightPairSearch
