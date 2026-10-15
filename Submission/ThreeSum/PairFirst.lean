import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.DivMod
import Submission.ThreeSum.LightArray
namespace ThreeSum.LightPairSearch
set_option maxHeartbeats 300000
def first (good : ℕ → Prop) [DecidablePred good] : ℕ → ℕ
  | 0 => 0
  | k+1 => if first good k=0 ∧ good k then k+1 else first good k

theorem first_le (good : ℕ → Prop) [DecidablePred good] : ∀ k, first good k≤k := by
  intro k
  induction k with
  | zero => rfl
  | succ k ih => rw [first]; split <;> omega

theorem first_spec (good : ℕ → Prop) [DecidablePred good] : ∀ k,
    (first good k=0 ↔ ∀ i<k, ¬good i) ∧
    (∀ s, first good k=s+1 → s<k ∧ good s ∧ ∀ i<s, ¬good i) := by
  intro k
  induction k with
  | zero => simp [first]
  | succ k ih =>
    by_cases hz : first good k=0
    · by_cases hg : good k
      · simp only [first,hz,hg,and_self,ite_true]
        constructor
        · constructor
          · omega
          · intro h; exact False.elim ((h k (by omega)) hg)
        · intro s hs
          have he : s=k := by omega
          subst s
          exact ⟨by omega,hg,ih.1.mp hz⟩
      · simp only [first,hz,hg,and_false,ite_false]
        constructor
        · simp only [true_iff]
          intro i hi
          by_cases hik : i<k
          · exact ih.1.mp hz i hik
          · have he : i=k := by omega
            simpa only [he] using hg
        · intro s hs; omega
    · simp only [first,hz,false_and,ite_false]
      constructor
      · constructor
        · exact fun h => False.elim h
        · intro h; exact False.elim (hz (ih.1.mpr (fun i hi => h i (by omega))))
      · intro s hs
        obtain ⟨hlt,hgood,hmin⟩ := ih.2 s hs
        exact ⟨by omega,hgood,hmin⟩

def goodCode (q : ℕ) (good : ℕ → ℕ → Prop) (k : ℕ) : Prop := good (k/q) (k%q)
instance (q : ℕ) (good : ℕ → ℕ → Prop) [DecidableRel good] : DecidablePred (goodCode q good) :=
  fun k => inferInstanceAs (Decidable (good (k/q) (k%q)))

theorem goodCode_pair (q u v : ℕ) (hq : 0<q) (hv : v<q)
    (good : ℕ → ℕ → Prop) : goodCode q good (u*q+v) ↔ good u v := by
  have hdiv : (u*q+v)/q=u := by
    rw [Nat.add_comm,Nat.add_mul_div_right _ _ hq,Nat.div_eq_of_lt hv,Nat.zero_add]
  have hmod : (u*q+v)%q=v := by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hv]
  simp only [goodCode,hdiv,hmod]


end ThreeSum.LightPairSearch
