import Submission.ThreeSum.ReportingHostFrontierLayout
import Submission.ThreeSum.Auxiliary
import Submission.ThreeSum.Scales

/-!
# Sound cumulative dense stopping on visited wanted labels

Distinct wanted labels have disjoint raw-incidence fibers. Therefore any
visited prefix already exceeding the exact representation-times-false-score
threshold certifies an original equation, before proportional traversal.
-/

namespace ThreeSum.DenseGuard

open Finset GlobalEncoding RawIncidences RawReporting ReportingHostFrontierLayout

set_option maxHeartbeats 1600000
set_option maxRecDepth 8000
set_option linter.unusedSectionVars false

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def mass {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) : ℕ := (visited.map (rootMass I)).sum

@[simp] theorem mass_nil {h J : ℕ} (I : Finset (RawItem h J α β γ)) : mass I []=0 := rfl

theorem mass_append {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) (w : Wanted h J α) :
    mass I (visited++[w])=mass I visited+rootMass I w := by simp [mass]

theorem mass_le_raw_card {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (visited : List (Wanted h J α)) (hn : visited.Nodup) : mass I visited ≤ I.card := by
  unfold mass
  rw [← List.sum_toFinset _ hn]
  calc
    _ ≤ ∑ w : Wanted h J α, rootMass I w := Finset.sum_le_sum_of_subset (Finset.subset_univ _)
    _ = I.card := by
      simp only [rootMass_eq]
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

theorem partial_early_yes {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (aux : Finset ℤ)
    (visited : List (Wanted h J α)) (hn : visited.Nodup)
    (hP : 0 < P) (hguard : 4*P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬ l ∣ difference a b c t)
    (hlarge : representationCap h J*Arithmetic.weightedFalseCount T (difference a b c) aux P <
      mass (rawOn h J P d T a b c) visited) :
    ∃ t ∈ T, difference a b c t=0 :=
  RawIncidences.dense_early_yes T a b c aux hP hguard hsep
    (hlarge.trans_le (mass_le_raw_card _ visited hn))

theorem partial_early_yes_of_upper {h J H : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (aux : Finset ℤ)
    (visited : List (Wanted h J α)) (hn : visited.Nodup)
    (hP : 0 < P) (hguard : 4*P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬ l ∣ difference a b c t)
    (hH : Arithmetic.weightedFalseCount T (difference a b c) aux P ≤ H)
    (hlarge : representationCap h J*H < mass (rawOn h J P d T a b c) visited) :
    ∃ t ∈ T, difference a b c t=0 :=
  partial_early_yes T a b c aux visited hn hP hguard hsep
    ((Nat.mul_le_mul_left _ hH).trans_lt hlarge)

theorem no_equation_mass_le {h J : ℕ} {P d : ℤ} (T : Finset (Original α β γ))
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (aux : Finset ℤ)
    (visited : List (Wanted h J α)) (hn : visited.Nodup)
    (hP : 0 < P) (hguard : 4*P ≤ globalModulus h J)
    (hsep : ∀ t ∈ T, difference a b c t ≠ 0 → ∃ l ∈ aux, ¬ l ∣ difference a b c t)
    (hno : ∀ t ∈ T, difference a b c t ≠ 0) :
    mass (rawOn h J P d T a b c) visited ≤
      representationCap h J*Arithmetic.weightedFalseCount T (difference a b c) aux P := by
  by_contra hfail
  obtain ⟨t,ht,he⟩ := partial_early_yes (d := d) T a b c aux visited hn hP hguard hsep (by omega)
  exact hno t ht he

end ThreeSum.DenseGuard
