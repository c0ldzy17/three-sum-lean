import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Range
import Mathlib.Tactic

/-!
# Pruned, deterministic enumeration of a ternary rank bank

The recursive procedure only visits prefixes that can occur in the bank.
Its recursion-tree size is at most the bank size times the word length plus one.
This is an enumeration lemma, not a machine-model running-time theorem.
-/

namespace ThreeSum.TernaryEnumeration

def digits (t : ℕ) : List ℕ := (List.range 3).filter (fun d => d ≤ t)

def words : ℕ → ℕ → List (List ℕ)
  | 0, _ => [[]]
  | n + 1, t => (digits t).flatMap fun d => (words n (t - d)).map (List.cons d)

def visits : ℕ → ℕ → ℕ
  | 0, _ => 1
  | n + 1, t => 1 + ((digits t).map fun d => visits n (t - d)).sum

@[simp] theorem mem_digits {d t : ℕ} : d ∈ digits t ↔ d < 3 ∧ d ≤ t := by
  simp [digits]

theorem mem_words (n t : ℕ) (xs : List ℕ) :
    xs ∈ words n t ↔ xs.length = n ∧ (∀ d ∈ xs, d < 3) ∧ xs.sum ≤ t := by
  induction n generalizing t xs with
  | zero =>
    simp only [words, List.mem_singleton]
    constructor
    · rintro rfl
      simp
    · rintro ⟨h, _, _⟩
      exact List.length_eq_zero_iff.mp h
  | succ n ih =>
    cases xs with
    | nil => simp [words]
    | cons d xs =>
      simp only [words, List.mem_flatMap, List.mem_map]
      constructor
      · rintro ⟨e, he, ys, hy, heq⟩
        have heq' : e = d ∧ ys = xs := List.cons.inj heq
        rcases heq' with ⟨rfl, rfl⟩
        obtain ⟨hd, hdt⟩ := mem_digits.mp he
        obtain ⟨hlen, hall, hsum⟩ := (ih (t - e) ys).mp hy
        refine ⟨by simp [hlen], ?_, ?_⟩
        · intro e he
          rcases List.mem_cons.mp he with rfl | he
          · exact hd
          · exact hall e he
        · simp only [List.sum_cons]
          omega
      · rintro ⟨hlen, hall, hsum⟩
        have hd : d < 3 := hall d (by simp)
        have hdt : d ≤ t := by simp only [List.sum_cons] at hsum; omega
        have htail : xs ∈ words n (t - d) := by
          apply (ih (t - d) xs).mpr
          refine ⟨by simpa using hlen, ?_, ?_⟩
          · intro e he
            exact hall e (by simp [he])
          · simp only [List.sum_cons] at hsum
            omega
        exact ⟨d, mem_digits.mpr ⟨hd, hdt⟩, xs, htail, rfl⟩

theorem zero_word_mem (n t : ℕ) : List.replicate n 0 ∈ words n t := by
  apply (mem_words n t _).mpr
  simp

theorem words_nonempty (n t : ℕ) : 0 < (words n t).length := by
  exact List.length_pos_of_mem (zero_word_mem n t)

private theorem sum_map_mono (l : List ℕ) (f g : ℕ → ℕ)
    (h : ∀ x ∈ l, f x ≤ g x) : (l.map f).sum ≤ (l.map g).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x (by simp)) (ih (fun y hy => h y (by simp [hy])))

private theorem sum_map_mul (l : List ℕ) (c : ℕ) (f : ℕ → ℕ) :
    (l.map (fun x => c * f x)).sum = c * (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x xs ih => simp [ih, Nat.mul_add]

theorem words_length_succ (n t : ℕ) :
    (words (n + 1) t).length =
      ((digits t).map fun d => (words n (t - d)).length).sum := by
  simp [words, List.length_flatMap]

theorem visits_le (n t : ℕ) : visits n t ≤ (n + 1) * (words n t).length := by
  induction n generalizing t with
  | zero => simp [visits, words]
  | succ n ih =>
    have hs := sum_map_mono (digits t)
      (fun d => visits n (t - d)) (fun d => (n + 1) * (words n (t - d)).length)
      (fun d _ => ih (t - d))
    rw [sum_map_mul] at hs
    rw [← words_length_succ] at hs
    have hp := words_nonempty (n + 1) t
    simp only [visits]
    nlinarith

end ThreeSum.TernaryEnumeration
