import Submission.ThreeSum.LightArray
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Summing an array of indirect nonnegative table lookups

The program reads each key once and adds its table entry to a word-sized
accumulator. The contract counts the loop, address arithmetic, both loads,
and additions. It does not change memory.
-/

namespace ThreeSum.LightLookupSum

open Light Finset
open scoped BigOperators

def prefixSum (f : ℕ → ℕ) (key : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∑ i ∈ range n, f (key i)

theorem prefixSum_zero (f key : ℕ → ℕ) : prefixSum f key 0 = 0 := by
  simp [prefixSum]

theorem prefixSum_succ (f key : ℕ → ℕ) (j : ℕ) :
    prefixSum f key (j+1) = prefixSum f key j + f (key j) := by
  exact sum_range_succ _ _

theorem prefixSum_le (f key : ℕ → ℕ) {n B j : ℕ}
    (hvalue : ∀ i < n, f (key i) ≤ B) (hj : j ≤ n) :
    prefixSum f key j ≤ j*B := by
  unfold prefixSum
  calc
    _ ≤ ∑ _i ∈ range j, B := sum_le_sum fun i hi => hvalue i (by
      have := mem_range.mp hi
      omega)
    _ = _ := by simp

def loopBody : Stmt :=
  .set 4 (v 4 +' M (v 1 +' M (v 0 +' v 5)))

/-- Arguments: key array, value table, number of keys, table length. -/
def body : Stmt :=
  .set 4 (k 0) ;;
  .for 5 (v 2) loopBody ;;
  .set 0 (v 4)

def time (n : ℕ) : ℕ := 24*n+20

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pThis : ℕ} (hThis : P[pThis]? = some body)
    {μ : ℕ → ℤ} {keys table n p B : ℕ} (key f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+n ≤ lim.space) (htable : table+p ≤ lim.space)
    (hkey : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hrange : ∀ i < n, key i < p)
    (hread : ∀ r < p, μ (table+r) = (f r : ℤ))
    (hvalue : ∀ r < p, f r ≤ B)
    (hword : (n*B : ℕ) ≤ lim.word) :
    Meets lim P pThis d [keys, table, n, p] μ (time n)
      fun r μ' => r = (prefixSum f key n : ℤ) ∧ μ' = μ := by
  have hv : ∀ i < n, f (key i) ≤ B := fun i hi => hvalue (key i) (hrange i hi)
  apply Meets.of_body hThis
  unfold body time
  light_set 0
  refine Ends.pieceThen (Ends.for (T := 24*n+6)
    (Q := fun σ => σ = ⟨frame [(keys : ℤ), table, n, p, prefixSum f key n, n], μ⟩)
    (fun j σ => σ = ⟨frame [(keys : ℤ), table, n, p, prefixSum f key j, j], μ⟩)
    n 16 ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · simp [prefixSum_zero, update_frame_setLocal]
  · rintro j _ hj _ rfl
    have hkr := hrange j hj
    have hkeyread := hkey j hj
    have htread := hread (key j) hkr
    have hsum := prefixSum_le f key hv (j := j+1) (by omega)
    have hsumword : (prefixSum f key (j+1) : ℤ) ≤ lim.word := by
      have hmul : (j+1)*B ≤ n*B := Nat.mul_le_mul_right B (by omega)
      exact (by exact_mod_cast hsum.trans hmul :
        (prefixSum f key (j+1) : ℤ) ≤ (n*B : ℕ)).trans hword
    have hsumcast : (prefixSum f key j : ℤ) + f (key j) = prefixSum f key (j+1) := by
      rw [prefixSum_succ, Nat.cast_add]
    unfold loopBody
    refine Ends.setLast ?_ (hs := by light_side [hkeyread, htread, hsumcast])
      (hT := by light_time)
    simp [hkeyread, htread, hsumcast, update_frame_setLocal]
  · intro σ hcounter hshape
    exact hshape
  · rintro j _ hj _ rfl
    light_side
  · intro σ hshape
    rw [hshape]
    light_set (prefixSum f key n)
    exact ⟨rfl, rfl⟩

def program : Program := [body]

theorem program_meets
    {μ : ℕ → ℤ} {keys table n p B : ℕ} (key f : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+n ≤ lim.space) (htable : table+p ≤ lim.space)
    (hkey : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hrange : ∀ i < n, key i < p)
    (hread : ∀ r < p, μ (table+r) = (f r : ℤ))
    (hvalue : ∀ r < p, f r ≤ B)
    (hword : (n*B : ℕ) ≤ lim.word) :
    Meets lim program 0 d [keys, table, n, p] μ (time n)
      (fun r μ' => r = (prefixSum f key n : ℤ) ∧ μ' = μ) :=
  meets rfl key f hw hkeys htable hkey hrange hread hvalue hword

end ThreeSum.LightLookupSum
