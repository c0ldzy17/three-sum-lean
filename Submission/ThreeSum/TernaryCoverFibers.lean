import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Literal output fibers from the untrimmed trinary edge set

The output-fiber bound uses every partition of each output.  Trimming source
buckets must therefore occur only after this count.  These lemmas are finite
double counts, independent of any entropy or random-hash estimate.
-/

namespace ThreeSum.TernaryCoverFibers

open Finset
open scoped BigOperators

variable {E Q K : Type*} [Fintype E] [Fintype Q] [Fintype K]
variable [DecidableEq Q] [DecidableEq K] [AddCommGroup K]

/-- The full edge count at an ordered pair of hashes. -/
def rawPairCount (left right : E → K) (a b : K) : ℕ :=
  (univ.filter fun e => left e = a ∧ right e = b).card

/-- The full set of outputs at one literal output hash. -/
def outputFiberCount (outputHash : Q → K) (o : K) : ℕ :=
  (univ.filter fun q => outputHash q = o).card

/-- Partition the edges at one sum hash by their first endpoint hash. -/
theorem sum_rawPairCount (left right : E → K) (o : K) :
    (∑ a : K, rawPairCount left right a (o - a)) =
      (univ.filter fun e => left e + right e = o).card := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := univ.filter fun e => left e + right e = o)
    (t := (univ : Finset K)) (f := left) (fun _ _ => mem_univ _)
  rw [hpartition]
  apply sum_congr rfl
  intro a _
  unfold rawPairCount
  congr 1
  ext e
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨hl, hr⟩
    exact ⟨by rw [hl, hr]; simp, hl⟩
  · rintro ⟨hadd, hl⟩
    exact ⟨hl, by rw [← hadd, hl]; simp⟩

/-- Every output has its full, constant number of ordered partitions. -/
theorem untrimmed_output_count (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G)
    (hadd : ∀ e : E, left e + right e = outputHash (output e)) (o : K) :
    (univ.filter fun e => left e + right e = o).card =
      G * outputFiberCount outputHash o := by
  classical
  have hpartition := Finset.card_eq_sum_card_fiberwise
    (s := univ.filter fun e => left e + right e = o)
    (t := univ.filter fun q => outputHash q = o) (f := output)
    (by
      intro e he
      apply mem_filter.mpr
      refine ⟨mem_univ _, ?_⟩
      rw [← hadd e]
      exact (mem_filter.mp he).2)
  rw [hpartition]
  have hterm : ∀ q ∈ (univ.filter fun q => outputHash q = o),
      ((univ.filter fun e => left e + right e = o).filter
        fun e => output e = q).card = G := by
    intro q hq
    have heq : ((univ.filter fun e => left e + right e = o).filter
        fun e => output e = q) = (univ.filter fun e => output e = q) := by
      ext e
      simp only [mem_filter, mem_univ, true_and]
      constructor
      · exact fun h => h.2
      · intro he
        refine ⟨?_, he⟩
        rw [hadd e, he]
        exact (mem_filter.mp hq).2
    rw [heq]
    exact hfiber q
  calc
    _ = ∑ _q ∈ (univ.filter fun q => outputHash q = o), G := sum_congr rfl hterm
    _ = G * outputFiberCount outputHash o := by
      simp [outputFiberCount, Nat.mul_comm]

/-- The literal output bound uses raw ordered fibers, not the retained
endpoint-bucket bound. -/
theorem literal_output_fiber_bound (output : E → Q) (outputHash : Q → K)
    (left right : E → K) (G τ : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G)
    (hadd : ∀ e : E, left e + right e = outputHash (output e))
    (hraw : ∀ a b : K, rawPairCount left right a b ≤ τ) (o : K) :
    G * outputFiberCount outputHash o ≤ Fintype.card K * τ := by
  rw [← untrimmed_output_count output outputHash left right G hfiber hadd o,
    ← sum_rawPairCount left right o]
  calc
    _ ≤ ∑ _a : K, τ := sum_le_sum (fun a _ => hraw a (o - a))
    _ = Fintype.card K * τ := by simp

/-- The total number of edges is outputs times partitions per output. -/
theorem edge_count (output : E → Q) (G : ℕ)
    (hfiber : ∀ q : Q, (univ.filter fun e => output e = q).card = G) :
    Fintype.card E = Fintype.card Q * G := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset E)) (t := (univ : Finset Q)) (f := output)
    (fun _ _ => mem_univ _)
  simpa [hfiber] using h

end ThreeSum.TernaryCoverFibers
