import Submission.ThreeSum.Greedy
import Submission.ThreeSum.LightMinimum

/-!
# Linking array extrema to the finite greedy-cover definition

The program scans indices in increasing order and retains the first
maximum. This is exactly the tie rule in `List.argmax` used by the
mathematical cover construction.
-/

namespace ThreeSum.IndexedGreedy

open LightMinimum

theorem argmax_range (f : ℕ → ℕ) {n : ℕ} (hn : 0 < n) :
    (List.range n).argmax f = some (least (fun i => -(f i : ℤ)) n) := by
  induction n with
  | zero => omega
  | succ n ih =>
    cases n with
    | zero => simp [least]
    | succ n =>
      rw [List.range_succ,List.argmax_concat,ih (by omega)]
      change (if f (least (fun i => -(f i : ℤ)) (n+1)) < f (n+1)
        then some (n+1) else some (least (fun i => -(f i : ℤ)) (n+1))) =
        some (if -(f (n+1) : ℤ) < -(f (least (fun i => -(f i : ℤ)) (n+1)) : ℤ)
          then n+1 else least (fun i => -(f i : ℤ)) (n+1))
      split_ifs <;> first | rfl | omega

theorem argmax_map {α β : Type*} (g : α → β) (f : β → ℕ) (xs : List α) :
    (xs.map g).argmax f = (xs.argmax (f ∘ g)).map g := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs x ih =>
    rw [List.map_append,List.map_singleton,List.argmax_concat,ih,List.argmax_concat]
    cases h : xs.argmax (f ∘ g) with
    | none => rfl
    | some y =>
      simp only [Option.map_some,Function.comp_apply]
      split <;> rfl

theorem selectMap_indices {U : Type*} [DecidableEq U]
    (covers : ℕ → U → Prop) [DecidableRel covers]
    (targets : Finset U) {n : ℕ} (hn : 0 < n) :
    Cover.selectMap (List.range n) covers targets =
      least (fun i => -((targets.filter (covers i)).card : ℤ)) n := by
  unfold Cover.selectMap
  rw [argmax_range _ hn]
  rfl

theorem selectMap_mapped {α : Type*} [Inhabited α]
    {U : Type*} [DecidableEq U]
    (g : ℕ → α) (covers : α → U → Prop) [DecidableRel covers]
    (targets : Finset U) {n : ℕ} (hn : 0 < n) :
    Cover.selectMap ((List.range n).map g) covers targets =
      g (least (fun i => -((targets.filter (covers (g i))).card : ℤ)) n) := by
  unfold Cover.selectMap
  rw [argmax_map,argmax_range _ hn]
  rfl

end ThreeSum.IndexedGreedy
