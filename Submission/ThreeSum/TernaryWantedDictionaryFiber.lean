import Submission.ThreeSum.TernaryCanonicalFibers

namespace ThreeSum.TernaryWantedDictionaryFiber
open TernaryWantedRadix RadixKeyLists TernaryCanonicalFibers

theorem filter_flatMap {A B : Type*} (xs : List A) (f : A → List B) (q : B → Bool) :
    (xs.flatMap f).filter q = xs.flatMap (fun x => (f x).filter q) := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp only [List.flatMap_cons,List.filter_append,ih]

theorem filter_flatMap_ite {A B : Type*} (xs : List A) (q : A → Bool) (f : A → List B) :
    (xs.filter q).flatMap f=xs.flatMap (fun x => if q x then f x else []) := by
  induction xs with
  | nil => simp
  | cons x xs ih => cases hx : q x <;> simp [hx,ih]

theorem flatMap_range_getD (xs : List ℤ) {A : Type*} (f : ℤ → List A) :
    xs.flatMap f=(List.range xs.length).flatMap (fun i => f (xs.getD i 0)) := by
  conv_rhs => rw [← List.flatMap_map,map_range_getD]

/-- Exact list equality, rather than just existence: every repeated dictionary
key corresponds to its own carry-compatible tuple occurrence. -/
theorem filtered_values (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) :
    ∀ j x, (values p raws j).filter (fun z => p^j ∣ x-z)=
      (wantedOutputs p raws j x).map (Radix.positionalHash p (fun i => raws.getD i 0)) := by
  intro j
  induction j with
  | zero => intro x; simp [values,wantedOutputs,Radix.positionalHash]
  | succ j ih =>
    intro x
    rw [values,step,filter_flatMap,flatMap_range_getD]
    simp only [wantedOutputs,List.map_flatMap,List.map_map,Function.comp_def,Radix.positionalHash]
    rw [localBucket,filter_flatMap_ite]
    apply List.flatMap_congr
    intro i hi
    by_cases hd : p ∣ x-raws.getD i 0
    · simp only [hd,decide_true,ite_true]
      rw [List.filter_map]
      have hpred : (fun z : ℤ => decide (p^(j+1) ∣ x-(raws.getD i 0+p*z)))=
          fun z => decide (p^j ∣ (x-raws.getD i 0)/p-z) := by
        funext z
        exact decide_eq_decide.mpr (by rw [Radix.radix_divisibility p _ _ _ hp]; simp only [hd,true_and])
      change ((values p raws j).filter (fun z => decide (p^(j+1) ∣ x-(raws.getD i 0+p*z)))).map _ = _
      rw [hpred,ih]
      simp only [List.map_map,Function.comp_def]
    · simp only [hd,decide_false,ite_false]
      apply List.filter_eq_nil_iff.mpr
      intro z hz
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hz
      simp only [Bool.not_eq_true,decide_eq_false_iff_not]
      intro h
      exact hd ((Radix.radix_divisibility p _ _ _ hp j).mp h).1

theorem values_fiber_cap (p : ℤ) (hp : p ≠ 0) (raws : List ℤ) (C : ℕ)
    (hcap : ∀ x, (localBucket p raws x).length ≤ C) (J : ℕ) (x : ℤ) :
    ((values p raws J).filter (fun z => p^J ∣ x-z)).length ≤ C^J := by
  rw [filtered_values p hp,List.length_map]
  exact wantedOutputs_length_le p raws C hcap J x
theorem source_values_fiber_cap {L p : ℕ} [Fact p.Prime]
    {α : TernaryJointType.DigitType} {I : Type*} [Fintype I] [DecidableEq I]
    (right : Bool) (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2<p) (J : ℕ) (x : ℤ) :
    ((values (p : ℤ)
      ((TernaryCanonicalDictionaries.records (α := α) right maps B).map
        (TernaryCanonicalDictionaries.native right maps)) J).filter
      (fun z => (p : ℤ)^J ∣ x-z)).length ≤ (Fintype.card I*B)^J := by
  exact values_fiber_cap (p : ℤ) (by exact_mod_cast (by omega : p≠0)) _ _
    (local_native_cap right maps B hp) J x

end ThreeSum.TernaryWantedDictionaryFiber
