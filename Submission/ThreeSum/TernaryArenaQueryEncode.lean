import Submission.ThreeSum.TernaryArenaQueryNative
import Submission.ThreeSum.TernaryWantedBatchInverse

noncomputable section
namespace ThreeSum.TernaryArenaQueryEncode
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaQueryModel TernaryGoodOutputCatalog
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 3000000
variable {p m F r : ℕ} [Fact p.Prime]

/-- Every retained output tuple with a literal original target has one
actual DFS output ordinal, retaining its target/carry occurrence. -/
theorem exists_query (maps : Fin F→Weight m p) (τ : ℕ) (targets : ℕ→ℤ)
    (positions : ℕ→ℕ) (n t : ℕ) (ht : t<n)
    (xs : Fin r→Record m (Fin F)) (hx : ∀ i, xs i∈records maps τ)
    (hdiv : (p : ℤ)^r∣targets t-Radix.positionalHash (p : ℤ) (key maps) (List.ofFn xs)) :
    ∃ j : Fin (queries (r := r) maps τ targets positions n).length,
      (descriptor maps τ targets positions n j).1=t ∧ block maps τ targets positions n j=xs := by
  let ix : Fin r→ℕ := fun i => (records maps τ).idxOf (xs i)
  have hi (i : Fin r) : ix i<(records maps τ).length := List.idxOf_lt_length_iff.mpr (hx i)
  have hget (i : Fin r) : (records maps τ)[ix i]'(hi i)=xs i := by simp [ix]
  have hr (i : Fin r) : (raws maps τ).getD (ix i) 0=key maps (xs i) := by
    rw [List.getD_eq_getElem _ _ (by simpa using hi i)]
    simp only [raws,List.getElem_map,hget]
  have hpoly : Radix.positionalHash (p : ℤ) (fun k => (raws maps τ).getD k 0) (List.ofFn ix)=
      Radix.positionalHash (p : ℤ) (key maps) (List.ofFn xs) := by
    calc
      _ = Radix.positionalHash (p : ℤ) id
          ((List.ofFn ix).map (fun k => (raws maps τ).getD k 0)) :=
        TernaryNativeTupleWitness.positional_map _ _ id _
      _ = Radix.positionalHash (p : ℤ) id ((List.ofFn xs).map (key maps)) := by
        congr 1
        simp only [List.map_ofFn]
        exact List.ofFn_inj.mpr (funext hr)
      _ = _ := (TernaryNativeTupleWitness.positional_map _ _ id _).symm

  have hw : List.ofFn ix∈TernaryWantedRadix.wantedOutputs (p : ℤ) (raws maps τ) r (targets t) := by
    apply (TernaryWantedRadix.mem_wantedOutputs (p : ℤ)
      (by exact_mod_cast (Fact.out : p.Prime).ne_zero) _ _ _ _).mpr
    refine ⟨by simp,?_,by simpa only [hpoly] using hdiv⟩
    intro k hk
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hk
    simpa using hi i
  have hd : (t,List.ofFn ix)∈TernaryWantedBatchProvenance.descriptors p r (raws maps τ) targets n :=
    (TernaryWantedBatchProvenance.mem_descriptors p r (raws maps τ) targets n _).mpr ⟨ht,hw⟩
  obtain ⟨j,hj⟩ := TernaryWantedBatchInverse.exists_decode p (4^fixedLength m) F r (raws maps τ)
    (wordCodes maps τ) (mapCodes maps τ) targets positions n (t,List.ofFn ix) hd
  refine ⟨j,congrArg Prod.fst hj,?_⟩
  funext i
  change (records maps τ)[(descriptor maps τ targets positions n j).2[i.val]'_]'_=xs i
  have hjs : (descriptor maps τ targets positions n j).2=List.ofFn ix := congrArg Prod.snd hj
  simp only [hjs,List.getElem_ofFn]
  exact hget i

end ThreeSum.TernaryArenaQueryEncode
