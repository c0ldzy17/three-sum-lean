import Submission.ThreeSum.RadixKeyLists
import Submission.ThreeSum.LocalMaskGraph
import Mathlib.Data.List.FinRange
import Mathlib.Data.List.ProdSigma

/-!
# Literal global-output records behind the radix key array

Local records use the verified layer enumerator's order and retain every
schedule occurrence. Cartesian extension enumerates each original global
output once. Mapping to integers may introduce equal values; the key array
retains all of those separate incidences.
-/

namespace ThreeSum.GlobalKeyEnumeration

open GlobalEncoding LocalGraph LocalCoverBounds LocalHashMoments
open RadixKeyLists
open scoped BigOperators

set_option maxHeartbeats 1800000

def layerRecord (h : ℕ) (i : Fin ((512*h).choose (2*h))) :
    {Q // Q ∈ LayerCounts.vertices (512*h) (2*h)} :=
  ⟨LocalMaskGraph.setAt (512*h) (2*h) i,
    LayerCounts.mem_vertices.mpr (LocalMaskGraph.setAt_card i.isLt)⟩

theorem layerRecord_injective (h : ℕ) : Function.Injective (layerRecord h) := by
  intro i j he
  apply Fin.ext
  exact LocalMaskGraph.setAt_injective i.isLt j.isLt (congrArg Subtype.val he)

theorem layerRecord_surjective (h : ℕ) : Function.Surjective (layerRecord h) := by
  intro Q
  obtain ⟨i,hi,he⟩ := LocalMaskGraph.setAt_complete Q.val
    (LayerCounts.mem_vertices.mp Q.property)
  exact ⟨⟨i,hi⟩,Subtype.ext he⟩

def layers (h : ℕ) := List.ofFn (layerRecord h)

theorem layers_length (h : ℕ) : (layers h).length=outputCount (512*h) h := by
  simp [layers,outputCount]

theorem mem_layers (h : ℕ) (Q : {Q // Q ∈ LayerCounts.vertices (512*h) (2*h)}) :
    Q ∈ layers h := by
  obtain ⟨i,rfl⟩ := layerRecord_surjective h Q
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

theorem layers_nodup (h : ℕ) : (layers h).Nodup :=
  List.nodup_ofFn_ofInjective (layerRecord_injective h)

def localRecords (h : ℕ) : List (OutputBlock h) :=
  (List.finRange (scheduleSize h)).product (layers h)

theorem localRecords_length (h : ℕ) :
    (localRecords h).length=scheduleSize h*outputCount (512*h) h := by
  calc
    _ = (List.finRange (scheduleSize h)).length*(layers h).length :=
      List.length_product _ _
    _ = _ := by rw [List.length_finRange,layers_length]

theorem mem_localRecords (h : ℕ) (b : OutputBlock h) : b ∈ localRecords h := by
  exact List.mem_product.mpr ⟨List.mem_finRange _,mem_layers h b.2⟩

theorem localRecords_nodup (h : ℕ) : (localRecords h).Nodup :=
  (List.nodup_finRange _).product (layers_nodup h)

def localKeys (h : ℕ) : List ℤ := (localRecords h).map blockKey

def tupleOfList {α : Type*} {J : ℕ} (xs : List α) (hlen : xs.length=J) : Fin J → α :=
  fun i => xs.get (Fin.cast hlen.symm i)

theorem ofFn_tupleOfList {α : Type*} {J : ℕ} (xs : List α) (hlen : xs.length=J) :
    List.ofFn (tupleOfList xs hlen)=xs := by
  subst J
  exact List.ofFn_get xs

def globalRecords (h J : ℕ) : List (GlobalOutput h J) :=
  (tuples (localRecords h) J).attach.map fun xs =>
    tupleOfList xs.val ((mem_tuples _ _ _).mp xs.property).1

theorem globalRecords_length (h J : ℕ) :
    (globalRecords h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  simp [globalRecords,tuples_length,localRecords_length,mul_pow]

theorem mem_globalRecords (h J : ℕ) (q : GlobalOutput h J) :
    q ∈ globalRecords h J := by
  have hx : List.ofFn q ∈ tuples (localRecords h) J :=
    (mem_tuples _ _ _).mpr ⟨List.length_ofFn,fun b _ => mem_localRecords h b⟩
  apply List.mem_map.mpr
  refine ⟨⟨List.ofFn q,hx⟩,by simp,?_⟩
  funext i
  simp [tupleOfList]

theorem globalRecords_nodup (h J : ℕ) : (globalRecords h J).Nodup := by
  apply ((tuples_nodup _ (localRecords_nodup h) J).attach).map
  intro xs ys he
  apply Subtype.ext
  have he' := congrArg List.ofFn he
  simpa only [ofFn_tupleOfList] using he'

def globalKeys (h J : ℕ) : List ℤ :=
  values (localPrime h : ℤ) (localKeys h) J

/-- Exact array identity, not merely equality of the set of key values. -/
theorem globalKeys_eq_map (h J : ℕ) :
    globalKeys h J=(globalRecords h J).map globalKey := by
  rw [globalKeys,localKeys,values_eq_map]
  unfold globalRecords
  rw [List.map_map]
  symm
  calc
    _ = (tuples (localRecords h) J).attach.map
        (fun xs => Radix.positionalHash (localPrime h) blockKey xs.val) := by
      apply List.map_congr_left
      intro xs _
      simp only [Function.comp_def,globalKey,ofFn_tupleOfList]
    _ = _ := by simp

theorem globalKeys_length (h J : ℕ) :
    (globalKeys h J).length=scheduleSize h^J*outputCount (512*h) h^J := by
  rw [globalKeys_eq_map,List.length_map,globalRecords_length]

theorem rawOutput_abs_le {h L : ℕ} (w : Weight L (LocalField h))
    (Q : Finset (Fin L)) : |rawOutput w Q| ≤ ((L*localPrime h : ℕ) : ℤ) := by
  unfold rawOutput
  calc
    _ ≤ ∑ i : Fin L, |if i ∈ Q then (0 : ℤ) else
        ((w (i,true)).val : ℤ)-((w (i,false)).val : ℤ)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin L, (localPrime h : ℤ) := by
      apply Finset.sum_le_sum
      intro i _
      by_cases hi : i ∈ Q
      · simp [hi]
      · simp only [hi,ite_false]
        have ht : ((w (i,true)).val : ℤ) < (localPrime h : ℤ) := by
          exact_mod_cast (w (i,true)).val_lt
        have hf : ((w (i,false)).val : ℤ) < (localPrime h : ℤ) := by
          exact_mod_cast (w (i,false)).val_lt
        exact abs_le.mpr ⟨by omega,by omega⟩
    _ = _ := by simp

theorem localKeys_bounded (h : ℕ) :
    ∀ x ∈ localKeys h, |x| ≤ ((512*h*localPrime h : ℕ) : ℤ) := by
  intro x hx
  obtain ⟨b,_,rfl⟩ := List.mem_map.mp hx
  exact rawOutput_abs_le _ _

theorem globalKeys_bounded (h J : ℕ) :
    ∀ x ∈ globalKeys h J,
      |x| ≤ (((512*h*localPrime h)*(localPrime h+1)^J : ℕ) : ℤ) :=
  values_bounded _ _ _ (localKeys_bounded h) J

end ThreeSum.GlobalKeyEnumeration
