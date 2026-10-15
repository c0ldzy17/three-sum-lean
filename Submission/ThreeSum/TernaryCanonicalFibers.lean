import Submission.ThreeSum.TernaryCanonicalDictionaries
import Submission.ThreeSum.TernaryWantedRadix

noncomputable section
namespace ThreeSum.TernaryCanonicalFibers
open Finset TernaryFixedDictionaries TernaryCanonicalDictionaries TernaryJointType TernaryCoverLocal
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

def rightNativeFiber (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p) (B : ℕ)
    (a : ZMod p) : Finset (SourceRecord L α I) := by
  classical
  exact univ.filter fun r => acceptedRight maps B r ∧ rightNative maps r = a

theorem right_native_fiber_cap (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (a : ZMod p) :
    (rightNativeFiber (α := α) maps B a).card ≤ Fintype.card I*B := by
  classical
  have hi (i : I) : ((rightNativeFiber (α := α) maps B a).filter fun r => r.1 = i).card ≤ B := by
    let F := (rightNativeFiber (α := α) maps B a).filter fun r => r.1 = i
    by_cases hz : F.card = 0
    · change F.card ≤ B
      rw [hz]
      exact Nat.zero_le B
    obtain ⟨r0,hr0⟩ := card_pos.mp (Nat.pos_of_ne_zero hz)
    obtain ⟨hr0,hi0⟩ := mem_filter.mp hr0
    have hdata := (mem_filter.mp hr0).2
    have hb : TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.rightVector (maps i) a ≤ B := by
      have h := hdata.1
      change TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.rightVector (maps r0.1) (rightNative maps r0) ≤ B at h
      simpa [hi0,hdata.2] using h
    have hc : F.card ≤ TernaryCoverTrimming.bucketSize (fieldVertices L p α)
        TernaryCoverHashes.rightVector (maps i) a := by
      unfold TernaryCoverTrimming.bucketSize
      apply card_le_card_of_injOn (fun r : SourceRecord L α I => fieldWord p r.2.val)
      · intro r hr
        obtain ⟨hr,hri⟩ := mem_filter.mp hr
        have hn := (mem_filter.mp hr).2.2
        apply mem_filter.mpr
        refine ⟨?_,?_⟩
        · exact mem_image.mpr ⟨r.2.val,r.2.property,rfl⟩
        · simpa [rightNative,hri] using hn
      · intro r hr t ht h
        apply Prod.ext
        · exact (mem_filter.mp hr).2.trans (mem_filter.mp ht).2.symm
        · apply Subtype.ext
          exact fieldWord_injective hp h
    exact hc.trans hb
  calc
    _ = ∑ i : I, ((rightNativeFiber (α := α) maps B a).filter fun r => r.1 = i).card :=
      card_eq_sum_card_fiberwise (fun _ _ => mem_univ _)
    _ ≤ ∑ _i : I, B := sum_le_sum (fun i _ => hi i)
    _ = _ := by simp


theorem map_range_getD {A : Type*} (xs : List A) (fallback : A) :
    (List.range xs.length).map (fun i => xs.getD i fallback)=xs := by
  apply List.ext_getElem (by simp)
  intro i hi hi'
  simp only [List.getD,List.getElem_map,List.getElem_range,List.getElem?_eq_getElem hi',Option.getD_some]

theorem localBucket_length (p : ℤ) (raws : List ℤ) (x : ℤ) :
    (TernaryWantedRadix.localBucket p raws x).length=
      (raws.filter (fun z => p ∣ x-z)).length := by
  have h : ((TernaryWantedRadix.localBucket p raws x).map (fun i => raws.getD i 0)) =
      raws.filter (fun z => p ∣ x-z) := by
    change ((List.range raws.length).filter
      ((fun z : ℤ => decide (p ∣ x-z)) ∘ (fun i => raws.getD i 0))).map
        (fun i => raws.getD i 0) = _
    rw [← List.filter_map,map_range_getD]
  simpa only [List.length_map] using congrArg List.length h

theorem native_cast (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (r : SourceRecord L α I) :
    ((native right maps r : ℤ) : ZMod p)=
      if right then rightNative maps r else leftNative maps r := by
  unfold native
  simp only [Int.cast_natCast,ZMod.natCast_zmod_val]

/-- The concrete trimmed table pays for every occurrence, including maps
with identical coefficients and vertices with equal integer key labels. -/
theorem native_filter_cap (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (x : ℤ) :
    ((records (α := α) right maps B).filter
      (fun r => (p : ℤ) ∣ x-native right maps r)).length ≤ Fintype.card I*B := by
  classical
  cases right with
  | false =>
    let rs := trimmedLeftRecords (α := α) maps B
    let selected := rs.filter (fun r => (p : ℤ) ∣ x-native false maps r)
    have hn : selected.Nodup := by
      apply List.Nodup.filter
      exact Finset.nodup_toList _
    have hc : selected.toFinset.card=selected.length := List.toFinset_card_of_nodup hn
    have hsub : selected.toFinset ⊆ leftNativeFiber (α := α) maps B (x : ZMod p) := by
      intro r hr
      obtain ⟨hr,hdiv⟩ := List.mem_filter.mp (List.mem_toFinset.mp hr)
      have ha : acceptedLeft maps B r := by
        simpa only [rs,trimmedLeftRecords,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using hr
      have he : leftNative maps r=(x : ZMod p) := by
        have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (native false maps r) x p).mpr
          (of_decide_eq_true hdiv)
        simpa only [native_cast,Bool.false_eq_true,if_false] using h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,he⟩
    change selected.length ≤ _
    rw [← hc]
    exact (Finset.card_le_card hsub).trans (left_native_fiber_cap maps B hp _)
  | true =>
    let rs := trimmedRightRecords (α := α) maps B
    let selected := rs.filter (fun r => (p : ℤ) ∣ x-native true maps r)
    have hn : selected.Nodup := by
      apply List.Nodup.filter
      exact Finset.nodup_toList _
    have hc : selected.toFinset.card=selected.length := List.toFinset_card_of_nodup hn
    have hsub : selected.toFinset ⊆ rightNativeFiber (α := α) maps B (x : ZMod p) := by
      intro r hr
      obtain ⟨hr,hdiv⟩ := List.mem_filter.mp (List.mem_toFinset.mp hr)
      have ha : acceptedRight maps B r := by
        simpa only [rs,trimmedRightRecords,Finset.mem_toList,Finset.mem_filter,Finset.mem_univ,true_and] using hr
      have he : rightNative maps r=(x : ZMod p) := by
        have h := (ZMod.intCast_eq_intCast_iff_dvd_sub (native true maps r) x p).mpr
          (of_decide_eq_true hdiv)
        simpa only [native_cast,if_true] using h
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,he⟩
    change selected.length ≤ _
    rw [← hc]
    exact (Finset.card_le_card hsub).trans (right_native_fiber_cap maps B hp _)

theorem local_native_cap (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (x : ℤ) :
    (TernaryWantedRadix.localBucket (p : ℤ)
      ((records (α := α) right maps B).map (native right maps)) x).length ≤ Fintype.card I*B := by
  rw [localBucket_length,List.filter_map,List.length_map]
  exact native_filter_cap right maps B hp x

theorem source_tuple_fiber_cap (right : Bool)
    (maps : I → TernaryCoverHashes.Coordinate (Fin L) → ZMod p)
    (B : ℕ) (hp : 2 < p) (J : ℕ) (x : ℤ) :
    (TernaryWantedRadix.wantedOutputs (p : ℤ)
      ((records (α := α) right maps B).map (native right maps)) J x).length ≤
      (Fintype.card I*B)^J :=
  TernaryWantedRadix.wantedOutputs_length_le _ _ _ (local_native_cap right maps B hp) J x

end ThreeSum.TernaryCanonicalFibers
