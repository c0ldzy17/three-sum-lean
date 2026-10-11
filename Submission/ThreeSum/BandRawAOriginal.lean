import Submission.ThreeSum.BandRawAScore
import Submission.ThreeSum.LightSortedBands

/-!
# Exact original-value membership and equation coverage of the owner catalog

Normalized sorted coordinates remain distinct from original input
positions. The normalization membership equivalence transfers values back
to their original color classes; the color-class bridge can then recover
the required distinct original positions.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows BandEnumeration BandPartition Finset
open scoped BigOperators

set_option maxHeartbeats 1800000
set_option maxRecDepth 8000

def sortedRecords (A B C : List ℤ) (g : ℕ) (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) : List Record :=
  records (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
    (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
    (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC))

theorem product_values_mem {A B C : List ℤ} {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ A ∧
      B.getD t.2.1 0 ∈ B ∧ C.getD t.2.2 0 ∈ C := by
  obtain ⟨ha,hb,hc⟩ := mem_allProducts.mp ht
  have hap := position_lt (at_mem ha)
  have hbp := bandPositions_lt hb
  have hcp := bandPositions_lt hc
  refine ⟨?_,?_,?_⟩
  · rw [valueAt,values_getD _ ha,List.getD_eq_getElem _ _ hap]
    exact List.getElem_mem hap
  · rw [List.getD_eq_getElem _ _ hbp]
    exact List.getElem_mem hbp
  · rw [List.getD_eq_getElem _ _ hcp]
    exact List.getElem_mem hcp

theorem product_original_values {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ allProducts A.length B.length C.length g rs) :
    valueAt A.length g rs (fun i => A.getD i 0) t.1 ∈ originalA ∧
      B.getD t.2.1 0 ∈ originalB ∧ C.getD t.2.2 0 ∈ originalC := by
  obtain ⟨ha,hb,hc⟩ := product_values_mem ht
  exact ⟨(hA _).mp ha,(hB _).mp hb,(hC _).mp hc⟩

theorem sorted_equation_complete {A B C : List ℤ} {g : ℕ} {a b c : ℤ}
    (hg : 0 < g) (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·))
    (hsC : C.Pairwise (· < ·)) (ha : a ∈ A) (hb : b ∈ B) (hc : c ∈ C)
    (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c := by
  obtain ⟨ia,hia,hA⟩ := List.mem_iff_getElem.mp ha
  obtain ⟨ib,hib,hB⟩ := List.mem_iff_getElem.mp hb
  obtain ⟨ic,hic,hC⟩ := List.mem_iff_getElem.mp hc
  have hAget : A.getD ia 0=a := (List.getD_eq_getElem A 0 hia).trans hA
  have hBget : B.getD ib 0=b := (List.getD_eq_getElem B 0 hib).trans hB
  have hCget : C.getD ic 0=c := (List.getD_eq_getElem C 0 hic).trans hC
  let FA := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let FB := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let FC := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  let band : Triple FA FB FC :=
    (⟨ia/g,index_lt_size hia⟩,⟨ib/g,index_lt_size hib⟩,⟨ic/g,index_lt_size hic⟩)
  have hAband : FA.lo band.1 ≤ a ∧ a ≤ FA.hi band.1 := by
    simpa only [FA,band,Family.lo,Family.hi,hAget] using covers (fun i => A.getD i 0) A.length g hg
      (LightSortedBands.getD_strict hsA) hia
  have hBband : FB.lo band.2.1 ≤ b ∧ b ≤ FB.hi band.2.1 := by
    simpa only [FB,band,Family.lo,Family.hi,hBget] using covers (fun i => B.getD i 0) B.length g hg
      (LightSortedBands.getD_strict hsB) hib
  have hCband : FC.lo band.2.2 ≤ c ∧ c ≤ FC.hi band.2.2 := by
    simpa only [FC,band,Family.lo,Family.hi,hCget] using covers (fun i => C.getD i 0) C.length g hg
      (LightSortedBands.getD_strict hsC) hic
  have hrel : relevant FA FB FC band := Bands.exact_equation_relevant hAband hBband hCband heq
  have hap : start g band.1.val ≤ ia ∧ ia < stop A.length g band.1.val := index_bounds hg hia
  have hbp : start g band.2.1.val ≤ ib ∧ ib < stop B.length g band.2.1.val := index_bounds hg hib
  have hcp : start g band.2.2.val ≤ ic ∧ ic < stop C.length g band.2.2.val := index_bounds hg hic
  obtain ⟨k,hk,hlabel,hproduct⟩ := relevant_product_complete band hrel hap hbp hcp
  have hs : slot FA FB FC (owner FA FB FC band) < (records FA FB FC).length := by
    rw [records_length]
    exact slot_lt FA FB FC _
  have hall : (k,ib,ic) ∈ allProducts A.length B.length C.length g (records FA FB FC) :=
    mem_biUnion.mpr ⟨slot FA FB FC (owner FA FB FC band),mem_range.mpr hs,hproduct⟩
  refine ⟨(k,ib,ic),hall,?_,hBget,hCget⟩
  change valueAt A.length g (records FA FB FC) (fun i => A.getD i 0) k=a
  rw [valueAt,values_getD _ hk,hlabel]
  exact hAget

theorem original_equation_complete {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {a b c : ℤ} (hg : 0 < g)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·))
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ha : a ∈ originalA) (hb : b ∈ originalB) (hc : c ∈ originalC) (heq : a+b=c) :
    ∃ t ∈ allProducts A.length B.length C.length g (sortedRecords A B C g hg hsA hsB hsC),
      valueAt A.length g (sortedRecords A B C g hg hsA hsB hsC)
        (fun i => A.getD i 0) t.1=a ∧ B.getD t.2.1 0=b ∧ C.getD t.2.2 0=c :=
  sorted_equation_complete hg hsA hsB hsC ((hA a).mpr ha) ((hB b).mpr hb) ((hC c).mpr hc) heq

theorem original_equation_sound {originalA originalB originalC A B C : List ℤ}
    {g : ℕ} {rs : List Record} {t : ℕ × ℕ × ℕ}
    (hA : ∀ z, z ∈ A ↔ z ∈ originalA) (hB : ∀ z, z ∈ B ↔ z ∈ originalB)
    (hC : ∀ z, z ∈ C ↔ z ∈ originalC)
    (ht : t ∈ allProducts A.length B.length C.length g rs)
    (heq : valueAt A.length g rs (fun i => A.getD i 0) t.1+B.getD t.2.1 0=C.getD t.2.2 0) :
    ∃ a ∈ originalA, ∃ b ∈ originalB, ∃ c ∈ originalC, a+b=c := by
  obtain ⟨ha,hb,hc⟩ := product_original_values hA hB hC ht
  exact ⟨_,ha,_,hb,_,hc,heq⟩

end ThreeSum.BandRawA
