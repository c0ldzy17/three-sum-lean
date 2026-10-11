import Submission.ThreeSum.LightReportingSuffixBoxes
import Submission.ThreeSum.LocalGraph

/-!
# Exact prefix catalog keys and sharing for fixed source occurrences

A catalog key consists only of the first k ordered disjoint balanced row
pairs. Its exact cardinality is (microOutputs*microPartitions)^k. Neither the
remaining output rows nor the wanted A-index enter a local box table once
the global occurrence vector is fixed.
-/

namespace ThreeSum.ReportingHostPrefixCatalog

open Finset LocalGraph LayerCounts BlockRows BlockIndex BlockIndexedQuery
open BlockEncoding BlockForced GlobalEncoding StoredReporting ReportingHostSuffix

set_option linter.unusedSectionVars false

abbrev Prefix (h k : ℕ) := Fin k → Edge (512*h) h

theorem prefix_card (h k : ℕ) :
    Fintype.card (Prefix h k) = ((512*h).choose (2*h)*(2*h).choose h)^k := by
  simp only [Prefix,Fintype.card_fun,Fintype.card_fin,LocalGraph.edge_card]

def leftRows {h J k : ℕ} (p : Prefix h k) : Fin J → Finset (Fin (512*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.1 else ∅

def rightRows {h J k : ℕ} (p : Prefix h k) : Fin J → Finset (Fin (512*h)) :=
  fun i => if hi : i.val < k then (p ⟨i.val,hi⟩).val.2 else ∅

def leftSet {h J k : ℕ} (p : Prefix h k) : Finset (Fin (J*(512*h))) :=
  leftPrefix k (leftRows p)

def rightSet {h J k : ℕ} (p : Prefix h k) : Finset (Fin (J*(512*h))) :=
  leftPrefix k (rightRows p)

theorem leftSet_card {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    (leftSet (J := J) p).card = k*h := by
  apply leftPrefix_card hk
  intro i hi
  simp only [leftRows,dif_pos (mem_prefixIndices.mp hi)]
  exact (edge_data _).1

theorem rightSet_card {h J k : ℕ} (hk : k ≤ J) (p : Prefix h k) :
    (rightSet (J := J) p).card = k*h := by
  apply leftPrefix_card hk
  intro i hi
  simp only [rightRows,dif_pos (mem_prefixIndices.mp hi)]
  exact (edge_data _).2.1

def ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) : Prefix h k :=
  fun i =>
    let j : Fin J := ⟨i.val,i.isLt.trans_le hk⟩
    ⟨(prefixRows pre j,outputRows q j \ prefixRows pre j),by
      have hu := hp.2 j i.isLt
      have hQ : (outputRows q j).card = 2*h := LayerCounts.mem_vertices.mp (q j).2.property
      apply LayerCounts.mem_edgeSet.mpr
      refine ⟨hu.2,?_,disjoint_sdiff_self_right⟩
      rw [Finset.card_sdiff_of_subset hu.1,hQ,hu.2]
      omega⟩

theorem leftSet_ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    leftSet (ofValidPrefix hk q pre hp) = leftPrefix k (prefixRows (J := J) pre) := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J (512*h)).surjective x
  simp only [leftSet,leftPrefix,prefixLeft,mem_indexSet,mem_join,mem_prefixIndices]
  by_cases hi : i.val < k
  · simp only [hi,true_and,leftRows,dif_pos hi,ofValidPrefix]
  · simp only [hi,false_and]

theorem rightSet_ofValidPrefix {h J k : ℕ} (hk : k ≤ J) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    rightSet (ofValidPrefix hk q pre hp) =
      rightPrefix k (outputRows q) (prefixRows (J := J) pre) := by
  ext x
  obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J (512*h)).surjective x
  simp only [rightSet,leftPrefix,rightPrefix,prefixLeft,prefixRight,mem_indexSet,mem_join,mem_prefixIndices]
  by_cases hi : i.val < k
  · simp only [hi,true_and,rightRows,dif_pos hi,ofValidPrefix]
  · simp only [hi,false_and]

section Sources

variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def leftSourceOf {h J : ℕ} (o : Occurrences h J) (P : ℤ) (B : Finset β) (b : β → ℤ) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h)) (fun S => (leftWeights o P B b S : ℤ))

def rightSourceOf {h J : ℕ} (o : Occurrences h J) (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) :
    Finset (Fin (J*(512*h))) → ℤ :=
  SubsetTransport.reindex (coordEquiv J (512*h)) (fun S => (rightWeights o P shift C c S : ℤ))

theorem leftSource_eq {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ) (q : GlobalOutput h J) :
    leftSource P B b q = leftSourceOf (outputOccurrences q) P B b := rfl

theorem rightSource_eq {h J : ℕ} (P shift : ℤ) (C : Finset γ) (c : γ → ℤ) (q : GlobalOutput h J) :
    rightSource P shift C c q = rightSourceOf (outputOccurrences q) P shift C c := rfl

theorem leftSource_eq_of_occurrences {h J : ℕ} (P : ℤ) (B : Finset β) (b : β → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q = outputOccurrences q') :
    leftSource P B b q = leftSource P B b q' := by rw [leftSource_eq,leftSource_eq,ho]

theorem rightSource_eq_of_occurrences {h J : ℕ} (P shift : ℤ) (C : Finset γ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} (ho : outputOccurrences q = outputOccurrences q') :
    rightSource P shift C c q = rightSource P shift C c q' := by rw [rightSource_eq,rightSource_eq,ho]

def leaf {h J k : ℕ} (hk : k ≤ J) (o : Occurrences h J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ) (p : Prefix h k) :
    Finset (Fin ((J-k)*(512*h))) → ℤ :=
  leafWeight (block_fit hk) (leftSourceOf o P B b) (rightSourceOf o P shift C c)
    (suffixStage J (512*h) k) (leftSet p) (rightSet p)

theorem localLeaf_eq_catalogLeaf {h J k : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) :
    LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre =
      leaf hk (outputOccurrences q) P shift B C b c (ofValidPrefix hk q pre hp) := by
  unfold LightReportingSuffixBoxes.localLeaf leaf
  rw [leftSet_ofValidPrefix,rightSet_ofValidPrefix,leftSource_eq,rightSource_eq]
  rfl

theorem localLeaf_shared {h J k : ℕ} (hk : k ≤ J)
    (P shift : ℤ) (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    {q q' : GlobalOutput h J} {pre pre' : List (Finset (Fin (512*h)))}
    (hp : ValidPrefix q k pre) (hp' : ValidPrefix q' k pre')
    (ho : outputOccurrences q = outputOccurrences q')
    (hkey : ofValidPrefix hk q pre hp = ofValidPrefix hk q' pre' hp') :
    LightReportingSuffixBoxes.localLeaf hk P shift B C b c q pre =
      LightReportingSuffixBoxes.localLeaf hk P shift B C b c q' pre' := by
  rw [localLeaf_eq_catalogLeaf hk P shift B C b c q pre hp,
    localLeaf_eq_catalogLeaf hk P shift B C b c q' pre' hp',ho,hkey]

end Sources

end ThreeSum.ReportingHostPrefixCatalog
