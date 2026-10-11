import Submission.ThreeSum.ReportingHostTerminalChoices

/-!
# Actual terminal completion mask arrays

The existing exact coordinate enumerator is applied to the entire remaining
query set. It emits both full endpoint masks, so the independent endpoint
and bucket-test constructors can consume them without constructing tuples
or invoking an oracle. Every original retained completion occurs.
-/

namespace ThreeSum.LightReportingTerminalMasks

open Light Finset BlockRows BlockIndex BlockEncoding BlockForced BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts
open QueryCoordinates ReportingHostTerminalChoices ThreeSum.SubsetAddress

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def choiceAt {h J : ℕ} (q : GlobalOutput h J) (k i : ℕ) : Finset (Coord J (512*h)) :=
  (choices q k)[i]?.getD ∅

def leftAt {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512*h)))) (i : ℕ) : Finset (Coord J (512*h)) :=
  prefixLeft (prefixIndices J k) (prefixRows pre) ∪ choiceAt q k i

def rightAt {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (pre : List (Finset (Fin (512*h)))) (i : ℕ) : Finset (Coord J (512*h)) :=
  prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
    (remaining (prefixIndices J k) (outputRows q) \ choiceAt q k i)

def count (h J k : ℕ) : ℕ := ((J-k)*(2*h)).choose ((J-k)*h)
def time (h J k : ℕ) : ℕ := LightBlockChildren.time (J*(512*h)) ((J-k)*(2*h)) ((J-k)*h)
def program : Program := LightBlockChildren.program

theorem choiceAt_eq_get {h J k i : ℕ} (q : GlobalOutput h J) (hi : i<(choices q k).length) :
    choiceAt q k i=(choices q k)[i] := by
  simp only [choiceAt,List.getElem?_eq_getElem hi,Option.getD_some]

theorem completion_index {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k≤J) (hp : ValidPrefix q k pre)
    (t : ChoiceTuple h J) (ht : t∈completions q k pre) :
    ∃ i<count h J k, leftAt q k pre i=leftSubset t ∧ rightAt q k pre i=rightSubset t := by
  obtain ⟨i,hi,hget⟩ := List.mem_iff_getElem.mp (completion_residual_mem q pre hk t ht)
  refine ⟨i,by simpa only [choices_length q hk,count] using hi,?_⟩
  rw [leftAt,rightAt,choiceAt_eq_get q hi,hget]
  exact completion_endpoints q pre hk hp t ht

private theorem leftMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) :
    LightBlockChildren.leftMasks (leftPrefix k (prefixRows pre)) (querySet k (outputRows q)) ((J-k)*h)=
      (choices q k).map (fun S => subsetMask (indexSet (prefixLeft (prefixIndices J k) (prefixRows pre) ∪ S))) := by
  simp only [LightBlockChildren.leftMasks,choices,List.map_map]
  apply List.map_congr_left
  intro S _
  simp only [Function.comp_apply,indexSet_union,index_unindex,leftPrefix]

private theorem rightMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) :
    LightBlockChildren.rightMasks (rightPrefix k (outputRows q) (prefixRows pre))
      (querySet k (outputRows q)) ((J-k)*h)=
      (choices q k).map (fun S => subsetMask (indexSet
        (prefixRight (prefixIndices J k) (outputRows q) (prefixRows pre) ∪
          (remaining (prefixIndices J k) (outputRows q) \ S)))) := by
  simp only [LightBlockChildren.rightMasks,choices,List.map_map,indexSet_union]
  apply List.map_congr_left
  intro S _
  congr 2
  change querySet k (outputRows q) \ S=indexSet (remaining (prefixIndices J k) (outputRows q) \ unindexSet S)
  simp only [indexSet,Finset.map_sdiff]
  rw [show (unindexSet S).map (coordEquiv J (512*h)).toEmbedding=S from index_unindex S]
  rfl

variable {lim : Limits} {d : ℕ}

theorem program_meets {μ : ℕ→ℤ} {h J k masks dstL dstR work : ℕ}
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h)))) (hk : k≤J)
    (hw : (lim.space : ℤ)≤lim.word)
    (hmasks : masks+count h J k≤dstL) (hleft : dstL+count h J k≤dstR)
    (hright : dstR+count h J k≤work) (hspace : work+(2*(J*(512*h))+2)≤lim.space)
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ)≤lim.word) (hd : d+J*(512*h)+3≤lim.depth) :
    Meets lim program 0 d
      [((J*(512*h) : ℕ) : ℤ),(((J-k)*h : ℕ) : ℤ),subsetMask (querySet k (outputRows q)),
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows q)),masks,dstL,dstR,work]
      μ (time h J k) (fun r ν => r=0 ∧
        (∀ i<count h J k, ν (dstL+i)=(subsetMask (indexSet (leftAt q k pre i)) : ℤ)) ∧
        (∀ i<count h J k, ν (dstR+i)=(subsetMask (indexSet (rightAt q k pre i)) : ℤ)) ∧
        Kept μ ν masks) := by
  have hQ := querySet_card hk (outputRows q) (fun i => LayerCounts.mem_vertices.mp (q i).2.property)
  have hhalf : (J-k)*h ≤ (querySet k (outputRows q)).card+1 := by rw [hQ]; nlinarith
  have hrun := LightBlockChildren.program_meets (μ := μ) (h := (J-k)*h)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (querySet k (outputRows q)) (querySet k (outputRows q)) hw
    (leftPrefix_disjoint_query _ _ _) (rightPrefix_disjoint_query _ _ _) (Finset.Subset.refl _)
    hhalf (by simpa only [hQ,count] using hmasks) (by simpa only [hQ,count] using hleft)
    (by simpa only [hQ,count] using hright) hspace hword hd
  rw [hQ] at hrun
  apply hrun.mono le_rfl
  rintro r ν ⟨hr,_,hL,hR,hkeep⟩
  refine ⟨by simpa using hr,?_,?_,hkeep⟩
  · rw [leftMasks_eq] at hL
    intro i hi
    have hi' : i<(choices q k).length := by simpa only [choices_length q hk,count] using hi
    have hh := hL.getElem (i := i) (by simpa only [List.length_map] using hi')
    simpa only [List.getElem_map,leftAt,choiceAt_eq_get q hi'] using hh
  · rw [rightMasks_eq] at hR
    intro i hi
    have hi' : i<(choices q k).length := by simpa only [choices_length q hk,count] using hi
    have hh := hR.getElem (i := i) (by simpa only [List.length_map] using hi')
    simpa only [List.getElem_map,rightAt,choiceAt_eq_get q hi'] using hh

theorem time_bound (h J k : ℕ) :
    time h J k≤1600*(J*(512*h)+1)^2*(2^((J-k)*(2*h))+1) := by
  have hc : (J-k)*(2*h)≤J*(512*h) :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  exact (LightBlockChildren.time_bound (h := (J-k)*h) hc).trans
    (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.choose_le_two_pow _ _) 1))

end ThreeSum.LightReportingTerminalMasks
