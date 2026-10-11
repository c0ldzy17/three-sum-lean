import Submission.ThreeSum.LightBlockChildren
import Submission.ThreeSum.LightBlockQuery

/-! # The concrete child constructor extends the original valid reporting prefixes -/

namespace ThreeSum.LightBlockChildrenIndexed

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightSubsetAddress
open BlockRows BlockIndex BlockMaskLayout BlockIndexedQuery BlockForced StoredReporting
open ReportingHostMasks QueryCoordinates GlobalEncoding LocalCoverBounds

variable {lim : Limits}

def childPrefixes {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) :=
  (localChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h).map fun S => pre ++ [S]

theorem childPrefixes_length {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) :
    (childPrefixes q pre hk).length = groupSize h := by
  have hc : (outputRows q ⟨k,hk⟩).card = 2*h :=
    LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  simp [childPrefixes,hc,groupSize]

theorem childPrefixes_valid {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (next : List (Finset (Fin (512*h)))) (hn : next ∈ childPrefixes q pre hk) :
    ValidPrefix q (k+1) next := by
  obtain ⟨S,hS,rfl⟩ := List.mem_map.mp hn
  exact localChild_validPrefix q pre hp hk S hS

private theorem leftMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.leftMasks (leftPrefix k (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next => subsetMask (leftPrefix (k+1) (prefixRows (J := J) next)) := by
  simp only [LightBlockChildren.leftMasks,childPrefixes,localChildren,globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (missingSets_mem _ _ _).mp hT
  simp only [Function.comp_apply]
  rw [prefixRows_append pre hp hk,leftPrefix_step,
    blockSet_localRow _ _ ht.1]

private theorem rightMasks_eq {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.rightMasks (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next =>
        subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next)) := by
  simp only [LightBlockChildren.rightMasks,childPrefixes,localChildren,globalChildren,List.map_map]
  apply List.map_congr_left
  intro T hT
  have ht := (missingSets_mem _ _ _).mp hT
  have he : blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩ \ localRow ⟨k,hk⟩ T) =
      blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) \ T := by
    have heT := blockSet_localRow ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) ht.1
    conv_rhs => rw [← heT]
    ext x
    obtain ⟨⟨i,a⟩,rfl⟩ := (coordEquiv J (512*h)).surjective x
    simp only [mem_blockSet,Finset.mem_sdiff]
    tauto
  simp only [Function.comp_apply]
  rw [prefixRows_append pre hp hk,rightPrefix_step,he]

theorem leftMasks_eq_childPrefixes {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.leftMasks (leftPrefix k (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next => subsetMask (leftPrefix (k+1) (prefixRows (J := J) next)) :=
  leftMasks_eq q pre hp hk

theorem rightMasks_eq_childPrefixes {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : pre.length = k) (hk : k < J) :
    LightBlockChildren.rightMasks (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
        (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) h =
      (childPrefixes q pre hk).map fun next =>
        subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next)) :=
  rightMasks_eq q pre hp hk

def childAt {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) (i : ℕ) :=
  (childPrefixes q pre hk)[i]?.getD []

theorem childAt_eq_get {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k < J) (i : ℕ) (hi : i < groupSize h) :
    childAt q pre hk i = (childPrefixes q pre hk)[i]'(by rw [childPrefixes_length]; exact hi) := by
  have hib : i < (childPrefixes q pre hk).length := by rw [childPrefixes_length]; exact hi
  simp only [childAt,List.getElem?_eq_getElem hib,Option.getD_some]

theorem childAt_valid {h J k : ℕ} (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hp : ValidPrefix q k pre) (hk : k < J)
    (i : ℕ) (hi : i < groupSize h) : ValidPrefix q (k+1) (childAt q pre hk i) := by
  rw [childAt_eq_get q pre hk i hi]
  exact childPrefixes_valid q pre hp hk _ (List.getElem_mem _)

theorem program_meets {μ : ℕ → ℤ} {h J k masks dstL dstR work d : ℕ}
    (q : GlobalOutput h J) (pre : List (Finset (Fin (512*h))))
    (hp : ValidPrefix q k pre) (hk : k < J)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hmasks : masks+groupSize h ≤ dstL)
    (hleft : dstL+groupSize h ≤ dstR)
    (hright : dstR+groupSize h ≤ work)
    (hspace : work+(2*(J*(512*h))+2) ≤ lim.space)
    (hword : ((2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+J*(512*h)+3 ≤ lim.depth) :
    Meets lim LightBlockChildren.program 0 d
      [J*(512*h),h,rowMask (outputRows q) ⟨k,hk⟩,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        subsetMask (querySet k (outputRows q)),masks,dstL,dstR,work]
      μ (LightBlockChildren.time (J*(512*h)) (2*h) h)
      (fun r μ' =>
        r = (subsetMask (querySet (k+1) (outputRows q)) : ℤ) ∧
        SegN μ' masks ((globalChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h).map subsetMask) ∧
        SegN μ' dstL ((childPrefixes q pre hk).map fun next =>
          subsetMask (leftPrefix (k+1) (prefixRows (J := J) next))) ∧
        SegN μ' dstR ((childPrefixes q pre hk).map fun next =>
          subsetMask (rightPrefix (k+1) (outputRows q) (prefixRows (J := J) next))) ∧
        Kept μ μ' masks) := by
  have hc : (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)).card = 2*h := by
    rw [blockSet_card]
    exact LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  have hcount : (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)).card.choose h = groupSize h := by
    rw [hc]
    rfl
  have hcall := LightBlockChildren.program_meets (μ := μ) (d := d)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) (querySet k (outputRows q))
    hw (prefix_disjoint_block _ hk _) (prefix_disjoint_block _ hk _)
    (blockSet_subset_query _ hk) (by rw [hc]; omega)
    (hcount ▸ hmasks) (hcount ▸ hleft) (hcount ▸ hright) hspace hword hd
  have hrow : subsetMask (blockSet ⟨k,hk⟩ (outputRows q ⟨k,hk⟩)) = rowMask (outputRows q) ⟨k,hk⟩ := by
    simp [rowMask]
  rw [hrow,hc,leftMasks_eq q pre hp.1 hk,rightMasks_eq q pre hp.1 hk,
    ← querySet_step (outputRows q) hk] at hcall
  exact hcall

theorem time_bound {h J k : ℕ} (hk : k < J) :
    LightBlockChildren.time (J*(512*h)) (2*h) h ≤
      1600*(J*(512*h)+1)^2*(groupSize h+1) := by
  apply LightBlockChildren.time_bound
  have hJ : 0 < J := by omega
  have hw : 512*h ≤ J*(512*h) := Nat.le_mul_of_pos_left _ hJ
  omega

end ThreeSum.LightBlockChildrenIndexed
