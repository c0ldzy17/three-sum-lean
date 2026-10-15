import Submission.ThreeSum.TernaryOversizePrime
import Submission.ThreeSum.TernaryCanonicalDictionaries
import Submission.ThreeSum.TernaryOriginalKeyCodes

noncomputable section
namespace ThreeSum.TernaryNativeCoverWitness
open Finset TernaryJointType TernaryCoverLocal TernaryLocalParameters
open TernaryCoverGoodMaps TernaryCoverFrequency TernaryFixedDictionaries
open TernaryCanonicalDictionaries
variable {m p : ℕ} [Fact p.Prime]
variable {I : Type*} [Fintype I] [DecidableEq I]
set_option maxHeartbeats 3000000

theorem retained_edge {B τ : ℕ}
    (w : Weight m p) (a b : ZMod p) (hc : Covers m p B τ w (a,b)) :
    w∉rawBadMaps m p τ ∧ ∃ e : ActualEdge m,
      leftHash w e=a ∧ rightHash w e=b ∧
      TernaryCoverTrimming.bucketSize (fieldVertices (fixedLength m) p (fixedAlpha m))
        TernaryCoverHashes.leftVector w a≤B ∧
      TernaryCoverTrimming.bucketSize (fieldVertices (fixedLength m) p (fixedAlpha m))
        TernaryCoverHashes.rightVector w b≤B := by
  classical
  have hg : w∉rawBadMaps m p τ := by
    intro hw
    simpa [Covers,prunedHit,hw] using hc
  have hh : hitCount (fixedAlpha m) (fixedPi m) B w a b≠0 := by
    simpa only [Covers,prunedHit,if_neg hg] using hc
  obtain ⟨e,he⟩ := card_pos.mp (Nat.pos_of_ne_zero hh)
  have ht := (mem_filter.mp he).2
  change w∈TernaryCoverTrimming.trimmedPairEvent _ _ a b _ _ B at ht
  obtain ⟨hpair,hcaps⟩ := mem_filter.mp ht
  have hhash := (mem_filter.mp hpair).2
  exact ⟨hg,e,hhash.1,hhash.2,hcaps⟩

def leftRecord (i : I) (e : ActualEdge m) : SourceRecord (fixedLength m) (fixedAlpha m) I :=
  (i,⟨left e,left_mem_vertices e⟩)
def rightRecord (i : I) (e : ActualEdge m) : SourceRecord (fixedLength m) (fixedAlpha m) I :=
  (i,⟨right e,right_mem_vertices e⟩)

theorem local_record_witness (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, Covers m p B τ (maps i) (a,b)) (a b : ZMod p) :
    ∃ i : I, ∃ e : ActualEdge m,
      maps i∉rawBadMaps m p τ ∧
      leftRecord i e∈records false maps B ∧ rightRecord i e∈records true maps B ∧
      leftNative maps (leftRecord i e)=a ∧ rightNative maps (rightRecord i e)=b ∧
      outputHash (maps i) (output e)=a+b := by
  classical
  obtain ⟨i,hi⟩ := hcover a b
  obtain ⟨hg,e,hl,hr,hbl,hbr⟩ := retained_edge (maps i) a b hi
  have hln : leftNative maps (leftRecord i e)=a := hl
  have hrn : rightNative maps (rightRecord i e)=b := hr
  refine ⟨i,e,hg,?_,?_,hln,hrn,?_⟩
  · have ha : acceptedLeft maps B (leftRecord i e) := by
      unfold acceptedLeft
      change TernaryCoverTrimming.bucketSize _ _ (maps i) (leftNative maps (leftRecord i e))≤B
      rw [hln]
      exact hbl
    simpa [records,trimmedLeftRecords] using ha
  · have ha : acceptedRight maps B (rightRecord i e) := by
      unfold acceptedRight
      change TernaryCoverTrimming.bucketSize _ _ (maps i) (rightNative maps (rightRecord i e))≤B
      rw [hrn]
      exact hbr
    simpa [records,trimmedRightRecords] using ha
  · rw [← hashes_add,hl,hr]

/-- A full native-coordinate vector has one retained local choice in every
coordinate. The list retains map occurrences, source words, and output type. -/
theorem vector_record_witness (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, Covers m p B τ (maps i) (a,b))
    {r : ℕ} (a b : Fin r → ZMod p) :
    ∃ occurrence : Fin r → I, ∃ edge : Fin r → ActualEdge m,
      ∀ j, maps (occurrence j)∉rawBadMaps m p τ ∧
        leftRecord (occurrence j) (edge j)∈records false maps B ∧
        rightRecord (occurrence j) (edge j)∈records true maps B ∧
        leftNative maps (leftRecord (occurrence j) (edge j))=a j ∧
        rightNative maps (rightRecord (occurrence j) (edge j))=b j ∧
        outputHash (maps (occurrence j)) (output (edge j))=a j+b j := by
  classical
  have hh (j : Fin r) := local_record_witness maps B τ hcover (a j) (b j)
  choose occurrence edge he using hh
  exact ⟨occurrence,edge,he⟩


theorem source_records_nonempty (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, Covers m p B τ (maps i) (a,b)) :
    0<(records (α := fixedAlpha m) false maps B).length ∧
      0<(records (α := fixedAlpha m) true maps B).length := by
  obtain ⟨i,e,hg,hl,hr,hlh,hrh,hout⟩ := local_record_witness maps B τ hcover 0 0
  constructor
  · by_contra hn
    have hz : records (α := fixedAlpha m) false maps B=[] := List.length_eq_zero_iff.mp (by omega)
    simpa [hz] using hl
  · by_contra hn
    have hz : records (α := fixedAlpha m) true maps B=[] := List.length_eq_zero_iff.mp (by omega)
    simpa [hz] using hr

open TernaryOversizePrime

def nativeMaps (K m k : ℕ) (i : Fin (nativeFamily K m k).length) :
    Weight m (nativePrime K m) := (nativeFamily K m k)[i.val]

theorem nativeMaps_cover {K m k : ℕ} (hK : 0<K) (hm : 0<m) (hk : 0<k)
    (a b : ZMod (nativePrime K m)) :
    ∃ i : Fin (nativeFamily K m k).length,
      Covers m (nativePrime K m) (TernaryCoverCapParameters.sourceCap m (nativePrime K m))
        (TernaryCoverCapParameters.rawThreshold (nativePrime K m)
          (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k)
        (nativeMaps K m k i) (a,b) := by
  obtain ⟨w,hw,hc⟩ := native_family_covers hK hm hk (a,b)
  obtain ⟨i,hi⟩ := List.mem_iff_get.mp hw
  refine ⟨i,?_⟩
  have he : nativeMaps K m k i=w := by simpa only [nativeMaps,List.get_eq_getElem] using hi
  rw [he]
  exact hc

end ThreeSum.TernaryNativeCoverWitness
