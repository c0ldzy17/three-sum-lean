import Submission.ThreeSum.SourceBucketView
import Submission.ThreeSum.BlockSourceEncoding
import Submission.ThreeSum.RawPrefixCounts
import Mathlib.Data.List.ProdSigma
import Mathlib.Data.List.Nodup

/-!
# Exact original-input bucket lists and raw Cartesian masses

Independent endpoint trimming selects an entire residue fiber or the empty
list. The physical array-index equivalence preserves original incidences,
including separate original indices whose values happen to agree.
-/

namespace ThreeSum.BlockSourceBuckets

open SourceBuckets LightHistogram BlockSourceEncoding LightSourceResidues
open BlockEncoding GlobalEncoding RawIncidences

set_option maxHeartbeats 1600000
set_option maxRecDepth 10000

def leftList {h J : ℕ} (μ : ℕ → ℤ) (flat : ℕ) (o : Occurrences h J) (p : ℕ)
    (v : ℕ → ℤ) (N : ℕ) (S : Finset (BlockRows.Coord J (512*h))) : List ℕ :=
  if LeftAllowed o S then
    bucketList μ flat
      (offset (fun i => key p (modulus h J) 0 (v i)) N
        (LightResidues.residue (modulus h J) 1 (endpointLeft o S)))
      (count (fun i => key p (modulus h J) 0 (v i))
        (LightResidues.residue (modulus h J) 1 (endpointLeft o S)) N)
  else []

def rightList {h J : ℕ} (μ : ℕ → ℤ) (flat : ℕ) (o : Occurrences h J) (p : ℕ) (shift : ℤ)
    (v : ℕ → ℤ) (N : ℕ) (S : Finset (BlockRows.Coord J (512*h))) : List ℕ :=
  if RightAllowed o S then
    bucketList μ flat
      (offset (fun i => key p (modulus h J) shift (v i)) N
        (LightResidues.residue (modulus h J) 1 (endpointRight o S)))
      (count (fun i => key p (modulus h J) shift (v i))
        (LightResidues.residue (modulus h J) 1 (endpointRight o S)) N)
  else []

theorem mem_leftList {h J p N offsets flat i : ℕ} {μ : ℕ → ℤ} {v : ℕ → ℤ}
    (H : Stored μ (fun i => key p (modulus h J) 0 (v i)) N (modulus h J) offsets flat)
    (o : Occurrences h J) (S : Finset (BlockRows.Coord J (512*h))) :
    i ∈ leftList μ flat o p v N S ↔ i < N ∧ LeftAllowed o S ∧
      globalModulus h J ∣ v i % (p : ℤ)-endpointLeft o S := by
  unfold leftList
  by_cases ha : LeftAllowed o S
  · simp only [ha,ite_true,true_and]
    rw [H.mem_bucketList (fun i _ => key_lt (modulus_pos h J) 0 (v i))
      (LightResidues.residue_lt (modulus_pos h J) 1 _),key_eq_iff (modulus_pos h J)]
    simp only [modulus_cast,add_zero]
  · simp only [ha,ite_false,List.not_mem_nil,false_and,and_false]

theorem mem_rightList {h J p N offsets flat i : ℕ} {shift : ℤ} {μ : ℕ → ℤ} {v : ℕ → ℤ}
    (H : Stored μ (fun i => key p (modulus h J) shift (v i)) N (modulus h J) offsets flat)
    (o : Occurrences h J) (S : Finset (BlockRows.Coord J (512*h))) :
    i ∈ rightList μ flat o p shift v N S ↔ i < N ∧ RightAllowed o S ∧
      globalModulus h J ∣ v i % (p : ℤ)+shift-endpointRight o S := by
  unfold rightList
  by_cases ha : RightAllowed o S
  · simp only [ha,ite_true,true_and]
    rw [H.mem_bucketList (fun i _ => key_lt (modulus_pos h J) shift (v i))
      (LightResidues.residue_lt (modulus_pos h J) 1 _),key_eq_iff (modulus_pos h J)]
    simp only [modulus_cast]
  · simp only [ha,ite_false,List.not_mem_nil,false_and,and_false]

theorem nodup_leftList {h J p N offsets flat : ℕ} {μ : ℕ → ℤ} {v : ℕ → ℤ}
    (H : Stored μ (fun i => key p (modulus h J) 0 (v i)) N (modulus h J) offsets flat)
    (o : Occurrences h J) (S : Finset (BlockRows.Coord J (512*h))) :
    (leftList μ flat o p v N S).Nodup := by
  unfold leftList
  split
  · exact H.nodup_bucketList (fun i _ => key_lt (modulus_pos h J) 0 (v i))
      (LightResidues.residue_lt (modulus_pos h J) 1 _)
  · exact List.nodup_nil

theorem nodup_rightList {h J p N offsets flat : ℕ} {shift : ℤ} {μ : ℕ → ℤ} {v : ℕ → ℤ}
    (H : Stored μ (fun i => key p (modulus h J) shift (v i)) N (modulus h J) offsets flat)
    (o : Occurrences h J) (S : Finset (BlockRows.Coord J (512*h))) :
    (rightList μ flat o p shift v N S).Nodup := by
  unfold rightList
  split
  · exact H.nodup_bucketList (fun i _ => key_lt (modulus_pos h J) shift (v i))
      (LightResidues.residue_lt (modulus_pos h J) 1 _)
  · exact List.nodup_nil

theorem leftList_length {β : Type*} [DecidableEq β] {h J N : ℕ}
    (μ : ℕ → ℤ) (flat : ℕ) (o : Occurrences h J) (p : ℕ)
    (B : Finset β) (b : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (v : ℕ → ℤ) (e : Fin N ≃ B) (hv : ∀ i : Fin N, v i.val = b (e i)) :
    (leftList μ flat o p v N S).length = leftWeights o (p : ℤ) B b S := by
  rw [leftWeights_eq_histogram o p B b S v e hv]
  unfold leftList
  split <;> simp only [bucketList_length,List.length_nil]

theorem rightList_length {β : Type*} [DecidableEq β] {h J N : ℕ}
    (μ : ℕ → ℤ) (flat : ℕ) (o : Occurrences h J) (p : ℕ) (shift : ℤ)
    (B : Finset β) (b : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (v : ℕ → ℤ) (e : Fin N ≃ B) (hv : ∀ i : Fin N, v i.val = b (e i)) :
    (rightList μ flat o p shift v N S).length = rightWeights o (p : ℤ) shift B b S := by
  rw [rightWeights_eq_histogram o p shift B b S v e hv]
  unfold rightList
  split <;> simp only [bucketList_length,List.length_nil]

def pairs {h J : ℕ} (μ : ℕ → ℤ) (flatL flatR p : ℕ) (shift : ℤ)
    (vL vR : ℕ → ℤ) (NL NR : ℕ) (t : ChoiceTuple h J) : List (ℕ × ℕ) :=
  (leftList μ flatL (outputOccurrences (tupleOutput t)) p vL NL (leftSubset t)) ×ˢ
    (rightList μ flatR (outputOccurrences (tupleOutput t)) p shift vR NR (rightSubset t))

theorem pairs_length {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J NL NR : ℕ} (μ : ℕ → ℤ) (flatL flatR p : ℕ) (shift : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hL : ∀ i : Fin NL, vL i.val = b (eL i)) (hR : ∀ i : Fin NR, vR i.val = c (eR i))
    (t : ChoiceTuple h J) :
    (pairs μ flatL flatR p shift vL vR NL NR t).length =
      leftBucket (p : ℤ) B b t*rightBucket (p : ℤ) shift C c t := by
  rw [pairs,List.length_product,leftList_length μ flatL _ p B b _ vL eL hL,
    rightList_length μ flatR _ p shift C c _ vR eR hR,
    leftWeights_choice (p : ℤ) B b t (tupleOutput t) rfl,
    rightWeights_choice (p : ℤ) shift C c t (tupleOutput t) rfl]

theorem pairs_length_eq_compatible_card {β γ : Type*} [Fintype β] [Fintype γ]
    [DecidableEq β] [DecidableEq γ] {h J NL NR : ℕ}
    (μ : ℕ → ℤ) (flatL flatR p : ℕ) (shift : ℤ)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (vL vR : ℕ → ℤ) (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hL : ∀ i : Fin NL, vL i.val = b (eL i)) (hR : ∀ i : Fin NR, vR i.val = c (eR i))
    (t : ChoiceTuple h J) :
    (pairs μ flatL flatR p shift vL vR NL NR t).length =
      (RawPrefixCounts.compatiblePairs (p : ℤ) shift B C b c t).card := by
  rw [pairs_length μ flatL flatR p shift B C b c vL vR eL eR hL hR,
    bucket_product_eq_card]
  rfl

theorem nodup_pairs {h J NL NR p offsetsL offsetsR flatL flatR : ℕ} {shift : ℤ} {μ : ℕ → ℤ}
    {vL vR : ℕ → ℤ}
    (HL : Stored μ (fun i => key p (modulus h J) 0 (vL i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun i => key p (modulus h J) shift (vR i)) NR (modulus h J) offsetsR flatR)
    (t : ChoiceTuple h J) : (pairs μ flatL flatR p shift vL vR NL NR t).Nodup :=
  (nodup_leftList HL _ _).product (nodup_rightList HR _ _)

theorem mem_pairs_iff {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J NL NR p offsetsL offsetsR flatL flatR : ℕ} {shift : ℤ} {μ : ℕ → ℤ}
    {vL vR : ℕ → ℤ}
    (HL : Stored μ (fun i => key p (modulus h J) 0 (vL i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun i => key p (modulus h J) shift (vR i)) NR (modulus h J) offsetsR flatR)
    (B : Finset β) (C : Finset γ) (b : β → ℤ) (c : γ → ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hL : ∀ i : Fin NL, vL i.val = b (eL i)) (hR : ∀ i : Fin NR, vR i.val = c (eR i))
    (t : ChoiceTuple h J) (i : Fin NL) (j : Fin NR) :
    (i.val,j.val) ∈ pairs μ flatL flatR p shift vL vR NL NR t ↔
      ((eL i).val,(eR j).val) ∈ RawPrefixCounts.compatiblePairs (p : ℤ) shift B C b c t := by
  rw [pairs,List.mem_product,mem_leftList HL,mem_rightList HR]
  simp only [i.isLt,j.isLt,leftAllowed_choice t (tupleOutput t) rfl,
    rightAllowed_choice t (tupleOutput t) rfl,endpointLeft_choice t (tupleOutput t) rfl,
    endpointRight_choice t (tupleOutput t) rfl,true_and,hL i,hR j,
    RawPrefixCounts.compatiblePairs,Finset.mem_filter,Finset.mem_product,
    (eL i).property,(eR j).property,true_and]

end ThreeSum.BlockSourceBuckets
