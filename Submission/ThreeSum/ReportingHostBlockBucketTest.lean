import Submission.ThreeSum.LightReportingBucketTest

/-!
# Original endpoint semantics and exact Cartesian-test cost

The selected physical lengths are the original independently trimmed source
weights, after transport by the original-index enumeration. Thus the actual
tuple tester's pair charge is exactly the raw leaf weight.
-/

namespace ThreeSum.ReportingHostBlockBucketTest

open Light Finset BlockRows BlockEncoding BlockSourceEncoding LightSourceResidues
open SourceBuckets LightSourceBucketSelect ReportingHostBucketTest
open GlobalEncoding RawIncidences

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

def leftResidue {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  LightResidues.residue (modulus h J) 1 (endpointLeft o S)

def rightResidue {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  LightResidues.residue (modulus h J) 1 (endpointRight o S)

def leftFlag {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  if LeftAllowed o S then 1 else 0

def rightFlag {h J : ℕ} (o : Occurrences h J) (S : Finset (Coord J (512*h))) : ℕ :=
  if RightAllowed o S then 1 else 0

theorem selected_left_eq_weights {β : Type*} [DecidableEq β] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (B : Finset β) (b : β→ℤ)
    (S : Finset (Coord J (512*h))) (v : ℕ→ℤ) (e : Fin N ≃ B)
    (hv : ∀ i : Fin N, v i.val=b (e i)) :
    countSelected (fun i => key p (modulus h J) 0 (v i)) N (leftResidue o S) (leftFlag o S)=
      leftWeights o (p : ℤ) B b S := by
  rw [leftWeights_eq_histogram o p B b S v e hv]
  unfold countSelected leftFlag leftResidue
  by_cases hs : LeftAllowed o S <;> simp [hs]

theorem selected_right_eq_weights {γ : Type*} [DecidableEq γ] {h J N : ℕ}
    (o : Occurrences h J) (p : ℕ) (shift : ℤ) (C : Finset γ) (c : γ→ℤ)
    (S : Finset (Coord J (512*h))) (v : ℕ→ℤ) (e : Fin N ≃ C)
    (hv : ∀ i : Fin N, v i.val=c (e i)) :
    countSelected (fun i => key p (modulus h J) shift (v i)) N (rightResidue o S) (rightFlag o S)=
      rightWeights o (p : ℤ) shift C c S := by
  rw [rightWeights_eq_histogram o p shift C c S v e hv]
  unfold countSelected rightFlag rightResidue
  by_cases hs : RightAllowed o S <;> simp [hs]

theorem actual_time_eq {β γ : Type*} [DecidableEq β] [DecidableEq γ] {h J NL NR : ℕ}
    (o : Occurrences h J) (p : ℕ) (shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β→ℤ) (c : γ→ℤ) (S T : Finset (Coord J (512*h))) (left right : ℕ→ℤ)
    (eL : Fin NL ≃ B) (eR : Fin NR ≃ C)
    (hvL : ∀ i : Fin NL, left i.val=b (eL i)) (hvR : ∀ j : Fin NR, right j.val=c (eR j)) :
    LightReportingBucketTest.time (fun i => key p (modulus h J) 0 (left i))
      (fun j => key p (modulus h J) shift (right j)) NL NR
      (leftResidue o S) (rightResidue o T) (leftFlag o S) (rightFlag o T) =
        240*(leftWeights o (p : ℤ) B b S*rightWeights o (p : ℤ) shift C c T)+700 := by
  rw [LightReportingBucketTest.time_eq,selected_left_eq_weights o p B b S left eL hvL,
    selected_right_eq_weights o p shift C c T right eR hvR]

theorem test_pos_iff {μ : ℕ→ℤ} {h J NL NR p offsetsL offsetsR flatL flatR : ℕ}
    (shift a : ℤ) (left right : ℕ→ℤ) (o : Occurrences h J) (S T : Finset (Coord J (512*h)))
    (HL : Stored μ (fun i => key p (modulus h J) 0 (left i)) NL (modulus h J) offsetsL flatL)
    (HR : Stored μ (fun j => key p (modulus h J) shift (right j)) NR (modulus h J) offsetsR flatR) :
    0<testCount μ a left right (fun i => key p (modulus h J) 0 (left i))
      (fun j => key p (modulus h J) shift (right j)) NL NR flatL flatR
      (leftResidue o S) (rightResidue o T) (leftFlag o S) (rightFlag o T) ↔
      LeftAllowed o S ∧ RightAllowed o T ∧
        ∃ i<NL, ∃ j<NR,
          globalModulus h J ∣ left i%(p : ℤ)-endpointLeft o S ∧
          globalModulus h J ∣ right j%(p : ℤ)+shift-endpointRight o T ∧
          right j-left i-a=0 := by
  rw [testCount_pos_iff (rL := leftResidue o S) (rR := rightResidue o T)
    (flagL := leftFlag o S) (flagR := rightFlag o T) HL HR (fun i _ => key_lt (modulus_pos h J) 0 (left i))
    (fun j _ => key_lt (modulus_pos h J) shift (right j))
    (LightResidues.residue_lt (modulus_pos h J) 1 _) (LightResidues.residue_lt (modulus_pos h J) 1 _) a left right]
  simp only [leftFlag,rightFlag]
  simp only [leftResidue,rightResidue,key_eq_iff (modulus_pos h J),modulus_cast,add_zero]
  by_cases hS : LeftAllowed o S <;> by_cases hT : RightAllowed o T <;> simp [hS,hT]

end ThreeSum.ReportingHostBlockBucketTest
