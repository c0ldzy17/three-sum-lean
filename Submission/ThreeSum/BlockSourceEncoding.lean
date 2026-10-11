import Submission.ThreeSum.BlockIndexedQuery
import Submission.ThreeSum.LightSourceHistogram

/-!
# Original-input histograms give the exact independently trimmed sources

The histogram keys retain the first modular reduction and the signed carry
offset. Looking up the endpoint's final residue therefore counts precisely
the original divisibility condition in `BlockEncoding`. An explicit finite
enumeration accounts for every original input incidence once.
-/

namespace ThreeSum.BlockSourceEncoding

open Finset BlockEncoding GlobalEncoding LocalCoverBounds LightSourceResidues
open scoped BigOperators

set_option maxHeartbeats 1000000

theorem key_eq_iff {p m : ℕ} (hm : 0 < m) (shift x endpoint : ℤ) :
    key p m shift x = LightResidues.residue m 1 endpoint ↔
      (m : ℤ) ∣ x % (p : ℤ) + shift - endpoint := by
  rw [← Int.natCast_inj, key_cast hm, LightResidues.residue_cast hm, one_mul,
    Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.dvd_iff_emod_eq_zero]

theorem count_eq_sum {p m : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (values : ℕ → ℤ) (n : ℕ) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ range n, if (m : ℤ) ∣ values i % (p : ℤ) + shift - endpoint
          then 1 else 0 := by
  unfold LightHistogram.count
  rw [Finset.card_eq_sum_ones,Finset.sum_filter]
  simp only [key_eq_iff hm]

theorem count_eq_sum_of_equiv {β : Type*} [DecidableEq β]
    {p m n : ℕ} (hm : 0 < m) (shift endpoint : ℤ)
    (B : Finset β) (b : β → ℤ) (values : ℕ → ℤ)
    (e : Fin n ≃ B) (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    LightHistogram.count (fun i => key p m shift (values i))
      (LightResidues.residue m 1 endpoint) n =
        ∑ i ∈ B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
  rw [count_eq_sum hm,← Fin.sum_univ_eq_sum_range]
  calc
    _ = ∑ i : B, if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then 1 else 0 := by
      apply Fintype.sum_equiv e
      intro i
      rw [hvalues i]
    _ = _ := Finset.sum_coe_sort B
      (fun i : β => if (m : ℤ) ∣ b i % (p : ℤ) + shift - endpoint then (1 : ℕ) else 0)

def modulus (h J : ℕ) : ℕ := localPrime h ^ J

theorem modulus_pos (h J : ℕ) : 0 < modulus h J := pow_pos (localPrime_pos h) J

@[simp] theorem modulus_cast (h J : ℕ) : (modulus h J : ℤ) = globalModulus h J := by
  simp only [modulus,globalModulus,Nat.cast_pow]

section OriginalSources

variable {β : Type*} [DecidableEq β]

theorem leftWeights_eq_histogram {h J n : ℕ} (o : Occurrences h J) (p : ℕ)
    (B : Finset β) (b : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ B)
    (hvalues : ∀ i : Fin n, values i.val = b (e i)) :
    leftWeights o (p : ℤ) B b S =
      if LeftAllowed o S then
        LightHistogram.count (fun i => key p (modulus h J) 0 (values i))
          (LightResidues.residue (modulus h J) 1 (endpointLeft o S)) n
      else 0 := by
  unfold leftWeights
  rw [count_eq_sum_of_equiv (modulus_pos h J) 0 (endpointLeft o S) B b values e hvalues]
  simp only [modulus_cast,add_zero]

theorem rightWeights_eq_histogram {h J n : ℕ} (o : Occurrences h J) (p : ℕ) (shift : ℤ)
    (C : Finset β) (c : β → ℤ) (S : Finset (BlockRows.Coord J (512*h)))
    (values : ℕ → ℤ) (e : Fin n ≃ C)
    (hvalues : ∀ i : Fin n, values i.val = c (e i)) :
    rightWeights o (p : ℤ) shift C c S =
      if RightAllowed o S then
        LightHistogram.count (fun i => key p (modulus h J) shift (values i))
          (LightResidues.residue (modulus h J) 1 (endpointRight o S)) n
      else 0 := by
  unfold rightWeights
  rw [count_eq_sum_of_equiv (modulus_pos h J) shift (endpointRight o S) C c values e hvalues]
  simp only [modulus_cast]

end OriginalSources

end ThreeSum.BlockSourceEncoding
