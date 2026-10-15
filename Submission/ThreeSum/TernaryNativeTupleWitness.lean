import Submission.ThreeSum.TernaryRepeatedWords
import Submission.ThreeSum.TernaryGoodOutputCatalog

noncomputable section
namespace ThreeSum.TernaryNativeTupleWitness
open Finset TernaryJointType TernaryLocalParameters TernaryCoverLocal TernaryCoverGoodMaps
open TernaryNativeCoverWitness TernaryExtensionEncoding TernaryFixedDictionaries
open scoped BigOperators
variable {p m : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

theorem positional_map {A B : Type*} (p : ℤ) (f : A → B) (g : B → ℤ) (xs : List A) :
    Radix.positionalHash p (g ∘ f) xs=Radix.positionalHash p g (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [Radix.positionalHash,ih]

theorem positional_cast_digits (p : ℕ) (xs : List ℕ) :
    Radix.positionalHash (p : ℤ) (fun a : ℕ => (a : ℤ)) xs=((Nat.ofDigits p xs : ℕ) : ℤ) := by
  induction xs with
  | nil => simp [Radix.positionalHash,Nat.ofDigits]
  | cons x xs ih => simp [Radix.positionalHash,Nat.ofDigits,ih,add_comm,mul_comm]

theorem positional_ofFn {A : Type*} {r : ℕ} (xs : Fin r → A) (raw : A → ℤ)
    (v : Fin r → ZMod p) (hraw : ∀ i, raw (xs i)=(v i).val) :
    Radix.positionalHash (p : ℤ) raw (List.ofFn xs)=(coefficientCode v : ℤ) := by
  have h1 : (List.ofFn xs).map raw=List.ofFn (fun i => ((v i).val : ℤ)) := by
    rw [List.map_ofFn]
    apply List.ofFn_inj.mpr
    funext i
    exact hraw i
  have h2 : (List.ofFn fun i => (v i).val).map (fun a : ℕ => (a : ℤ))=
      List.ofFn (fun i => ((v i).val : ℤ)) := List.map_ofFn
  calc
    _ = Radix.positionalHash (p : ℤ) id ((List.ofFn xs).map raw) := positional_map _ _ _ _
    _ = Radix.positionalHash (p : ℤ) id
        ((List.ofFn fun i => (v i).val).map (fun a : ℕ => (a : ℤ))) := by rw [h1,h2]
    _ = Radix.positionalHash (p : ℤ) (fun a : ℕ => (a : ℤ)) (List.ofFn fun i => (v i).val) :=
      (positional_map _ _ _ _).symm
    _ = _ := positional_cast_digits p _

theorem output_mem_vertices (e : ActualEdge m) : output e∈vertices (fixedLength m) (fixedPi m) := by
  classical
  exact mem_filter.mpr ⟨mem_univ _,(edge_data e).2.2.1⟩

variable {I : Type*} [Fintype I] [DecidableEq I]

theorem tuple_witness (maps : I → Weight m p) (B τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, TernaryCoverFrequency.Covers m p B τ (maps i) (a,b))
    {r : ℕ} (a b : Fin r → ZMod p) :
    ∃ occurrence : Fin r → I, ∃ edge : Fin r → ActualEdge m,
      (List.ofFn fun i => leftRecord (occurrence i) (edge i))∈
        RadixKeyLists.tuples (TernaryCanonicalDictionaries.records false maps B) r ∧
      (List.ofFn fun i => rightRecord (occurrence i) (edge i))∈
        RadixKeyLists.tuples (TernaryCanonicalDictionaries.records true maps B) r ∧
      (List.ofFn fun i => (occurrence i, (⟨output (edge i),output_mem_vertices (edge i)⟩ :
        TernaryGoodOutputCatalog.Output m)))∈
        RadixKeyLists.tuples (TernaryGoodOutputCatalog.records maps τ) r ∧
      Radix.positionalHash (p : ℤ) (TernaryCanonicalDictionaries.native false maps)
        (List.ofFn fun i => leftRecord (occurrence i) (edge i))=(coefficientCode a : ℤ) ∧
      Radix.positionalHash (p : ℤ) (TernaryCanonicalDictionaries.native true maps)
        (List.ofFn fun i => rightRecord (occurrence i) (edge i))=(coefficientCode b : ℤ) ∧
      Radix.positionalHash (p : ℤ) (TernaryGoodOutputCatalog.key maps)
        (List.ofFn fun i => (occurrence i, (⟨output (edge i),output_mem_vertices (edge i)⟩ :
          TernaryGoodOutputCatalog.Output m)))=(coefficientCode (a+b) : ℤ) := by
  classical
  obtain ⟨occ,edge,h⟩ := vector_record_witness maps B τ hcover a b
  refine ⟨occ,edge,?_,?_,?_,?_,?_,?_⟩
  · apply (RadixKeyLists.mem_tuples _ _ _).mpr
    refine ⟨by simp,?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (h i).2.1
  · apply (RadixKeyLists.mem_tuples _ _ _).mpr
    refine ⟨by simp,?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (h i).2.2.1
  · apply (RadixKeyLists.mem_tuples _ _ _).mpr
    refine ⟨by simp,?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact (TernaryGoodOutputCatalog.mem_records maps τ _).mpr (h i).1
  · apply positional_ofFn
    intro i
    simp only [TernaryCanonicalDictionaries.native,Bool.false_eq_true,↓reduceIte,(h i).2.2.2.1]
  · apply positional_ofFn
    intro i
    simp only [TernaryCanonicalDictionaries.native,↓reduceIte,(h i).2.2.2.2.1]
  · apply positional_ofFn
    intro i
    simp only [TernaryGoodOutputCatalog.key,TernaryGoodOutputCatalog.native,Prod.fst,Prod.snd]
    rw [(h i).2.2.2.2.2]
    rfl

end ThreeSum.TernaryNativeTupleWitness
