import Submission.ThreeSum.TernaryCanonicalDictionaries
import Submission.ThreeSum.LightTernarySourceCountHost

noncomputable section
namespace ThreeSum.TernaryCanonicalSixTables
open TernaryCanonicalDictionaries TernaryJointType
variable {L p : ℕ} [Fact p.Prime] {α : DigitType}
variable {I : Type*} [Fintype I] [DecidableEq I]

def hashes (right : Bool) (maps : I→TernaryCoverHashes.Coordinate (Fin L)→ZMod p) (B : ℕ) : List ℤ :=
  (records (α := α) right maps B).map (native right maps)
def words (right : Bool) (maps : I→TernaryCoverHashes.Coordinate (Fin L)→ZMod p) (B : ℕ) : List ℤ :=
  (records (α := α) right maps B).map wordCode
def groups (right : Bool) (maps : I→TernaryCoverHashes.Coordinate (Fin L)→ZMod p) (B : ℕ) : List ℤ :=
  (records (α := α) right maps B).map mapCode

/-- The concrete source/count program contains the canonical native-field,
word and map-occurrence tables for both sides of the very same local maps. -/
def program (maps : I→TernaryCoverHashes.Coordinate (Fin L)→ZMod p) (B : ℕ) : Light.Program :=
  LightTernarySourceCountHost.program
    (hashes (α := α) false maps B) (words (α := α) false maps B) (groups (α := α) false maps B)
    (hashes (α := α) true maps B) (words (α := α) true maps B) (groups (α := α) true maps B)

theorem lengths (right : Bool) (maps : I→TernaryCoverHashes.Coordinate (Fin L)→ZMod p) (B : ℕ) :
    (words (α := α) right maps B).length=(hashes (α := α) right maps B).length ∧
    (groups (α := α) right maps B).length=(hashes (α := α) right maps B).length := by
  simp [hashes,words,groups]

theorem bounds (right : Bool) (maps : I→TernaryCoverHashes.Coordinate (Fin L)→ZMod p) (B : ℕ) :
    (∀ x∈hashes (α := α) right maps B, |x|≤(p : ℤ)) ∧
    (∀ x∈words (α := α) right maps B, |x|≤((4^L : ℕ) : ℤ)) ∧
    (∀ x∈groups (α := α) right maps B, |x|≤(Fintype.card I : ℤ)) := by
  constructor
  · intro x hx
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
    exact native_bound right maps r
  constructor
  · intro x hx
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
    exact wordCode_bound r
  · intro x hx
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp hx
    exact mapCode_bound r

end ThreeSum.TernaryCanonicalSixTables
