import Submission.ThreeSum.TernaryOriginalRowMenu

/-! Literal collisions of ORIGINAL source records. Both orientations of a
colliding pair are counted. Removing all nonsingleton buckets therefore
deletes no more records than this score; no maximum-bucket moment is assumed. -/

noncomputable section
namespace ThreeSum.TernaryOriginalCollisions

open Finset TernaryOriginalRowMenu
open scoped BigOperators
attribute [local instance] Classical.propDecidable

variable {K E B W : Type*} [Field K] [Fintype K] [DecidableEq K]
  [Field E] [Algebra K E] [Fintype E] [DecidableEq E]
  [Fintype B] [DecidableEq B] [DecidableEq W]

def collisionPairs (hash : B → W) : Finset (B × B) :=
  univ.filter fun ab => ab.1 ≠ ab.2 ∧ hash ab.1 = hash ab.2

def deleted (hash : B → W) : Finset B :=
  univ.filter fun a => ∃ b, a ≠ b ∧ hash a = hash b

theorem deleted_card_le_collisions (hash : B → W) :
    (deleted hash).card ≤ (collisionPairs hash).card := by
  let partner : (deleted hash) → B := fun a => Classical.choose (mem_filter.mp a.property).2
  let f : (deleted hash) → (collisionPairs hash) := fun a =>
    ⟨(a.val,partner a),mem_filter.mpr ⟨mem_univ _,Classical.choose_spec (mem_filter.mp a.property).2⟩⟩
  have hf : Function.Injective f := by
    intro a b h
    apply Subtype.ext
    exact congrArg (fun c : collisionPairs hash => c.val.1) h
  simpa using Fintype.card_le_of_injective f hf

theorem surviving_hash_injective (hash : B → W) :
    Function.Injective (fun a : {a : B // a ∉ deleted hash} => hash a.val) := by
  intro a b h
  apply Subtype.ext
  by_contra hab
  apply a.property
  exact mem_filter.mpr ⟨mem_univ _,b.val,hab,h⟩

def nextCollisions {Λ : ℕ} (ℓ : E →ₗ[K] K) (v : B → Fin Λ → K)
    (hash : B → W) (seed : E × E) : ℕ :=
  ((collisionPairs hash).filter fun ab => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)).card

theorem sum_nextCollisions_bound {Λ : ℕ} (ℓ : E →ₗ[K] K) (hℓ : ℓ ≠ 0)
    (v : B → Fin Λ → K) (hv : Function.Injective v) (hash : B → W)
    (V : Submodule K (Fin Λ → K)) (hV : V ≠ ⊤) (hp : 3 ≤ Fintype.card K)
    (hsize : 8*Λ*Fintype.card K^2 ≤ Fintype.card E) :
    Fintype.card K * (∑ seed ∈ admissible Λ ℓ V, nextCollisions ℓ v hash seed) ≤
      3*(admissible Λ ℓ V).card*(collisionPairs hash).card := by
  let S := admissible Λ ℓ V
  let C := collisionPairs hash
  have hterm (ab : B × B) (hab : ab ∈ C) :
      Fintype.card K * (S.filter fun seed => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)).card ≤
        3*S.card := by
    have hvne : v ab.1-v ab.2 ≠ 0 := by
      intro hz
      exact (mem_filter.mp hab).2.1 (hv (sub_eq_zero.mp hz))
    have hind : LinearIndependent K (fun _ : Fin 1 => v ab.1-v ab.2) := by
      simpa only [linearIndependent_unique_iff] using hvne
    have hh := admissible_event_bound ℓ hℓ V hV hp
      (fun _ : Fin 1 => v ab.1-v ab.2) hind 0 hsize (by simpa using hsize)
    have he : (S ∩ menuEvent ℓ (fun _ : Fin 1 => v ab.1-v ab.2) 0) =
        S.filter (fun seed => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)) := by
      ext seed
      simp [menuEvent,map_sub,sub_eq_zero,Fin.forall_fin_one]
    simp only [pow_one] at hh
    change Fintype.card K * (S ∩ menuEvent ℓ (fun _ : Fin 1 => v ab.1-v ab.2) 0).card ≤ 3*S.card at hh
    rw [he] at hh
    exact hh
  have hex : (∑ seed ∈ S, nextCollisions ℓ v hash seed) =
      ∑ ab ∈ C, (S.filter fun seed => row Λ ℓ seed (v ab.1) = row Λ ℓ seed (v ab.2)).card := by
    simp only [nextCollisions,card_eq_sum_ones,sum_filter]
    rw [sum_comm]
  rw [hex,mul_sum]
  calc
    _ ≤ ∑ _ab ∈ C, 3*S.card := sum_le_sum hterm
    _ = _ := by simp [S,C,Nat.mul_comm]

end ThreeSum.TernaryOriginalCollisions
