import Submission.ThreeSum.LightStoredSpan
import Submission.ThreeSum.TernaryOriginalRowMenu
import Submission.ThreeSum.TernarySignedLayout
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Digit-only physical admissibility. Tags are deliberately absent from the
stored span. Reversing the J digit coordinates preserves exactly the logical
span condition used by the original extension-field row menu. -/
noncomputable section
namespace ThreeSum.TernaryPhysicalDigitSpan
open Light
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

variable {K : Type*} [Field K] {J : ℕ}

def reversal (J : ℕ) : (Fin J → K) ≃ₗ[K] (Fin J → K) where
  toFun v i := v i.rev
  invFun v i := v i.rev
  left_inv v := by funext i; simp
  right_inv v := by funext i; simp
  map_add' v w := rfl
  map_smul' a v := rfl

def digitProjection (J : ℕ) : (Fin (J+2) → K) →ₗ[K] (Fin J → K) where
  toFun v i := v (Fin.castAdd 2 i)
  map_add' v w := rfl
  map_smul' a v := rfl

def physicalDigits (row : Fin (J+2) → K) : Fin J → K :=
  reversal J (digitProjection J row)

def oldSpan (rows : List (Fin J → K)) : Submodule K (Fin J → K) :=
  Submodule.span K {v | v∈rows}

def forbidden (rows : List (Fin J → K)) : Submodule K (Fin (J+2) → K) :=
  Submodule.comap (digitProjection J) (oldSpan rows)

theorem digitProjection_surjective : Function.Surjective (digitProjection (K := K) J) := by
  intro v
  refine ⟨fun i => if hi : i.val<J then v ⟨i.val,hi⟩ else 0,?_⟩
  funext i
  simp [digitProjection,i.isLt]

theorem reversal_span (rows : List (Fin J → K)) (row : Fin J → K) :
    reversal J row∈oldSpan (rows.map (reversal J)) ↔ row∈oldSpan rows := by
  have himage : {v | v∈rows.map (reversal J)}=(reversal J) '' {v | v∈rows} := by
    ext v
    simp only [Set.mem_setOf_eq,List.mem_map,Set.mem_image]
  unfold oldSpan
  rw [himage]
  exact Submodule.apply_mem_span_image_iff_mem_span (reversal J).injective

theorem physical_span_iff (rows : List (Fin J → K)) (row : Fin (J+2) → K) :
    physicalDigits row∈oldSpan (rows.map (reversal J)) ↔ row∈forbidden rows :=
  reversal_span rows (digitProjection J row)

theorem oldSpan_proper (rows : List (Fin J → K)) (hlen : rows.length<J) : oldSpan rows≠⊤ := by
  classical
  let v : Fin rows.length → Fin J → K := fun i => rows[i.val]
  have he : Set.range v={w | w∈rows} := by
    ext w
    simp only [Set.mem_range,Set.mem_setOf_eq]
    constructor
    · rintro ⟨i,rfl⟩; exact List.getElem_mem _
    · intro hw
      obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp hw
      exact ⟨⟨i,hi⟩,he⟩
  intro htop
  have hh := finrank_le_of_span_eq_top (R := K) (v := v) (by rw [he]; exact htop)
  simp only [Module.finrank_pi,Module.finrank_self,Fintype.card_fin,one_mul] at hh
  omega

theorem forbidden_proper (rows : List (Fin J → K)) (hlen : rows.length<J) : forbidden rows≠⊤ := by
  intro htop
  apply oldSpan_proper rows hlen
  apply top_unique
  intro v _
  obtain ⟨w,rfl⟩ := digitProjection_surjective (K := K) (J := J) v
  have hw : w∈forbidden rows := by rw [htop]; trivial
  exact hw

variable {E : Type*} [Field E] [Algebra K E] [Fintype K] [Fintype E] [DecidableEq K] [DecidableEq E]

theorem menu_admissible_iff (ℓ : E →ₗ[K] K) (rows : List (Fin J → K)) (seed : E×E) :
    seed∈TernaryOriginalRowMenu.admissible (J+2) ℓ (forbidden rows) ↔
      physicalDigits (TernaryOriginalRowMenu.seedRow (J+2) ℓ seed)∉oldSpan (rows.map (reversal J)) := by
  simp only [TernaryOriginalRowMenu.admissible,Finset.mem_filter,Finset.mem_univ,true_and]
  exact not_congr (physical_span_iff rows _).symm

variable {p : ℕ} [Fact p.Prime]

@[simp] theorem flag_menu_iff [Algebra (ZMod p) E] (ℓ : E →ₗ[ZMod p] ZMod p) (rows : List (Fin J → ZMod p)) (seed : E×E) :
    LightStoredSpan.admissibleFlag (rows.map (reversal J))
      (physicalDigits (TernaryOriginalRowMenu.seedRow (J+2) ℓ seed))=1 ↔
      seed∈TernaryOriginalRowMenu.admissible (J+2) ℓ (forbidden rows) := by
  rw [LightStoredSpan.admissibleFlag_eq_one]
  exact (menu_admissible_iff ℓ rows seed).symm

/-- The backend's first J physical cells are the logical digit projection
followed by reversal; the two unrestricted tag cells never enter this row. -/
theorem physicalDigits_val (row : Fin (J+2) → K) (i : Fin J) :
    physicalDigits row i=row ⟨J-1-i.val,by have := i.isLt; omega⟩ := by
  change row (Fin.castAdd 2 i.rev)=_
  congr 1
  apply Fin.ext
  simp only [Fin.coe_castAdd,Fin.val_rev]
  omega


/-- Executed membership testing of only the J physical digits returns the
logical digit-comap admissibility bit. -/
theorem admissible_meets {lim : Limits} {P : Program}
    {pMain pEq catalog n candidate depth : ℕ}
    (hmain : P[pMain]?=some (LightSpanCatalogTest.body pEq))
    (heq : P[pEq]?=some LightSpanRowEqual.body)
    (μ : ℕ → ℤ) (f : ℕ → ℕ → ℕ) (row : Fin (J+2) → ZMod p)
    (rows : List (Fin J → ZMod p))
    (H : TernaryStoredSpan.Represents f n (rows.map (reversal J)))
    (hw : (lim.space : ℤ)≤lim.word) (hcat : catalog+J*n≤lim.space)
    (hrow : candidate+J≤lim.space)
    (hcontrols : ((n+J+16 : ℕ) : ℤ)≤lim.word) (hpp : (p : ℤ)≤lim.word)
    (hf : ∀k<n, ∀i<J, f k i<p)
    (hread : ∀k<n, ∀i<J, μ (catalog+J*k+i)=(f k i : ℤ))
    (hreadRow : ∀i<J, μ (candidate+i)=(LightStoredSpan.rowValues (physicalDigits row) i : ℤ))
    (hd : depth+1≤lim.depth) :
    Meets lim P pMain depth [catalog,n,J,candidate] μ (LightSpanCatalogTest.time J n)
      (fun r ν => (r=1 ↔ row∉forbidden rows) ∧ ν=μ) := by
  have hh := LightStoredSpan.admissible_meets hmain heq μ f (physicalDigits row)
    (rows.map (reversal J)) H hw hcat hrow hcontrols hpp hf hread hreadRow hd
  apply hh.mono le_rfl
  intro r ν h
  refine ⟨?_,h.2⟩
  rw [h.1]
  have hflag : LightStoredSpan.admissibleFlag (rows.map (reversal J)) (physicalDigits row)=1 ↔ row∉forbidden rows := by
    rw [LightStoredSpan.admissibleFlag_eq_one]
    exact not_congr (physical_span_iff rows row)
  simpa only [Nat.cast_eq_one] using hflag

end ThreeSum.TernaryPhysicalDigitSpan
