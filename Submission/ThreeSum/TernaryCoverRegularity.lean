import Submission.ThreeSum.TernaryCoverLocal
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryCoverRegularity
open Finset TernaryJointType TernaryCoverLocal
variable {L : ℕ}

def reindex (σ : Equiv.Perm (Fin L)) (w : TritWord L) : TritWord L := w ∘ σ

theorem digitCount_reindex (σ : Equiv.Perm (Fin L)) (w : TritWord L) (d : Fin 3) :
    digitCount (reindex σ w) d = digitCount w d :=
  Equiv.sum_comp σ (fun i => if w i = d then 1 else 0)

theorem type_reindex (σ : Equiv.Perm (Fin L)) {w : TritWord L} {α : DigitType}
    (hw : HasType w α) : HasType (reindex σ w) α := by
  intro d
  rw [digitCount_reindex]
  exact hw d

/-- All words of the same type lie in one coordinate-permutation orbit. -/
theorem same_type_perm {a b : TritWord L} {α : DigitType}
    (ha : HasType a α) (hb : HasType b α) :
    ∃ σ : Equiv.Perm (Fin L), reindex σ a = b := by
  classical
  have hc (d : Fin 3) : Fintype.card {i // b i = d} = Fintype.card {i // a i = d} := by
    rw [Fintype.card_subtype, Fintype.card_subtype, card_filter, card_filter]
    change digitCount b d = digitCount a d
    rw [hb d, ha d]
  let e (d : Fin 3) : {i // b i = d} ≃ {i // a i = d} := Fintype.equivOfCardEq (hc d)
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext i
  exact Equiv.ofFiberEquiv_map e i

theorem edge_reindex (σ : Equiv.Perm (Fin L)) {a b q : TritWord L} {α π : DigitType}
    (he : Edge α π a b q) : Edge α π (reindex σ a) (reindex σ b) (reindex σ q) :=
  ⟨type_reindex σ he.1, type_reindex σ he.2.1, type_reindex σ he.2.2.1, fun i => he.2.2.2 (σ i)⟩

def mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType} (e : LocalEdge L α π) :
    LocalEdge L α π := by
  classical
  exact ⟨(reindex σ (left e), reindex σ (right e), reindex σ (output e)),
    mem_filter.mpr ⟨mem_univ _, edge_reindex σ (edge_data e)⟩⟩

@[simp] theorem left_mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : left (mapEdge σ e) = reindex σ (left e) := rfl

@[simp] theorem right_mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : right (mapEdge σ e) = reindex σ (right e) := rfl

@[simp] theorem output_mapEdge (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : output (mapEdge σ e) = reindex σ (output e) := rfl

@[simp] theorem reindex_symm (σ : Equiv.Perm (Fin L)) (w : TritWord L) :
    reindex σ.symm (reindex σ w) = w := by
  funext i
  simp [reindex]

@[simp] theorem reindex_symm' (σ : Equiv.Perm (Fin L)) (w : TritWord L) :
    reindex σ (reindex σ.symm w) = w := by
  funext i
  simp [reindex]

@[simp] theorem mapEdge_symm (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : mapEdge σ.symm (mapEdge σ e) = e := by
  apply Subtype.ext
  exact Prod.ext (reindex_symm σ _) (Prod.ext (reindex_symm σ _) (reindex_symm σ _))

@[simp] theorem mapEdge_symm' (σ : Equiv.Perm (Fin L)) {α π : DigitType}
    (e : LocalEdge L α π) : mapEdge σ (mapEdge σ.symm e) = e := by
  apply Subtype.ext
  exact Prod.ext (reindex_symm' σ _) (Prod.ext (reindex_symm' σ _) (reindex_symm' σ _))

abbrev sourceFiber (α π : DigitType) (a : TritWord L) := {e : LocalEdge L α π // left e = a}

/-- Actual degrees are equal; this is an equivalence of original local edges. -/
theorem sourceFiber_card_equal {α π : DigitType} {a b : TritWord L}
    (ha : HasType a α) (hb : HasType b α) :
    Fintype.card (sourceFiber α π a) = Fintype.card (sourceFiber α π b) := by
  classical
  obtain ⟨σ, hσ⟩ := same_type_perm ha hb
  have hinv : reindex σ.symm b = a := by rw [← hσ, reindex_symm]
  let e : sourceFiber α π a ≃ sourceFiber α π b :=
    { toFun := fun x => ⟨mapEdge σ x.val, by rw [left_mapEdge, x.property, hσ]⟩
      invFun := fun x => ⟨mapEdge σ.symm x.val, by rw [left_mapEdge, x.property, hinv]⟩
      left_inv := fun x => by apply Subtype.ext; exact mapEdge_symm σ _
      right_inv := fun x => by apply Subtype.ext; exact mapEdge_symm' σ _ }
  exact Fintype.card_congr e


/-- A source fiber injects into the other endpoint family. -/
theorem source_degree_le_vertices (α π : DigitType) (a : TritWord L) :
    Fintype.card (sourceFiber α π a) ≤ (vertices L α).card := by
  classical
  let f : sourceFiber α π a → {b // b ∈ vertices L α} :=
    fun e => ⟨right e.val, right_mem_vertices e.val⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    apply endpoint_injective α π
    exact Prod.ext (e.property.trans e'.property.symm) (congrArg Subtype.val h)
  simpa using Fintype.card_le_of_injective f hf

/-- Regularity gives the exact edge count without a multinomial formula. -/
theorem source_edge_count {α π : DigitType} {a : TritWord L} (ha : HasType a α) :
    Fintype.card (LocalEdge L α π) =
      (vertices L α).card * Fintype.card (sourceFiber α π a) := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (univ : Finset (LocalEdge L α π))) (t := vertices L α) (f := left)
    (fun e _ => left_mem_vertices e)
  have hf (b : TritWord L) (hb : b ∈ vertices L α) :
      (univ.filter (fun e : LocalEdge L α π => left e = b)).card =
        Fintype.card (sourceFiber α π a) := by
    rw [← Fintype.card_subtype]
    exact sourceFiber_card_equal ((mem_filter.mp hb).2) ha
  calc
    _ = ∑ b ∈ vertices L α, (univ.filter (fun e : LocalEdge L α π => left e = b)).card :=
      by simpa only [card_univ] using h
    _ = ∑ _b ∈ vertices L α, Fintype.card (sourceFiber α π a) :=
      sum_congr rfl (fun b hb => hf b hb)
    _ = _ := by simp

/-- The full edge count pays every individual source-degree square. -/
theorem source_degree_sq_le_edges {α π : DigitType} {a : TritWord L} (ha : HasType a α) :
    (Fintype.card (sourceFiber α π a))^2 ≤ Fintype.card (LocalEdge L α π) := by
  rw [source_edge_count ha, pow_two]
  exact Nat.mul_le_mul_right _ (source_degree_le_vertices α π a)

theorem source_degree_le_prime {α π : DigitType} {a : TritWord L} (ha : HasType a α)
    (P : ℕ) (hE : Fintype.card (LocalEdge L α π) ≤ P^2) :
    Fintype.card (sourceFiber α π a) ≤ P := by
  have h := source_degree_sq_le_edges (π := π) ha
  nlinarith


/-- Endpoint reversal preserves every original local condition. -/
def swapEdge {α π : DigitType} (e : LocalEdge L α π) : LocalEdge L α π := by
  classical
  refine ⟨(right e,left e,output e), mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  have h := edge_data e
  exact ⟨h.2.1,h.1,h.2.2.1,fun i => (Nat.add_comm _ _).trans (h.2.2.2 i)⟩

@[simp] theorem left_swapEdge {α π : DigitType} (e : LocalEdge L α π) :
    left (swapEdge e) = right e := rfl
@[simp] theorem right_swapEdge {α π : DigitType} (e : LocalEdge L α π) :
    right (swapEdge e) = left e := rfl
@[simp] theorem swapEdge_swapEdge {α π : DigitType} (e : LocalEdge L α π) :
    swapEdge (swapEdge e) = e := by apply Subtype.ext; rfl

theorem swapEdge_injective (α π : DigitType) :
    Function.Injective (swapEdge (α := α) (π := π) (L := L)) :=
  Function.LeftInverse.injective (fun e => swapEdge_swapEdge e)

end ThreeSum.TernaryCoverRegularity
