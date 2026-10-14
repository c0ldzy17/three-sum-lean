import Submission.ThreeSum.TernaryTypeLowerBound
import Submission.ThreeSum.LocalGraph
import Submission.ThreeSum.TernaryCoverPartitionLower
import Submission.ThreeSum.TernaryLocalParameters
import Mathlib.Tactic

noncomputable section
namespace ThreeSum.TernaryPartitionCount
open Finset TernaryJointType TernaryCoverLocal TernaryCoverRegularity TernaryCoverOutputCap
open TernaryTypeLowerBound

abbrev Index (t r s : ℕ) := Fin t ⊕ (Fin (2*r) ⊕ Fin (3*s))
abbrev Parts (r s : ℕ) := {S // S ∈ LayerCounts.vertices (2*r) r} × LocalGraph.Edge (3*s) s

def piType (t r s : ℕ) : DigitType := ![t,2*r,3*s]
def alphaType (t r s : ℕ) : DigitType := ![t+r+s,r+s,s]

abbrev partLeft {t r s : ℕ} (c : Parts r s) : Index t r s → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => if i ∈ c.1.val then 1 else 0
  | Sum.inr (Sum.inr i) => if i ∈ c.2.val.1 then 0 else if i ∈ c.2.val.2 then 2 else 1

abbrev partRight {t r s : ℕ} (c : Parts r s) : Index t r s → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl i) => if i ∈ c.1.val then 0 else 1
  | Sum.inr (Sum.inr i) => if i ∈ c.2.val.1 then 2 else if i ∈ c.2.val.2 then 0 else 1

abbrev targetWord (t r s : ℕ) : Index t r s → Fin 3
  | Sum.inl _ => 0
  | Sum.inr (Sum.inl _) => 1
  | Sum.inr (Sum.inr _) => 2

private theorem left_indicators {r s : ℕ} (c : Parts r s) (i : Fin (3*s)) :
    (if (if i ∈ c.2.val.1 then (0 : Fin 3) else if i ∈ c.2.val.2 then 2 else 1) = 1
      then 1 else 0 : ℕ) = (if i ∉ c.2.val.1 ∪ c.2.val.2 then 1 else 0) ∧
    (if (if i ∈ c.2.val.1 then (0 : Fin 3) else if i ∈ c.2.val.2 then 2 else 1) = 2
      then 1 else 0 : ℕ) = (if i ∈ c.2.val.2 then 1 else 0) := by
  have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
  by_cases hT : i ∈ c.2.val.1 <;> by_cases hU : i ∈ c.2.val.2 <;> simp_all

private theorem right_indicators {r s : ℕ} (c : Parts r s) (i : Fin (3*s)) :
    (if (if i ∈ c.2.val.1 then (2 : Fin 3) else if i ∈ c.2.val.2 then 0 else 1) = 1
      then 1 else 0 : ℕ) = (if i ∉ c.2.val.1 ∪ c.2.val.2 then 1 else 0) ∧
    (if (if i ∈ c.2.val.1 then (2 : Fin 3) else if i ∈ c.2.val.2 then 0 else 1) = 2
      then 1 else 0 : ℕ) = (if i ∈ c.2.val.1 then 1 else 0) := by
  have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
  by_cases hT : i ∈ c.2.val.1 <;> by_cases hU : i ∈ c.2.val.2 <;> simp_all

private theorem remaining_count {r s : ℕ} (c : Parts r s) :
    (∑ i : Fin (3*s), if i ∉ c.2.val.1 ∪ c.2.val.2 then 1 else 0 : ℕ) = s := by
  have ht := LayerCounts.mem_edgeSet.mp c.2.property
  have hf : (univ.filter fun i => i ∉ c.2.val.1 ∪ c.2.val.2) =
      (univ : Finset (Fin (3*s))) \ (c.2.val.1 ∪ c.2.val.2) := by ext; simp
  rw [← card_filter,hf,card_sdiff_of_subset (subset_univ _),card_union_of_disjoint ht.2.2]
  simp [ht.1,ht.2.1]
  omega

private theorem binary_ind_one (P : Prop) [Decidable P] :
    (if (if P then (1 : Fin 3) else 0) = 1 then 1 else 0 : ℕ) = if P then 1 else 0 := by
  by_cases h : P <;> simp [h]
private theorem binary_ind_two (P : Prop) [Decidable P] :
    (if (if P then (1 : Fin 3) else 0) = 2 then 1 else 0 : ℕ) = 0 := by
  by_cases h : P <;> simp [h]
private theorem binary_right_one (P : Prop) [Decidable P] :
    (if (if P then (0 : Fin 3) else 1) = 1 then 1 else 0 : ℕ) = if ¬P then 1 else 0 := by
  by_cases h : P <;> simp [h]
private theorem binary_right_two (P : Prop) [Decidable P] :
    (if (if P then (0 : Fin 3) else 1) = 2 then 1 else 0 : ℕ) = 0 := by
  by_cases h : P <;> simp [h]

theorem source_counts {t r s : ℕ} (c : Parts r s) :
    count (partLeft (t := t) c) 1 = r+s ∧ count (partLeft (t := t) c) 2 = s ∧
    count (partRight (t := t) c) 1 = r+s ∧ count (partRight (t := t) c) 2 = s := by
  have hc := LayerCounts.mem_vertices.mp c.1.property
  have ht := LayerCounts.mem_edgeSet.mp c.2.property
  have hb : (∑ i : Fin (2*r), if i ∉ c.1.val then 1 else 0 : ℕ) = r := by
    rw [← card_filter]
    have he : univ.filter (fun i : Fin (2*r) => i ∉ c.1.val) = univ \ c.1.val := by ext; simp
    rw [he,card_sdiff_of_subset (subset_univ _)]
    simp [hc]
    omega
  have hrem : (univ.filter (fun i : Fin (3*s) => i ∉ c.2.val.1 ∧ i ∉ c.2.val.2)).card = s := by
    simpa using remaining_count c
  have hb' : (∑ i : Fin (2*r), if i ∈ c.1.val then 0 else 1 : ℕ) = r := by
    simpa using hb
  simp only [count,Fintype.sum_sum_type]
  simp_rw [binary_ind_one,binary_ind_two,binary_right_one,binary_right_two,
    (left_indicators c _).1,(left_indicators c _).2,
    (right_indicators c _).1,(right_indicators c _).2]
  simpa [partLeft,partRight,hrem,hb',hc,ht.1,ht.2.1]

theorem parts_add {t r s : ℕ} (c : Parts r s) (i : Index t r s) :
    (partLeft c i).val+(partRight c i).val = (targetWord t r s i).val := by
  have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
  rcases i with i | i
  · rfl
  rcases i with i | i
  · by_cases h : i ∈ c.1.val <;> simp [partLeft,partRight,targetWord,h]
  · by_cases hT : i ∈ c.2.val.1 <;> by_cases hU : i ∈ c.2.val.2 <;>
      simp_all [partLeft,partRight,targetWord]

theorem partLeft_injective {t r s : ℕ} : Function.Injective (partLeft (t := t) (r := r) (s := s)) := by
  intro c d h
  apply Prod.ext
  · apply Subtype.ext
    ext i
    have hi := congrFun h (Sum.inr (Sum.inl i))
    by_cases hc : i ∈ c.1.val <;> by_cases hd : i ∈ d.1.val <;> simp_all [partLeft]
  · apply Subtype.ext
    apply Prod.ext
    · ext i
      have hi := congrFun h (Sum.inr (Sum.inr i))
      have hc := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
      have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp d.2.property).2.2
      by_cases hcT : i ∈ c.2.val.1 <;> by_cases hcU : i ∈ c.2.val.2 <;>
        by_cases hdT : i ∈ d.2.val.1 <;> by_cases hdU : i ∈ d.2.val.2 <;> simp_all [partLeft]
    · ext i
      have hi := congrFun h (Sum.inr (Sum.inr i))
      have hc := disjoint_left.mp (LayerCounts.mem_edgeSet.mp c.2.property).2.2
      have hd := disjoint_left.mp (LayerCounts.mem_edgeSet.mp d.2.property).2.2
      by_cases hcT : i ∈ c.2.val.1 <;> by_cases hcU : i ∈ c.2.val.2 <;>
        by_cases hdT : i ∈ d.2.val.1 <;> by_cases hdU : i ∈ d.2.val.2 <;> simp_all [partLeft]


def canonicalEquiv (t r s : ℕ) : Fin (t+2*r+3*s) ≃ Index t r s :=
  Fintype.equivOfCardEq (by simp [Index,Fintype.card_sum]; omega)

def canonicalTarget (t r s : ℕ) : TritWord (t+2*r+3*s) := targetWord t r s ∘ canonicalEquiv t r s

def canonicalLeft {t r s : ℕ} (c : Parts r s) : TritWord (t+2*r+3*s) :=
  partLeft c ∘ canonicalEquiv t r s

def canonicalRight {t r s : ℕ} (c : Parts r s) : TritWord (t+2*r+3*s) :=
  partRight c ∘ canonicalEquiv t r s

private theorem count_transfer (t r s : ℕ) (w : Index t r s → Fin 3) (d : Fin 3) :
    digitCount (w ∘ canonicalEquiv t r s) d = count w d :=
  Equiv.sum_comp (canonicalEquiv t r s) (fun i => if w i = d then 1 else 0)

private theorem source_type {t r s : ℕ} (w : TritWord (t+2*r+3*s))
    (h1 : digitCount w 1 = r+s) (h2 : digitCount w 2 = s) : HasType w (alphaType t r s) := by
  have hz := count_total w
  change digitCount w 0+digitCount w 1+digitCount w 2 = Fintype.card (Fin (t+2*r+3*s)) at hz
  rw [h1,h2,Fintype.card_fin] at hz
  intro d
  fin_cases d
  · change digitCount w 0 = t+r+s
    omega
  · exact h1
  · exact h2

theorem canonicalTarget_type (t r s : ℕ) : HasType (canonicalTarget t r s) (piType t r s) := by
  intro d
  rw [canonicalTarget,count_transfer]
  simp only [count,Fintype.sum_sum_type]
  fin_cases d <;> simp [targetWord,piType]

def canonicalEdge {t r s : ℕ} (c : Parts r s) :
    LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s) := by
  classical
  have hc := source_counts (t := t) c
  refine ⟨(canonicalLeft c,canonicalRight c,canonicalTarget t r s),
    mem_filter.mpr ⟨mem_univ _, ?_⟩⟩
  refine ⟨source_type _ ?_ ?_,source_type _ ?_ ?_,canonicalTarget_type t r s, ?_⟩
  · exact (count_transfer t r s (partLeft c) 1).trans hc.1
  · exact (count_transfer t r s (partLeft c) 2).trans hc.2.1
  · exact (count_transfer t r s (partRight c) 1).trans hc.2.2.1
  · exact (count_transfer t r s (partRight c) 2).trans hc.2.2.2
  · intro i
    exact parts_add c (canonicalEquiv t r s i)

theorem canonicalEdge_injective {t r s : ℕ} :
    Function.Injective (canonicalEdge (t := t) (r := r) (s := s)) := by
  intro c d h
  apply partLeft_injective (t := t)
  funext i
  have hh := congrFun (congrArg left h) ((canonicalEquiv t r s).symm i)
  simpa [canonicalEdge,canonicalLeft,left] using hh

theorem canonical_output_lower (t r s : ℕ) :
    (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) ≤
    Fintype.card (outputFiber (alphaType t r s) (piType t r s) (canonicalTarget t r s)) := by
  classical
  let f : Parts r s → outputFiber (alphaType t r s) (piType t r s) (canonicalTarget t r s) :=
    fun c => ⟨canonicalEdge c,rfl⟩
  have hf : Function.Injective f := fun _ _ h => canonicalEdge_injective (congrArg Subtype.val h)
  have h := Fintype.card_le_of_injective f hf
  have hc : Fintype.card (Parts r s) =
      (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) := by
    rw [Fintype.card_prod]
    rw [Fintype.card_coe,Fintype.card_coe]
    rw [LayerCounts.vertices_card,LayerCounts.edgeSet_card]
  rw [hc] at h
  exact h

/-- Every genuine fixed-type output has at least the full balanced binary
and balanced ternary partition product. -/
theorem output_partition_lower (t r s : ℕ) (q : TritWord (t+2*r+3*s))
    (hq : HasType q (piType t r s)) :
    (2*r).choose r * ((3*s).choose (2*s) * (2*s).choose s) ≤
    Fintype.card (outputFiber (alphaType t r s) (piType t r s) q) := by
  classical
  obtain ⟨σ,hσ⟩ := same_type_perm (canonicalTarget_type t r s) hq
  let f : outputFiber (alphaType t r s) (piType t r s) (canonicalTarget t r s) →
      outputFiber (alphaType t r s) (piType t r s) q :=
    fun e => ⟨mapEdge σ e.val, by rw [output_mapEdge,e.property,hσ]⟩
  have hf : Function.Injective f := by
    intro e e' h
    apply Subtype.ext
    have hh := congrArg (fun x => mapEdge σ.symm x.val) h
    simpa [f] using hh
  exact (canonical_output_lower t r s).trans (Fintype.card_le_of_injective f hf)


def partitionGroup (r s : ℕ) : ℕ := (2*r).choose r*((3*s).choose s*(2*s).choose s)
def partitionLoss (r s : ℕ) : ℕ := (2*r+1)*(3*s+1)*(2*s+1)

theorem output_partitionGroup_lower (t r s : ℕ) (q : TritWord (t+2*r+3*s))
    (hq : HasType q (piType t r s)) :
    partitionGroup r s ≤ Fintype.card (outputFiber (alphaType t r s) (piType t r s) q) := by
  have h := output_partition_lower t r s q hq
  have he : (3*s).choose (2*s) = (3*s).choose s :=
    Nat.choose_symm_of_eq_add (by omega : 3*s = 2*s+s)
  simpa [partitionGroup,he] using h

theorem output_group_mul_vertices_le_edges (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*partitionGroup r s ≤
    Fintype.card (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by
  classical
  let L := t+2*r+3*s
  let α := alphaType t r s
  let π := piType t r s
  have h := card_eq_sum_card_fiberwise (s := (univ : Finset (LocalEdge L α π)))
    (t := vertices L π) (f := output)
    (fun e _ => mem_filter.mpr ⟨mem_univ _,(edge_data e).2.2.1⟩)
  calc
    _ = ∑ _q ∈ vertices L π, partitionGroup r s := by simp [L,π]
    _ ≤ ∑ q ∈ vertices L π, (univ.filter (fun e : LocalEdge L α π => output e = q)).card := by
      apply sum_le_sum
      intro q hq
      rw [← Fintype.card_subtype]
      exact output_partitionGroup_lower t r s q ((mem_filter.mp hq).2)
    _ = _ := by simpa only [card_univ] using h.symm

/-- The actual graph edge mass pays the full partition cap up to a polynomial. -/
theorem edge_mass_lower (t r s : ℕ) :
    (vertices (t+2*r+3*s) (piType t r s)).card*(2^(2*r)*3^(3*s)) ≤
    partitionLoss r s*Fintype.card
      (LocalEdge (t+2*r+3*s) (alphaType t r s) (piType t r s)) := by
  have hp : 2^(2*r)*3^(3*s) ≤ partitionLoss r s*partitionGroup r s := by
    simpa [partitionLoss,partitionGroup,Nat.mul_assoc] using
      TernaryCoverPartitionLower.partitionCap_le_poly_mul_group r s
  have he := output_group_mul_vertices_le_edges t r s
  calc
    _ ≤ (vertices (t+2*r+3*s) (piType t r s)).card*(partitionLoss r s*partitionGroup r s) :=
      Nat.mul_le_mul_left _ hp
    _ = partitionLoss r s*((vertices (t+2*r+3*s) (piType t r s)).card*partitionGroup r s) := by ring
    _ ≤ _ := Nat.mul_le_mul_left _ he

open TernaryLocalParameters

theorem fixed_edge_mass_lower (m : ℕ) :
    (vertices (fixedLength m) (fixedPi m)).card*(2^(fixedPi m 1)*3^(fixedPi m 2)) ≤
    partitionLoss (7930175*m) (978249*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by
  have h := edge_mass_lower (81204903*m) (7930175*m) (978249*m)
  have hL : 81204903*m+2*(7930175*m)+3*(978249*m) = fixedLength m := by
    simp [fixedLength]; omega
  have hα : alphaType (81204903*m) (7930175*m) (978249*m) = fixedAlpha m := by
    funext d
    fin_cases d <;> simp [alphaType,fixedAlpha] <;> omega
  have hπ : piType (81204903*m) (7930175*m) (978249*m) = fixedPi m := by
    funext d
    fin_cases d <;> simp [piType,fixedPi] <;> omega
  have h1 : 2*(7930175*m) = fixedPi m 1 := by simp [fixedPi]; omega
  have h2 : 3*(978249*m) = fixedPi m 2 := by simp [fixedPi]; omega
  rw [hL,hα,hπ,h1,h2] at h
  exact h

theorem fixed_prime_sq_le_poly_edges (m p : ℕ)
    (hP : p^2 ≤ 16*(vertices (fixedLength m) (fixedPi m)).card*
      (2^(fixedPi m 1)*3^(fixedPi m 2))) :
    p^2 ≤ 16*partitionLoss (7930175*m) (978249*m)*
      Fintype.card (LocalEdge (fixedLength m) (fixedAlpha m) (fixedPi m)) := by
  exact hP.trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left 16 (fixed_edge_mass_lower m))

end ThreeSum.TernaryPartitionCount
