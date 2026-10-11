import Submission.ThreeSum.LightBlockChildrenIndexed

/-!
# Coverage and raw-mass charging in the machine's actual child order

The output-sensitive enumerator uses its recursive coordinate order. The
reporting tree is instantiated with that exact order here; its positive
frontiers retain the original incidences and their multiplicities.
-/

namespace ThreeSum.ReportingHostFrontier

open Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostMasks BlockForced
open scoped BigOperators

def children {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) : List (Finset (Fin (512*h))) :=
  if hk : k < J then localChildren ⟨k,hk⟩ (outputRows q ⟨k,hk⟩) h else []

theorem mem_children_iff {h J : ℕ} (q : GlobalOutput h J) (k : ℕ)
    (S : Finset (Fin (512*h))) : S ∈ children q k ↔ S ∈ RawReporting.children q k := by
  unfold children RawReporting.children
  split
  · exact localChildren_mem _ _ _ _
  · rfl

theorem children_nodup {h J : ℕ} (q : GlobalOutput h J) (k : ℕ) :
    (children q k).Nodup := by
  unfold children
  split
  · exact localChildren_nodup _ _ _
  · exact List.nodup_nil

theorem children_length {h J k : ℕ} (q : GlobalOutput h J) (hk : k < J) :
    (children q k).length = groupSize h := by
  rw [children,dif_pos hk,localChildren_length]
  have hc : (outputRows q ⟨k,hk⟩).card = 2*h :=
    LayerCounts.mem_vertices.mp (q ⟨k,hk⟩).2.property
  rw [hc]
  rfl

section Indices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

def frontier {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :=
  Reporting.frontier (children w.2.2) (prefixQuery I w) k

theorem word_children {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α)
    (r : RawItem h J α β γ) (hr : r ∈ domain I w) (j : ℕ) (hj : j < J) :
    (word r)[j]'(by rw [word,partitionWord_length]; exact hj) ∈ children w.2.2 j :=
  (mem_children_iff _ _ _).mpr (RawReporting.word_children I w r hr j hj)

theorem mem_frontier_iff {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) (pre : List (Finset (Fin (512*h)))) :
    pre ∈ frontier I w k ↔ ∃ r ∈ I, wantedOf r = w ∧ (word r).take k = pre := by
  rw [frontier,Reporting.mem_frontier_iff (domain I w) word (fun _ => 1)
    (children w.2.2) (prefixQuery I w) J k
    (fun r _ => partitionWord_length r.2.1) (word_children I w)
    (fun _ _ _ => rfl) hk]
  rw [Reporting.mass_pos_iff]
  simp only [domain,Finset.mem_filter,Nat.lt_one_iff,and_true]
  constructor
  · rintro ⟨r,⟨hr,hw⟩,hp⟩
    exact ⟨r,hr,hw,hp⟩
  · rintro ⟨r,hr,hw,hp⟩
    exact ⟨r,⟨hr,hw⟩,hp⟩

omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] in
theorem frontier_nodup {h J : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (k : ℕ) : (frontier I w k).Nodup :=
  Reporting.frontier_nodup _ _ (children_nodup _) _

theorem frontier_length_le_domain {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k ≤ J) : (frontier I w k).length ≤ (domain I w).card := by
  have h := Reporting.frontier_length_le_mass (domain I w) word (fun _ => 1)
    (children w.2.2) (prefixQuery I w) J k
    (fun r _ => partitionWord_length r.2.1) (word_children I w)
    (fun _ _ _ => rfl) (children_nodup w.2.2) hk
  simpa only [frontier,Finset.sum_const,smul_eq_mul,mul_one] using h

theorem total_frontier_length_le_raw_card {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k ≤ J) : (∑ w : Wanted h J α, (frontier I w k).length) ≤ I.card := by
  calc
    _ ≤ ∑ w : Wanted h J α, (domain I w).card := by
      exact Finset.sum_le_sum (fun w _ => frontier_length_le_domain I w hk)
    _ = _ := by
      symm
      exact Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)

theorem true_original_reported {h J : ℕ} {P d : ℤ}
    (T : Finset (Original α β γ)) (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ)
    (hh : 0 < h) (hP : 0 < P) (t : Original α β γ) (ht : t ∈ T)
    (he : difference a b c t = 0) :
    ∃ r ∈ rawOn h J P d T a b c, r.1 = t ∧
      word r ∈ frontier (rawOn h J P d T a b c) (wantedOf r) J := by
  obtain ⟨r,hr,hrt⟩ := raw_true_triple_complete hh hP ht he
  refine ⟨r,hr,hrt,(mem_frontier_iff _ _ le_rfl _).mpr ⟨r,hr,rfl,?_⟩⟩
  simpa only [word,partitionWord_length] using (List.take_length (l := word r))

def candidates {h J : ℕ} (I : Finset (RawItem h J α β γ)) (w : Wanted h J α) (k : ℕ) :=
  (frontier I w k).flatMap fun pre => (children w.2.2 k).map fun S => pre ++ [S]

omit [Fintype α] [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ] in
theorem candidates_length {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (w : Wanted h J α) (hk : k < J) :
    (candidates I w k).length = (frontier I w k).length*groupSize h := by
  rw [candidates,Reporting.generated_candidates_length,children_length _ hk]

theorem total_candidates_le_raw_card {h J k : ℕ} (I : Finset (RawItem h J α β γ))
    (hk : k < J) :
    (∑ w : Wanted h J α, (candidates I w k).length) ≤ I.card*groupSize h := by
  simp only [candidates_length I _ hk,← Finset.sum_mul]
  exact Nat.mul_le_mul_right _ (total_frontier_length_le_raw_card I (Nat.le_of_lt hk))

/-- Sum of the actual verified child-construction time over positive parents. -/
def generationWork {h J : ℕ} (I : Finset (RawItem h J α β γ)) (k : ℕ) : ℕ :=
  ∑ w : Wanted h J α,
    (frontier I w k).length*LightBlockChildren.time (J*(512*h)) (2*h) h

theorem generationWork_le {h J k : ℕ} (I : Finset (RawItem h J α β γ)) (hk : k < J) :
    generationWork I k ≤ I.card*(1600*(J*(512*h)+1)^2*(groupSize h+1)) := by
  rw [generationWork,← Finset.sum_mul]
  exact Nat.mul_le_mul (total_frontier_length_le_raw_card I (Nat.le_of_lt hk))
    (LightBlockChildrenIndexed.time_bound hk)

theorem all_generationWork_le {h J K : ℕ} (I : Finset (RawItem h J α β γ)) (hK : K ≤ J) :
    (∑ k ∈ Finset.range K, generationWork I k) ≤
      K*I.card*(1600*(J*(512*h)+1)^2*(groupSize h+1)) := by
  calc
    _ ≤ ∑ _k ∈ Finset.range K, I.card*(1600*(J*(512*h)+1)^2*(groupSize h+1)) := by
      apply Finset.sum_le_sum
      intro k hk
      exact generationWork_le I ((Finset.mem_range.mp hk).trans_le hK)
    _ = _ := by simp [Nat.mul_assoc]

end Indices

end ThreeSum.ReportingHostFrontier
