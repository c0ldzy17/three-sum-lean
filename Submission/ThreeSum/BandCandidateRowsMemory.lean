import Submission.ThreeSum.BandCandidateRows
import Submission.ThreeSum.LocalKeyArraySemantics

/-! # List and memory interfaces for the exact candidate record array -/

namespace ThreeSum.BandCandidateRows

open Light BandEnumeration

set_option maxHeartbeats 1300000

theorem mem_records_owner {A B C : Family} {r : Record} (hr : r ∈ records A B C) :
    ∃ o : Owner A B C, fromOwner A B C o=r := by
  rcases List.mem_append.mp hr with hb | hh
  · obtain ⟨j,hj,hk⟩ := List.mem_flatMap.mp hb
    obtain ⟨k,hk,he⟩ := List.mem_map.mp hk
    exact ⟨.inl (⟨j,List.mem_range.mp hj⟩,⟨k,List.mem_range.mp hk⟩),he⟩
  · rcases List.mem_append.mp hh with hb | hc
    · obtain ⟨i,hi,hj⟩ := List.mem_flatMap.mp hb
      obtain ⟨j,hj,he⟩ := List.mem_map.mp hj
      exact ⟨.inr (⟨i,List.mem_range.mp hi⟩,.inl ⟨j,List.mem_range.mp hj⟩),he⟩
    · obtain ⟨i,hi,hk⟩ := List.mem_flatMap.mp hc
      obtain ⟨k,hk,he⟩ := List.mem_map.mp hk
      exact ⟨.inr (⟨i,List.mem_range.mp hi⟩,.inr ⟨k,List.mem_range.mp hk⟩),he⟩

theorem records_sound {A B C : Family} {r : Record}
    (hr : r ∈ records A B C) (hf : r.flag=1) :
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  obtain ⟨o,rfl⟩ := mem_records_owner hr
  exact fromOwner_sound A B C o hf

theorem records_flag {A B C : Family} {r : Record} (hr : r ∈ records A B C) :
    r.flag=0 ∨ r.flag=1 := by
  obtain ⟨o,rfl⟩ := mem_records_owner hr
  rcases o with ⟨j,k⟩ | ⟨i,j | k⟩ <;> exact make_flag _ _ _ _

theorem getD_sound {A B C : Family} {s : ℕ} (hs : s < (records A B C).length)
    (hf : ((records A B C).getD s default).flag=1) :
    let r := (records A B C).getD s default
    r.a < A.size ∧ r.b < B.size ∧ r.c < C.size ∧
      Bands.Relevant A.lower A.upper B.lower B.upper C.lower C.upper (r.a,r.b,r.c) := by
  apply records_sound _ hf
  rw [List.getD_eq_getElem _ _ hs]
  exact List.getElem_mem hs

theorem seg_record {μ : ℕ → ℤ} {dst s : ℕ} {rs : List Record}
    (H : Seg μ dst (cells rs)) (hs : s < rs.length) :
    Seg μ (dst+4*s) (rs.getD s default).cells := by
  intro j hj
  have hj4 : j < 4 := by simpa [Record.cells] using hj
  have hi : s*4+j < (cells rs).length := by rw [cells_length]; omega
  have he := H.getD hi 0
  rw [cells,OutputDecodeOrder.getD_flatMap_uniform rs Record.cells 4
    (by intro r _; rfl) default 0 hs hj4,List.getD_eq_getElem _ _ hj] at he
  simpa only [Nat.mul_comm s 4,Nat.add_assoc] using he

theorem seg_cells {μ : ℕ → ℤ} {dst : ℕ} (rs : List Record)
    (H : ∀ s < rs.length, Seg μ (dst+4*s) (rs.getD s default).cells) :
    Seg μ dst (cells rs) := by
  apply LocalKeyArraySemantics.seg_flatMap_rows rs Record.cells 4 dst (by intro r _; rfl)
  intro s hs j hj
  have hrec := H s hs
  rw [List.getD_eq_getElem _ _ hs] at hrec
  have he := hrec j (by simpa [Record.cells] using hj)
  simpa only [Nat.mul_comm s 4,Nat.add_assoc] using he

theorem seg_rect {μ : ℕ → ℤ} {dst m n : ℕ} (F : ℕ → ℕ → Record)
    (H : ∀ i < m, ∀ j < n, Seg μ (dst+4*(i*n+j)) (F i j).cells) :
    Seg μ dst (cells (rect m n F)) := by
  apply seg_cells
  intro s hs
  have hs' : s < m*n := by rwa [rect_length] at hs
  have hn : 0 < n := by
    by_contra h
    have hn : n=0 := by omega
    simp [hn] at hs'
  have hi : s/n < m := (Nat.div_lt_iff_lt_mul hn).mpr hs'
  have hj : s%n < n := Nat.mod_lt s hn
  have hindex : s/n*n+s%n=s := by simpa only [Nat.mul_comm] using Nat.div_add_mod s n
  have he := H (s/n) hi (s%n) hj
  have hr := rect_getD F hi hj
  rw [hindex] at he hr
  rwa [hr]

theorem record_fields {μ : ℕ → ℤ} {dst : ℕ} {r : Record}
    (H : Seg μ dst r.cells) :
    μ dst=(r.flag : ℤ) ∧ μ (dst+1)=(r.a : ℤ) ∧
      μ (dst+2)=(r.b : ℤ) ∧ μ (dst+3)=(r.c : ℤ) := by
  simpa [Record.cells,seg_cons,Nat.add_assoc] using H

end ThreeSum.BandCandidateRows
