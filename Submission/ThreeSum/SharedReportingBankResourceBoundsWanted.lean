import Submission.ThreeSum.SharedReportingBankResourceBoundsWantedIndices
import Submission.ThreeSum.LightReportingWantedLayout
import Submission.ThreeSum.DenseGuard

/-!
# Relative resources for the complete guarded wanted reporter

All buffer extents are relative to the caller's arbitrary free address.
Retained pointers are bounded individually by that address; they are never
summed into a purported size-only bound. Reserving frontier capacity does
not change the separately verified running time.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light Finset GlobalEncoding LocalCoverBounds RawIncidences RawReporting
open ReportingHostWantedLayout ReportingHostFrontierLayout

set_option maxHeartbeats 2600000
set_option maxRecDepth 14000
set_option linter.unusedSectionVars false

def wantedWork (h J K N NB NC : ℕ) : ℕ :=
  (LightReportingWantedLayout.layout 0 h J K N NB NC).work

def wantedNumeric (h J K N NB NC : ℕ) : ℕ :=
  N*NB+N*NB*NC+massBound N NB NC (representationCap h J)+
    J+512*h+K+N+NB+NC+representationCap h J+groupSize h+
    LightBlockQuery.sourceCut h J+1024

def wantedScratch (h J V : ℕ) : ℕ :=
  LightReportingTerminal.space 0 h J+queryWorkSpan h J+
    (Nat.log 2 (V+1)+2)+(512*h+1)+20

def wantedCells (h J K N NB NC V : ℕ) : ℕ :=
  wantedWork h J K N NB NC+wantedNumeric h J K N NB NC+wantedScratch h J V

def wantedDepth (h J K N NB NC : ℕ) : ℕ :=
  K+2*LightBlockQuery.width h J+massBound N NB NC (representationCap h J)+
    2^(LightBlockQuery.width h J)+50

theorem wanted_work_eq (dst h J K N NB NC : ℕ) :
    (LightReportingWantedLayout.layout dst h J K N NB NC).work=
      dst+wantedWork h J K N NB NC := by
  unfold wantedWork LightReportingWantedLayout.layout make slot
    ReportingHostWantedLayout.root packed access decoded
  ring

theorem wanted_work_formula (h J K N NB NC : ℕ) :
    wantedWork h J K N NB NC=44+3*J+
      (K+1)*(4+2*capacityBound N NB NC (representationCap h J) (groupSize h))+
      5*groupSize h+12*2^(LightBlockQuery.width h J)+5*LightBlockQuery.width h J := by
  unfold wantedWork LightReportingWantedLayout.layout make slot
    ReportingHostWantedLayout.root packed access decoded
  ring

theorem wanted_terminal_space_eq (work h J : ℕ) :
    LightReportingTerminal.space work h J=work+LightReportingTerminal.space 0 h J := by
  unfold LightReportingTerminal.space LightReportingTerminalPrepared.space
    LightSourcePreparation.space LightBlockSourceHashes.space LightSourceMaskFlags.space
  omega

theorem wanted_layout_values_le (dst h J K N NB NC : ℕ) {x : ℕ}
    (hx : x∈values (LightReportingWantedLayout.layout dst h J K N NB NC)) :
    x≤(LightReportingWantedLayout.layout dst h J K N NB NC).work := by
  simp only [values,List.mem_cons,List.not_mem_nil,or_false] at hx
  rcases hx with hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx|hx <;> subst x
  all_goals
    dsimp only [LightReportingWantedLayout.layout,make]
    unfold slot
    omega

structure WantedBuffers (lim : Limits) (dst h J K N NB NC V : ℕ) : Prop where
  numeric : (LightReportingWantedLayout.layout dst h J K N NB NC).work+
    wantedNumeric h J K N NB NC≤lim.space
  terminal : LightReportingTerminal.space
    (LightReportingWantedLayout.layout dst h J K N NB NC).work h J≤lim.space
  query : (LightReportingWantedLayout.layout dst h J K N NB NC).work+
    queryWorkSpan h J≤lim.space
  decoder : LightWantedDecode.space
    (LightReportingWantedLayout.layout dst h J K N NB NC).work V≤lim.space
  pack : (LightReportingWantedLayout.layout dst h J K N NB NC).work+(512*h+1)≤lim.space
  parameters : J+512*h+groupSize h+LightBlockQuery.sourceCut h J≤lim.space
  values : ∀ x∈ReportingHostWantedLayout.values
    (LightReportingWantedLayout.layout dst h J K N NB NC), x≤lim.space

theorem wanted_buffers {lim : Limits} {dst h J K N NB NC V : ℕ}
    (hs : dst+wantedCells h J K N NB NC V≤lim.space) :
    WantedBuffers lim dst h J K N NB NC V := by
  have he := wanted_work_eq dst h J K N NB NC
  have ht := wanted_terminal_space_eq
    (LightReportingWantedLayout.layout dst h J K N NB NC).work h J
  have hwork : (LightReportingWantedLayout.layout dst h J K N NB NC).work≤lim.space := by
    unfold wantedCells at hs
    omega
  constructor
  · unfold wantedCells at hs
    omega
  · unfold wantedCells wantedScratch at hs
    omega
  · unfold wantedCells wantedScratch at hs
    omega
  · change (LightReportingWantedLayout.layout dst h J K N NB NC).work+
      (Nat.log 2 (V+1)+2)≤lim.space
    unfold wantedCells wantedScratch at hs
    omega
  · unfold wantedCells wantedScratch at hs
    omega
  · unfold wantedCells wantedNumeric at hs
    omega
  · intro x hx
    exact (wanted_layout_values_le dst h J K N NB NC hx).trans hwork

theorem wanted_guard_word_le {old rootMass threshold M : ℕ}
    (hold : old≤threshold) (hroot : rootMass≤M) :
    old+rootMass+threshold+2≤2*threshold+M+2 := by omega

theorem wanted_guard_word_le_mass {old rootMass threshold M : ℕ}
    (hold : old≤M) (hroot : rootMass≤M) :
    old+rootMass+threshold+2≤2*M+threshold+2 := by omega

section Raw

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem wanted_frontier_length_le {h J K N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hK : K≤J) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    (ReportingHostFrontier.frontier (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w K).length≤
      massBound N NB NC (representationCap h J) := by
  have hh := ReportingHostFrontier.frontier_length_le_domain
    (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w hK
  rw [← rootMass_eq] at hh
  exact hh.trans (root_mass_le A B C a b c w hP hg hA hB hC)

theorem wanted_depth {lim : Limits} {h J K N NB NC d : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hK : K≤J) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC)
    (hd : d+wantedDepth h J K N NB NC≤lim.depth) :
    d+K+2*LightBlockQuery.width h J+
      (ReportingHostFrontier.frontier (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w K).length+
      LightReportingTerminalMasks.count h J K+30≤lim.depth := by
  have hf := wanted_frontier_length_le (shift := shift) A B C a b c w hK hP hg hA hB hC
  have ht := terminal_count_le h J K
  unfold wantedDepth at hd
  omega

theorem wanted_visited_mass_le {h J N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (visited : List (Wanted h J α)) (hn : visited.Nodup)
    (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    DenseGuard.mass (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) visited≤
      massBound N NB NC (representationCap h J) := by
  have hc := raw_card_le (shift := shift) (A ×ˢ (B ×ˢ C)) a b c hP hg
  have hp : (A ×ˢ (B ×ˢ C)).card≤N*NB*NC := by
    rw [Finset.card_product,Finset.card_product]
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul hA (Nat.mul_le_mul hB hC)
  exact (DenseGuard.mass_le_raw_card _ visited hn).trans
    (hc.trans (Nat.mul_le_mul_right _ hp))

end Raw
end ThreeSum.SharedReportingBankResourceBounds
