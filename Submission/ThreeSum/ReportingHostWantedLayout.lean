import Submission.ThreeSum.LightReportingWanted

/-!
# A reusable finite scratch layout for every wanted slot

The capacity uses the original physical input counts and the retained
representation cap. Its memory bound does not charge any traversal time:
only the actual retained frontier cells are visited. A mask span of `2^W`
also bounds every partial-depth terminal candidate array.
-/

namespace ThreeSum.ReportingHostWantedLayout

open Finset GlobalEncoding RawIncidences RawReporting LocalCoverBounds
open ReportingHostFrontierLayout LightBlockQuery

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false

def massBound (N NB NC cap : ℕ) : ℕ := N*NB*NC*cap
def capacityBound (N NB NC cap G : ℕ) : ℕ := (massBound N NB NC cap+1)*G

structure Layout where
  root : ℕ
  masks : ℕ
  childL : ℕ
  childR : ℕ
  counts : ℕ
  selected : ℕ
  maskBase : ℕ
  terminalMasks : ℕ
  masksL : ℕ
  masksR : ℕ
  base : ℕ
  bitBase : ℕ
  rowOut : ℕ
  work : ℕ

def make (root K W G T cap : ℕ) : Layout :=
  let masks := slot root cap (K+1)
  let childL := masks+G
  let childR := childL+G
  let counts := childR+G
  let selected := counts+G
  let maskBase := selected+G
  let terminalMasks := maskBase+T
  let masksL := terminalMasks+T
  let masksR := masksL+T
  let base := masksR+T
  let bitBase := base+2*(2*W+4*T+2)
  let rowOut := bitBase+W
  ⟨root,masks,childL,childR,counts,selected,maskBase,terminalMasks,masksL,masksR,base,bitBase,rowOut,rowOut+2⟩

def values (L : Layout) : List ℕ :=
  [L.root,L.masks,L.childL,L.childR,L.counts,L.selected,L.maskBase,L.terminalMasks,
    L.masksL,L.masksR,L.base,L.bitBase,L.rowOut,L.work]

@[simp] theorem values_length (L : Layout) : (values L).length=14 := rfl

def decoded (dst : ℕ) : ℕ := dst+14
def access (dst J : ℕ) : ℕ := decoded dst+4+J+J
def packed (dst J : ℕ) : ℕ := access dst J+20
def root (dst J : ℕ) : ℕ := packed dst J+J

theorem root_eq (dst J : ℕ) : root dst J=dst+38+3*J := by
  unfold root packed access decoded
  omega

structure Bounds (L : Layout) (root K W G T cap : ℕ) : Prop where
  root_eq : L.root=root
  frontier : slot root cap (K+1)≤L.masks
  masks : L.masks+G≤L.childL
  childL : L.childL+G≤L.childR
  childR : L.childR+G≤L.counts
  counts : L.counts+G≤L.selected
  selected : L.selected+G≤L.maskBase
  queryMasks : L.maskBase+T≤L.work
  terminalFrontier : slot root cap (K+1)≤L.terminalMasks
  terminalMasks : L.terminalMasks+T≤L.masksL
  masksL : L.masksL+T≤L.masksR
  masksR : L.masksR+T≤L.base
  stop : LightReportingTerminalPreparation.stop L.base W T≤L.bitBase
  bits : L.bitBase+W≤L.rowOut
  rowOut : L.rowOut+2≤L.work

theorem make_bounds {root K W G T cap cap' : ℕ} (hc : cap≤cap') :
    Bounds (make root K W G T cap') root K W G T cap := by
  have hf : slot root cap (K+1)≤slot root cap' (K+1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_left _ (by omega)) _
  refine ⟨rfl,hf,le_rfl,le_rfl,le_rfl,le_rfl,le_rfl,?_,?_,le_rfl,le_rfl,le_rfl,?_,le_rfl,le_rfl⟩
  · simp only [make]
    omega
  · simp only [make]
    omega
  · rfl

theorem terminal_count_le (h J k : ℕ) : LightReportingTerminalMasks.count h J k≤2^(width h J) := by
  have hh : (J-k)*(2*h)≤width h J := by
    exact (Nat.mul_le_mul_left _ (by omega : 2*h≤512*h)).trans
      (Nat.mul_le_mul_right _ (Nat.sub_le J k))
  exact (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) hh)

theorem terminal_stop_mono {base W n T : ℕ} (hn : n≤T) :
    LightReportingTerminalPreparation.stop base W n≤LightReportingTerminalPreparation.stop base W T := by
  unfold LightReportingTerminalPreparation.stop LightReportingTerminalPreparation.span
  omega

section Mass

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem raw_card_le {h J : ℕ} {P shift : ℤ}
    (T : Finset (Original α β γ)) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (hP : 0<P) (hg : 4*P≤globalModulus h J) :
    (rawOn h J P shift T a b c).card≤T.card*representationCap h J := by
  change rawMass h J P shift T a b c≤_
  rw [rawMass_eq_sum_witnesses]
  calc
    _ ≤ ∑ _t∈T, representationCap h J := Finset.sum_le_sum (fun _ _ => witnesses_card_bound hP hg)
    _ = _ := by simp

theorem root_mass_le {h J N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    rootMass (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w≤
      massBound N NB NC (representationCap h J) := by
  rw [rootMass_eq]
  have hp : (A ×ˢ (B ×ˢ C)).card≤N*NB*NC := by
    rw [Finset.card_product,Finset.card_product]
    calc
      _ ≤ N*(NB*NC) := Nat.mul_le_mul hA (Nat.mul_le_mul hB hC)
      _ = _ := by ring
  exact (Finset.card_filter_le _ _).trans
    ((raw_card_le (A ×ˢ (B ×ˢ C)) a b c hP hg).trans
      (Nat.mul_le_mul_right _ hp))

theorem capacity_le {h J N NB NC : ℕ} {P shift : ℤ}
    (A : Finset α) (B : Finset β) (C : Finset γ) (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ)
    (w : Wanted h J α) (hP : 0<P) (hg : 4*P≤globalModulus h J)
    (hA : A.card≤N) (hB : B.card≤NB) (hC : C.card≤NC) :
    capacity (rawOn h J P shift (A ×ˢ (B ×ˢ C)) a b c) w≤
      capacityBound N NB NC (representationCap h J) (groupSize h) :=
  Nat.mul_le_mul_right _ (Nat.add_le_add_right (root_mass_le A B C a b c w hP hg hA hB hC) 1)

end Mass

end ThreeSum.ReportingHostWantedLayout
