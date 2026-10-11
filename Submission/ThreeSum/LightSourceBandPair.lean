import Submission.ThreeSum.LightSourceBandProgram
import Submission.ThreeSum.SourceBandPairData
import Submission.ThreeSum.LightSortedBands

/-!
# Actual B/C source catalogs from retained normalized headers

The program reads both physical lengths and band counts, and reads the C
shift from its supplied result cell. It constructs the B catalog with shift
zero, then the C catalog, then one shared empty histogram/offset row. The
eight-cell result header retains both catalog pointers and counts, the
empty-row pointer, the next free address, and both original lengths.
-/

namespace ThreeSum.LightSourceBandPair

open Light BandPartition SourceBandPairData

set_option maxHeartbeats 3000000
set_option maxRecDepth 18000

/-- Values B, endpoint header B, values C, endpoint header C, band size,
prime, residue count, selected-shift cell, and result header. -/
def body (pSetup pFill : ℕ) : Stmt :=
  .set 9 (M (v 1)) ;;
  .set 10 (M (v 3)) ;;
  .set 11 (M (v 7)) ;;
  .set 12 (M (v 1 +' k 1)) ;;
  .set 13 (M (v 3 +' k 1)) ;;
  .set 14 (v 8 +' k 8) ;;
  .call pSetup [v 0,v 9,v 4,v 5,v 6,k 0,v 14] 15 ;;
  .call pSetup [v 2,v 10,v 4,v 5,v 6,v 11,v 15] 16 ;;
  .call pFill [v 16,v 6 +' k 1,k 0] 17 ;;
  .set 18 (v 16 +' v 6 +' k 1) ;;
  .store (v 8) (v 14) ;;
  .store (v 8 +' k 1) (v 12) ;;
  .store (v 8 +' k 2) (v 15) ;;
  .store (v 8 +' k 3) (v 13) ;;
  .store (v 8 +' k 4) (v 16) ;;
  .store (v 8 +' k 5) (v 18) ;;
  .store (v 8 +' k 6) (v 9) ;;
  .store (v 8 +' k 7) (v 10) ;;
  .set 0 (v 18)

def time (NL NR g p m U D : ℕ) : ℕ :=
  LightSourceBandSetup.time NL g p m U D+LightSourceBandSetup.time NR g p m U D+
    fillTime (m+1)+2000

def space (base NL NR g p m U D : ℕ) : ℕ :=
  LightSourceResidues.space (next base NL NR g m) p U D

def word (NL NR g p m U D : ℕ) : ℕ :=
  max (LightSourceBandStep.word NL g p m U D) (LightSourceBandStep.word NR g p m U D)+16

structure Procs (P : Program) (pMain : ℕ) where
  pSetup : ℕ
  pFill : ℕ
  setup : LightSourceBandSetup.Procs P pSetup
  fill : P[pFill]?=some fillBody
  main : P[pMain]?=some (body pSetup pFill)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {srcL headL srcR headR shiftCell base NL NR g p m U D : ℕ} {shift : ℤ}
    (fL fR : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+6 < lim.depth)
    (hg : 0 < g) (hp : 0 < p) (hm : 0 < m)
    (hsrcL : srcL+NL ≤ base) (hsrcR : srcR+NR ≤ base)
    (hheadL : headL+2 ≤ base) (hheadR : headR+2 ≤ base) (hshiftCell : shiftCell < base)
    (hspace : space base NL NR g p m U D ≤ lim.space)
    (hword : (word NL NR g p m U D : ℤ) ≤ lim.word)
    (hshift : |shift| ≤ (D : ℤ))
    (hlenL : μ headL=(NL : ℤ)) (hlenR : μ headR=(NR : ℤ))
    (hcountL : μ (headL+1)=(size NL g : ℤ)) (hcountR : μ (headR+1)=(size NR g : ℤ))
    (hshiftRead : μ shiftCell=shift)
    (hreadL : ∀ j < NL, μ (srcL+j)=fL j) (hreadR : ∀ j < NR, μ (srcR+j)=fR j)
    (hvaluesL : ∀ j < NL, |fL j| ≤ (U : ℤ)) (hvaluesR : ∀ j < NR, |fR j| ≤ (U : ℤ)) :
    Meets lim P pMain d [srcL,headL,srcR,headR,g,p,m,shiftCell,base] μ
      (time NL NR g p m U D) (fun r ν =>
        r=(next base NL NR g m : ℤ) ∧
        Stored ν fL fR base NL NR g p m shift ∧ Kept μ ν base) := by
  have ho := ordered base NL NR g m
  have hs : next base NL NR g m ≤ lim.space := by
    unfold space LightSourceResidues.space at hspace
    omega
  have hwl : (LightSourceBandStep.word NL g p m U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_left _ _).trans (Nat.le_add_right _ 16))).trans hword
  have hwr : (LightSourceBandStep.word NR g p m U D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_right _ _).trans (Nat.le_add_right _ 16))).trans hword
  have hnL : (NL : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightSourceBandStep.word; omega)).trans hwl
  have hnR : (NR : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightSourceBandStep.word; omega)).trans hwr
  have hcL := (Int.ofNat_le.mpr (size_le NL g)).trans hnL
  have hcR := (Int.ofNat_le.mpr (size_le NR g)).trans hnR
  have hD : (D : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (by unfold LightSourceBandStep.word LightSourceResidues.word; omega)).trans hwl
  have hshiftW : |shift| ≤ lim.word := hshift.trans hD
  have h8 : (8 : ℤ) ≤ lim.word := by unfold word at hword; omega
  have hleftAddr : base+8 ≤ lim.space := by change leftBase base ≤ lim.space; omega
  have hm1 : m+1 ≤ lim.space := by unfold next at hs; omega
  have hnextAddr : (SourceBandLayout.work (rightBase base NL g m) NR g m : ℤ)+(m : ℤ)+1 ≤ lim.word :=
    (by exact_mod_cast hs :
      (SourceBandLayout.work (rightBase base NL g m) NR g m : ℤ)+(m : ℤ)+1 ≤ lim.space).trans hw
  have hspaceL : LightSourceResidues.space (rightBase base NL g m) p U D ≤ lim.space := by
    unfold space LightSourceResidues.space at hspace
    unfold LightSourceResidues.space
    omega
  have hspaceR : LightSourceResidues.space (zeroBase base NL NR g m) p U D ≤ lim.space := by
    unfold space LightSourceResidues.space at hspace
    unfold LightSourceResidues.space
    omega
  apply Meets.of_body C.main
  unfold body time
  light_set (NL : ℕ) using hlenL
  light_set (NR : ℕ) using hlenR
  light_set shift using hshiftRead
  light_set (size NL g : ℕ) using hcountL
  light_set (size NR g : ℕ) using hcountR
  light_set (leftBase base : ℕ) using leftBase
  have hrunL := C.setup.meets (d := d+1) (μ := μ) (src := srcL) (n := NL)
    (g := g) (p := p) (m := m) (base := leftBase base) (U := U) (D := D) (shift := 0)
    fL hw (by omega) hg hp hm (by unfold leftBase; omega) hspaceL (by simp) hwl hreadL hvaluesL
  light_call hrunL with rL ν₁ ⟨hrL,left,keptL⟩
  have hrL' : rL=(rightBase base NL g m : ℤ) := hrL
  have hreadR' : ∀ j < NR, ν₁ (srcR+j)=fR j := by
    intro j hj
    exact (keptL _ (by unfold leftBase; omega)).trans (hreadR j hj)
  have hrunR := C.setup.meets (d := d+1) (μ := ν₁) (src := srcR) (n := NR)
    (g := g) (p := p) (m := m) (base := rightBase base NL g m) (U := U) (D := D) (shift := shift)
    fR hw (by omega) hg hp hm (by unfold leftBase at ho; omega) hspaceR hshift hwr hreadR' hvaluesR
  light_call hrunR using hrL' with rR ν₂ ⟨hrR,right,keptR⟩
  have hrR' : rR=(zeroBase base NL NR g m : ℤ) := hrR
  have hrunZero := fill_meets (d := d+1) (μ := ν₂) (dst := zeroBase base NL NR g m)
    (n := m+1) (x := 0) C.fill hw (by unfold next at hs; omega)
  light_call hrunZero using hrR' with unused ν₃ ⟨filled,keptZero⟩
  have Kzero : Kept ν₂ ν₃ (zeroBase base NL NR g m) := fun a ha => keptZero a (Or.inl ha)
  have Hdata : Data ν₃ fL fR base NL NR g p m shift := by
    refine ⟨?_,?_,?_⟩
    · intro i hi
      exact ((left i hi).of_kept hm hi keptR (by rfl)).of_kept hm hi Kzero
        (by change rightBase base NL g m ≤ zeroBase base NL NR g m; omega)
    · intro i hi
      exact (right i hi).of_kept hm hi Kzero (by rfl)
    · intro r hr
      exact (filled r (by simpa using (show r < m+1 by omega))).trans (List.getElem_replicate ..)
  light_set (next base NL NR g m : ℕ) using next,hrR'
  light_store base (leftBase base : ℕ)
  light_store (base+1) (size NL g : ℕ)
  light_store (base+2) (rightBase base NL g m : ℕ) using hrL'
  light_store (base+3) (size NR g : ℕ)
  light_store (base+4) (zeroBase base NL NR g m : ℕ) using hrR'
  light_store (base+5) (next base NL NR g m : ℕ)
  light_store (base+6) (NL : ℕ)
  light_store (base+7) (NR : ℕ)
  light_set (next base NL NR g m : ℕ)
  let ν₄ := Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update ν₃ base
      (leftBase base : ℤ)) (base+1) (size NL g : ℤ)) (base+2) (rightBase base NL g m : ℤ))
      (base+3) (size NR g : ℤ)) (base+4) (zeroBase base NL NR g m : ℤ))
      (base+5) (next base NL NR g m : ℤ)) (base+6) (NL : ℤ)) (base+7) (NR : ℤ)
  have hrest : ∀ a, base+8 ≤ a → ν₄ a=ν₃ a := by
    intro a ha
    dsimp only [ν₄]
    repeat' rw [Function.update_of_ne (by omega)]
  refine ⟨rfl,⟨Hdata.transfer hm hrest,?_⟩,?_⟩
  · intro i hi
    have hi' : i < 8 := by simpa only [header,List.length_cons,List.length_nil] using hi
    change ν₄ (base+i)=(header base NL NR g m)[i]
    interval_cases i <;> simp [ν₄,header]
  · intro a ha
    change ν₄ a=μ a
    dsimp only [ν₄]
    repeat' rw [Function.update_of_ne (by omega)]
    exact (Kzero a (by unfold leftBase at ho; omega)).trans
      ((keptR a (by unfold leftBase at ho; omega)).trans (keptL a (by unfold leftBase; omega)))

def program : Program := LightSourceBandProgram.program ++ [body 12 5]

def setupProcs : LightSourceBandSetup.Procs program 12 :=
  ⟨11,10,rfl,⟨9,⟨0,⟨1,6,⟨2,3,4,5,rfl,rfl,rfl,rfl,rfl⟩,⟨7,8,rfl,rfl,rfl⟩,rfl⟩,rfl⟩,rfl⟩,rfl⟩

def programProcs : Procs program 13 := ⟨12,5,setupProcs,rfl,rfl⟩

theorem program_length : program.length=14 := rfl

end ThreeSum.LightSourceBandPair
