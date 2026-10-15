import Submission.ThreeSum.LightTernaryFastProgramProof
import Submission.ThreeSum.TernaryComputedExtensionMenu

noncomputable section
namespace ThreeSum.TernaryGlobalReceiptTransport
open Light LightTernaryGlobalPrelude LightTernaryFastProgramProof LightExtensionBackendLayout
set_option maxHeartbeats 3000000

theorem menu_end (base d p q J : ℕ) :
    physical base d q J+q*q*(J+2)≤base+reserve d p q J := by
  apply le_trans _ (end_le base d p q J)
  unfold sum prod LightExtensionBackendLayout.r h LightExtensionBackendLayout.b a
  omega

theorem menu_keep {p : ℕ} [Fact p.Prime] {base d q J c cut : ℕ} {μ ν : ℕ→ℤ}
    (H : LightTernaryGlobalPreludeProof.Menu μ base d p q J c)
    (K : Kept μ ν cut) (hend : physical base d q J+q*q*(J+2)≤cut) :
    LightTernaryGlobalPreludeProof.Menu ν base d p q J c := by
  intro s hs i hi
  have hm := Nat.mul_le_mul_right (J+2) (Nat.succ_le_of_lt hs)
  rw [K _ (by nlinarith)]
  exact H s hs i hi

/-- Every color invocation reuses the actual found field and menu. The
complete coloring scan preserves these real initialized memory cells. -/
theorem receipt_keep {M b p K κ n free c : ℕ} [Fact p.Prime] {μ ν₀ ν : ℕ→ℤ}
    (H : Receipt M b p K κ n free c μ ν₀)
    (hkeep : Kept ν₀ ν (scanFree M b p K κ n free)) :
    Receipt M b p K κ n free c μ ν := by
  have hfree : free+33≤scanFree M b p K κ n free := by
    unfold scanFree finish backend
    omega
  refine ⟨H.1,?_,?_,?_,?_⟩
  · exact H.2.1.of_kept hkeep (by simp only [header,List.length_cons,List.length_nil]; omega)
  · exact H.2.2.1.of_kept hkeep (by simp only [LightScales.values,List.length_cons,List.length_nil,LightTernaryGlobalPrelude.params]; omega)
  · apply menu_keep H.2.2.2.1 hkeep
    exact menu_end _ _ _ _ _
  · intro i hi
    exact (hkeep i (by omega)).trans (H.2.2.2.2 i hi)

theorem menu_before_colors (M b p K κ n free : ℕ) :
    physical (backend free) (LightTernaryDimensions.dim M b p K n (n^κ))
      (p^(LightTernaryDimensions.dim M b p K n (n^κ))) (LightTernaryDimensions.J M b n (n^κ))+
      (p^(LightTernaryDimensions.dim M b p K n (n^κ)))*
        (p^(LightTernaryDimensions.dim M b p K n (n^κ)))*
        (LightTernaryDimensions.J M b n (n^κ)+2)≤scanFree M b p K κ n free :=
  menu_end _ _ _ _ _

/-- All global-header reads made by the actual per-color preparation are
consequences of the initialized ten-cell header and five-cell scales. -/
theorem preparation_reads {M b p K κ n free c : ℕ} [Fact p.Prime] {μ ν : ℕ→ℤ}
    (H : Receipt M b p K κ n free c μ ν) :
    let par := LightTernaryGlobalPrelude.params free
    let J := LightTernaryDimensions.J M b n (n^κ)
    let d := LightTernaryDimensions.dim M b p K n (n^κ)
    let q := p^d
    let menu := physical (backend free) d q J
    9≤par ∧ par+19≤scanFree M b p K κ n free+6 ∧ menu≤scanFree M b p K κ n free+6 ∧
    ν (par-9)=((n^κ:ℕ):ℤ) ∧ ν (par-8)=(LightTernaryDimensions.r M n:ℤ) ∧
    ν (par-7)=(J:ℤ) ∧ ν (par-5)=(q:ℤ) ∧ ν (par-3)=(menu:ℤ) ∧
    ν par=(Scales.inputBits n:ℤ) := by
  intro par J d q menu
  have hfree : free+33≤scanFree M b p K κ n free := by
    unfold scanFree finish backend
    omega
  have hmenu : menu≤scanFree M b p K κ n free :=
    (Nat.le_add_right _ _).trans (menu_before_colors M b p K κ n free)
  have read (i : ℕ) (hi : i<10) := H.2.1 i (by simpa [header] using hi)
  have h1 : ν (free+1)=((n^κ:ℕ):ℤ) := by simpa [header] using read 1 (by decide)
  have h2 : ν (free+2)=(LightTernaryDimensions.r M n:ℤ) := by simpa [header] using read 2 (by decide)
  have h3 : ν (free+3)=(J:ℤ) := by simpa [header,J] using read 3 (by decide)
  have h5 : ν (free+5)=(q:ℤ) := by simpa [header,q,d] using read 5 (by decide)
  have h7 : ν (free+7)=(menu:ℤ) := by simpa [header,menu,q,d,J] using read 7 (by decide)
  have hbits : ν par=(Scales.inputBits n:ℤ) := by
    simpa [par,LightScales.values] using H.2.2.1 0 (by simp [LightScales.values])
  have hpar : par=free+10 := rfl
  refine ⟨by omega,by omega,by omega,?_,?_,?_,?_,?_,hbits⟩
  · rw [show par-9=free+1 by omega]
    exact h1
  · rw [show par-8=free+2 by omega]
    exact h2
  · rw [show par-7=free+3 by omega]
    exact h3
  · rw [show par-5=free+5 by omega]
    exact h5
  · rw [show par-3=free+7 by omega]
    exact h7

end ThreeSum.TernaryGlobalReceiptTransport
