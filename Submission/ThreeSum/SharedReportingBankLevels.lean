import Submission.ThreeSum.SharedReportingBankMemory
import Submission.ThreeSum.LightSwitchDepth

/-! # Exact level layout and retention for one shared source pair -/

namespace ThreeSum.SharedReportingBankLevels

open Light SubsetAddress LightReportingPrefixCatalog LightReportingSuffixCatalog
open SharedReportingBankLayout SharedReportingBankData

set_option maxHeartbeats 1400000

def residual (h J k : ℕ) : ℕ := 2*h*(J-k)
def switch (h J k : ℕ) : ℕ := Switch.switchIndex J k (residual h J k)
def boxCut (h J k : ℕ) : ℕ := residual h J k-switch h J k
def offset (h J : ℕ) : ℕ → ℕ := levelOffset h J (boxCut h J)
def baseAt (base h J k : ℕ) : ℕ := base+offset h J k
def catalogAt (base h J k : ℕ) : ReportingHostLevelData.Catalog :=
  catalog (baseAt base h J k) h J k (boxCut h J k) (switch h J k)

def Built (μ : ℕ → ℤ) (record base h J K : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Prop :=
  ∀ k < K, ∃ hk : k ≤ J, Entry μ (record+5*k) (catalogAt base h J k) hk f g

theorem level_le {J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) : k ≤ J := by
  have hh := Nat.div_mul_le_self (13*J) 20
  unfold LightSwitchDepth.depth at hk
  omega

theorem candidates_nonempty {h J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) :
    (Switch.candidates J k (residual h J k)).Nonempty := by
  by_cases hz : residual h J k=0
  · refine ⟨0,Switch.mem_candidates.mpr ⟨by omega,?_⟩⟩
    simp [Switch.accepts,Switch.cubicNumerator,hz]
  · have hJ : 0 < J := by
      by_contra h
      have he : J=0 := by omega
      simp [residual,he] at hz
    have hdepth : 20*k ≤ 13*J := by
      have hd := Nat.div_mul_le_self (13*J) 20
      unfold LightSwitchDepth.depth at hk
      omega
    exact Switch.candidates_nonempty hJ hdepth (by omega)
      ⟨h*(J-k),by unfold residual; ring⟩

theorem switch_le {h J k : ℕ} (hk : k ≤ LightSwitchDepth.depth J) :
    switch h J k ≤ residual h J k :=
  LightSwitch.index_le_residual (candidates_nonempty hk)

theorem boxCut_le (h J k : ℕ) : boxCut h J k ≤ residual h J k := Nat.sub_le _ _

theorem residual_le_width (h J k : ℕ) : residual h J k ≤ (J-k)*(512*h) := by
  unfold residual
  nlinarith

theorem pre_cut {h J k : ℕ} (hk : k ≤ J) : k*h+boxCut h J k ≤ 2*h*J := by
  have hc := boxCut_le h J k
  have hd := Nat.sub_add_cancel hk
  unfold residual at hc
  nlinarith

theorem count_zero (h : ℕ) : count h 0=1 := by simp [count]
theorem count_succ (h k : ℕ) : count h (k+1)=count h k*localPairs h := by
  simp only [count,localPairs,localWidth,pow_succ]
theorem span_zero (h : ℕ) : prefixSpan h 0=2 := by
  simp [prefixSpan,LightRadixKeys.offset,count]
theorem span_succ (h k : ℕ) : prefixSpan h (k+1)=prefixSpan h k+1+count h (k+1) := by
  unfold prefixSpan
  rw [LightRadixKeys.offset]
  change LightRadixKeys.offset (localPairs h) k+1+count h k+1+count h (k+1)=_
  omega

theorem count_mono (h : ℕ) : Monotone (count h) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by
    have hh := count_pos h 1
    simpa only [count,pow_one] using hh) hij

theorem span_mono (h : ℕ) : Monotone (prefixSpan h) :=
  monotone_nat_of_le_succ (fun k => by rw [span_succ]; omega)

theorem baseAt_zero (base h J : ℕ) : baseAt base h J 0=base := rfl
theorem baseAt_mono (base h J : ℕ) : Monotone (baseAt base h J) := by
  intro i j hij
  exact Nat.add_le_add_left (levelOffset_mono h J (boxCut h J) hij) base

theorem finish_baseAt (base h J k : ℕ) :
    finish (baseAt base h J k) h J k (boxCut h J k)=baseAt base h J (k+1) :=
  finish_level base h J k (boxCut h J)

theorem catalog_low (base h J k : ℕ) :
    base ≤ (catalogAt base h J k).indexBase ∧
    base ≤ (catalogAt base h J k).ptrBase ∧
    base ≤ (catalogAt base h J k).boxBase := by
  have ho := ordered (baseAt base h J k) h J k (boxCut h J k)
  have hb : base ≤ baseAt base h J k := Nat.le_add_right _ _
  dsimp only [catalogAt,catalog,index]
  omega

theorem catalog_end (base h J k : ℕ) :
    (catalogAt base h J k).indexBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).ptrBase+count h k ≤ baseAt base h J (k+1) ∧
    (catalogAt base h J k).boxBase+count h k*
      stride ((J-k)*(512*h)) (boxCut h J k) ≤ baseAt base h J (k+1) := by
  have ho := ordered (baseAt base h J k) h J k (boxCut h J k)
  have hi := index_end (baseAt base h J k) h J k (boxCut h J k)
  have hp : pointers (baseAt base h J k) h k+count h k=boxes (baseAt base h J k) h k := rfl
  have hm : boxes (baseAt base h J k) h k+count h k*
      stride ((J-k)*(512*h)) (boxCut h J k)=masks (baseAt base h J k) h J k (boxCut h J k) := rfl
  rw [← finish_baseAt]
  dsimp only [catalogAt,catalog]
  omega

theorem Built.empty (μ : ℕ → ℤ) (record base h J : ℕ)
    (f g : Finset (Fin (J*(512*h))) → ℤ) : Built μ record base h J 0 f g := by
  intro k hk
  omega

theorem Built.append {μ ν : ℕ → ℤ} {record base h J i : ℕ}
    {f g : Finset (Fin (J*(512*h))) → ℤ} (H : Built μ record base h J i f g)
    (hi : i ≤ J)
    (Hnew : Entry ν (record+5*i) (catalogAt base h J i) hi f g)
    (hkeep : KeptBut μ ν (baseAt base h J i) (record+5*i) 5)
    (hrecord : record+5*i+5 ≤ base) : Built ν record base h J (i+1) f g := by
  intro j hj
  rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
  · obtain ⟨hjJ,Hj⟩ := H j hj
    have hlow := catalog_low base h J j
    have hend := catalog_end base h J j
    have hbefore := baseAt_mono base h J (show j+1 ≤ i by omega)
    refine ⟨hjJ,Hj.of_later hkeep (by omega) hrecord
      (Nat.le_add_right _ _) hlow.1 hlow.2.1 hlow.2.2
      (hend.1.trans hbefore) (hend.2.1.trans hbefore) (hend.2.2.trans hbefore)⟩
  · exact ⟨hi,Hnew⟩

end ThreeSum.SharedReportingBankLevels
