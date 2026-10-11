import Submission.ThreeSum.SharedReportingBankCosts
import Submission.ThreeSum.PolynomialResources

/-!
# Explicit finite resource envelopes for the executed shared reporting bank

The envelopes below include the entire header and metadata slab, every
compact payload and construction scratch region, all prefix/local counts,
packed keys, switch intermediates, and both independent source lengths.
They are derived from the actual finite host contract.
-/

namespace ThreeSum.SharedReportingBankResourceBounds

open Light SubsetAddress SharedReportingBankLayout SharedReportingBankLevels
open SharedReportingBankHeader SharedReportingBankRows

set_option maxHeartbeats 2800000
set_option maxRecDepth 14000

def prefixCount (h J : ℕ) : ℕ := 2^(2*((J+1)*(512*h)))
def prefixStorage (h J : ℕ) : ℕ := (levels J+1)*(prefixCount h J+1)
def cellBound (h J : ℕ) : ℕ :=
  2^(512*h)+2*2^(2*(512*h))+2*prefixStorage h J+3*prefixCount h J+
    prefixCount h J*(width h J+1)*2^(width h J)+2^(width h J)+2*(512*h)+3+
    (width h J+1)^2+(width h J+1)
def extent (h J n : ℕ) : ℕ :=
  9+(512*h+1)^2+LightBlockSourceCatalog.count h J*n*n*
    (5*levels J+levels J*cellBound h J)
def depth (h J : ℕ) : ℕ := 512*h+levels J+2*width h J+30
def control (h J n : ℕ) : ℕ :=
  LightBlockSourceCatalog.count h J*n+LightBlockSourceCatalog.count h J+n+n+J+levels J+512
def stateWord (h J : ℕ) : ℕ := J+levels J+512+prefixStorage h J+prefixCount h J
def word (h J n g : ℕ) : ℕ :=
  control h J n+SourceBandBankLayout.span h J (2*h*J)+2^(512*h+1)+2^(2*(512*h))+
    LightSwitchDepth.word J+stateWord h J+LightRadixKeys.word (2^(512*h)) (2^(512*h)) J+
    (width h J+1)*2^(width h J+1)+
    LightReportingSortedCatalog.word (width h J) (2^(2*width h J))+
    2^(width h J)*((2^(width h J)*g)*(2^(width h J)*g))+
    (J+2*h*J+1001)^64

theorem downset_le_pow (W cut : ℕ) : downsetCap W cut ≤ 2^W := by
  have hn := enumerateDownset_nodup W cut
  have hsub : (enumerateDownset W cut).toFinset ⊆ Finset.range (2^W) := by
    intro m hm
    exact Finset.mem_range.mpr ((mem_enumerateDownset W cut m).mp (List.mem_toFinset.mp hm)).1
  have hc := Finset.card_le_card hsub
  simpa [List.toFinset_card_of_nodup hn,enumerateDownset_length] using hc

theorem levels_le (J : ℕ) : levels J ≤ J+1 := by
  have hh := level_le (show LightSwitchDepth.depth J ≤ LightSwitchDepth.depth J from le_rfl)
  unfold levels
  omega

theorem count_le {h J k : ℕ} (hk : k ≤ levels J) :
    LightReportingPrefixCatalog.count h k ≤ prefixCount h J :=
  ReportingHostPackedCatalog.prefix_count_le_pow (hk.trans (levels_le J))

theorem storage_le {h J k : ℕ} (hk : k ≤ levels J) : prefixSpan h k ≤ prefixStorage h J := by
  have hE : 1 ≤ localPairs h := by
    have hh := LightReportingPrefixCatalog.count_pos h 1
    exact Nat.succ_le_of_lt (by
      simpa only [LightReportingPrefixCatalog.count,pow_one,localPairs,localWidth] using hh)
  have hspace := LightRadixKeys.space_bound 0 (localPairs h) k hE
  have hcount := count_le (h := h) hk
  change (localPairs h)^k ≤ prefixCount h J at hcount
  have hspace' : prefixSpan h k ≤ (k+1)*((localPairs h)^k+1) := by
    simpa only [LightRadixKeys.space,Nat.zero_add,prefixSpan,LightReportingPrefixCatalog.count,localPairs,localWidth] using hspace
  exact hspace'.trans (Nat.mul_le_mul (Nat.add_le_add_right hk 1) (Nat.add_le_add_right hcount 1))

theorem local_pairs_le (h : ℕ) : localPairs h ≤ 2^(2*(512*h)) := by
  simpa only [LightReportingPrefixCatalog.count,pow_one,localPairs,localWidth,Nat.one_mul] using
    (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) (J := 1) (k := 1) le_rfl)

theorem cell_le {h J k cut : ℕ} (hk : k < levels J) : cellSize h J k cut ≤ cellBound h J := by
  have hc := count_le (h := h) hk.le
  have hs := storage_le (h := h) hk.le
  have he := local_pairs_le h
  have hh : localChoose h ≤ 2^(512*h) := Nat.choose_le_two_pow _ _
  have hv : (J-k)*(512*h) ≤ width h J := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hcap : cap h J k cut ≤ 2^(width h J) :=
    (downset_le_pow _ _).trans (Nat.pow_le_pow_right (by decide) hv)
  have hbox := Nat.mul_le_mul hc
    (Nat.mul_le_mul (Nat.add_le_add_right hv 1) hcap)
  unfold cellSize SharedReportingBankLayout.finish work masks boxes pointers stageR stageL pairR pairL
    LightReportingSuffixCatalog.stride LightPascal.tableSize cellBound
  change _ ≤ _ at hbox
  simp only [Nat.zero_add]
  dsimp only [suffixWidth,cap,localWidth] at *
  nlinarith

theorem offset_le (h J : ℕ) : offset h J (levels J) ≤ levels J*cellBound h J := by
  have haux : ∀ k, k ≤ levels J → offset h J k ≤ k*cellBound h J := by
    intro k
    induction k with
    | zero => simp [offset,levelOffset]
    | succ k ih =>
      intro hk
      have hh := ih (by omega)
      have hc := cell_le (h := h) (cut := boxCut h J k) (show k < levels J by omega)
      change offset h J k+cellSize h J k (boxCut h J k) ≤ _
      nlinarith
  exact haux _ le_rfl

theorem total_le {NB NC n h J g : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    total h J NB NC g ≤ LightBlockSourceCatalog.count h J*n*n :=
  Nat.mul_le_mul (Nat.mul_le_mul_left _ ((BandPartition.size_le NB g).trans hB))
    ((BandPartition.size_le NC g).trans hC)

theorem space_le {free h J NB NC g n : ℕ} (hB : NB ≤ n) (hC : NC ≤ n) :
    LightSharedReportingHost.space free h J NB NC g ≤ free+extent h J n := by
  have hP := total_le (h := h) (J := J) (g := g) hB hC
  have ho := offset_le h J
  have hm := Nat.mul_le_mul_left (total h J NB NC g) ho
  have hp := Nat.mul_le_mul_right (5*levels J+levels J*cellBound h J) hP
  unfold LightSharedReportingHost.space
  apply max_le
  · unfold records LightPascal.tableSize extent
    omega
  · unfold SharedReportingBankHeader.finish rowBase payload records extent
    nlinarith

theorem index_word_mono {W a b : ℕ} (hab : a ≤ b) :
    LightReportingSortedCatalog.word W a ≤ LightReportingSortedCatalog.word W b := by
  have hm := Nat.mul_le_mul_left ((2^W)^2) (Nat.add_le_add_right hab 1)
  unfold LightReportingSortedCatalog.word LightReportingPackKeys.word
  omega

theorem resources {lim : Limits} {free h J NB NC g n d : ℕ}
    (hB : NB ≤ n) (hC : NC ≤ n)
    (hspace : free+extent h J n ≤ lim.space)
    (hword : (word h J n g : ℤ) ≤ lim.word)
    (hdepth : d+depth h J ≤ lim.depth) :
    LightSharedReportingHost.Resources lim free h J NB NC g d := by
  have budget (x : ℕ) (hx : x ≤ word h J n g) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hs := (space_le (free := free) (h := h) (J := J) (g := g) hB hC).trans hspace
  have hend : SharedReportingBankHeader.finish free h J NB NC g ≤ lim.space := (le_max_right _ _).trans hs
  have hNB := (BandPartition.size_le NB g).trans hB
  have hNC := (BandPartition.size_le NC g).trans hC
  have hmul := Nat.mul_le_mul_left (LightBlockSourceCatalog.count h J) hNB
  have hcount := count_le (h := h) (J := J) (k := levels J) le_rfl
  have hstorage := storage_le (h := h) (J := J) (k := levels J) le_rfl
  have hpowNonneg : (0 : ℤ) ≤ ((2^(512*h) : ℕ) : ℤ) := Int.natCast_nonneg _
  have hpairPowNonneg : (0 : ℤ) ≤ ((2^(2*(512*h)) : ℕ) : ℤ) := Int.natCast_nonneg _
  refine ⟨hs,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,budget _ ?_,?_,?_⟩
  · unfold LightSharedReportingBank.controlWord word control
    omega
  · unfold word; omega
  · unfold word; omega
  · have he := local_pairs_le h
    unfold word
    omega
  · unfold word; omega
  · unfold depth at hdepth
    omega
  · intro q hq
    refine ⟨budget _ ?_,?_,budget _ ?_,?_,budget _ ?_,?_,?_,?_,?_,?_,?_⟩
    · unfold word stateWord
      omega
    · rw [rowBase_next]
      exact (rowBase_mono _ h J (levels J) (show q+1 ≤ total h J NB NC g from hq)).trans hend
    · unfold word; omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      apply budget
      have hh := LightRadixKeys.word_mono (p := 2^(512*h)) (U := 2^(512*h)) hkJ
      unfold word
      omega
    · unfold word width localWidth
      omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      have hc := index_word_mono (W := width h J) (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      apply budget
      change LightReportingSortedCatalog.word (width h J) (LightReportingPrefixCatalog.count h k) ≤ _
      change LightReportingSortedCatalog.word (width h J) (LightReportingPrefixCatalog.count h k) ≤
        LightReportingSortedCatalog.word (width h J) (2^(2*width h J)) at hc
      unfold word
      omega
    · intro k hk
      have hv : (J-k)*(512*h) ≤ width h J := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
      have hp := Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hv
      have hm := Nat.mul_le_mul hp (Nat.mul_le_mul (Nat.mul_le_mul_right g hp) (Nat.mul_le_mul_right g hp))
      apply budget
      unfold word
      omega
    · intro k hk
      have hr : SharedReportingBankLevels.residual h J k ≤ 2*h*J := Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      have ht := Nat.pow_le_pow_left (show J+SharedReportingBankLevels.residual h J k+1001 ≤ J+2*h*J+1001 by omega) 64
      apply budget
      change (J+SharedReportingBankLevels.residual h J k+1001)^64 ≤ _
      unfold word
      omega
    · unfold depth at hdepth
      omega
    · unfold depth width localWidth at hdepth
      omega
    · intro k hk
      have hkJ : k ≤ J := level_le (show k ≤ LightSwitchDepth.depth J by unfold levels at hk; omega)
      have hc := ReportingHostCatalogIndexCosts.sort_clog_le (ReportingHostPackedCatalog.prefix_count_le_pow (h := h) hkJ)
      unfold depth width localWidth at hdepth
      omega

end ThreeSum.SharedReportingBankResourceBounds
