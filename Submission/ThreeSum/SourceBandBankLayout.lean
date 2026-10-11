import Submission.ThreeSum.LightBlockSourceCatalog
import Submission.ThreeSum.SourceBandPairSlices
import Submission.ThreeSum.BlockSourceCatalogCosts

/-! # Complete source banks per common band with preserved earlier banks -/

namespace ThreeSum.SourceBandBankLayout

open Light LightBlockSourceBatchLayout GlobalEncoding BlockSourceOccurrenceOrder

def span (h J cut : ℕ) : ℕ :=
  LightBlockSourceRetainedHost.space
    (work 0 (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J

def baseAt (base h J cut i : ℕ) : ℕ := base+i*span h J cut

theorem work_add (base count W cut : ℕ) : work base count W cut=base+work 0 count W cut := by
  simp only [BlockSourceCatalogCosts.work_address]
  omega

theorem host_space_add (base free h J : ℕ) :
    LightBlockSourceRetainedHost.space (base+free) h J=
      base+LightBlockSourceRetainedHost.space free h J := by
  unfold LightBlockSourceRetainedHost.space LightSourcePreparation.space
    LightBlockSourceHashes.space LightSourceMaskFlags.space LightSourceRetainedStages.space
  omega

theorem complete_end (base h J cut i : ℕ) :
    LightBlockSourceRetainedHost.space
      (work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut) h J=
      baseAt base h J cut (i+1) := by
  rw [work_add,host_space_add]
  unfold baseAt span
  ring

theorem baseAt_mono (base h J cut : ℕ) : Monotone (baseAt base h J cut) := by
  intro i j hij
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ hij) _

theorem work_le_end (base h J cut i : ℕ) :
    work (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) (J*(512*h)) cut ≤
      baseAt base h J cut (i+1) := by
  rw [← complete_end]
  exact (Nat.le_add_right _ _).trans (le_max_left _ _)

theorem word_mono {NL NR NL' NR' h J : ℕ} (hl : NL ≤ NL') (hr : NR ≤ NR') :
    LightBlockSourceRetainedHost.word NL NR h J ≤ LightBlockSourceRetainedHost.word NL' NR' h J := by
  have hpl := Nat.mul_le_mul_left (2^(J*(512*h))) hl
  have hpr := Nat.mul_le_mul_left (2^(J*(512*h))) hr
  unfold LightBlockSourceRetainedHost.word LightSourceRetainedStages.word
  omega

theorem bank_of_kept {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]
    {h J base count cut i bound : ℕ} {μ ν : ℕ → ℤ} {p shift : ℤ}
    {B : Finset β} {b : β → ℤ} {A : Finset γ} {a : γ → ℤ} {q : GlobalOutput h J}
    (H : LightBlockSourceBatch.BankAt μ base count cut i p shift B b A a q)
    (hi : i < count) (K : Kept μ ν bound) (hb : work base count (J*(512*h)) cut ≤ bound) :
    LightBlockSourceBatch.BankAt ν base count cut i p shift B b A a q := by
  have hmask := masks_le_work base count (J*(512*h)) cut
  have hnext := slot_le_masks (base := base) (W := J*(512*h)) (cut := cut)
    (show i+1 ≤ count by omega)
  have hhead := banks_le_work base count (J*(512*h)) cut
  unfold banks at hhead
  refine ⟨?_,?_,?_,?_⟩
  · intro j hj S hS
    have hs := left_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.left j hj S hS)
  · intro j hj S hS
    have hs := right_cell_lt_next (base := base) (count := count) (i := i) hj hS
    exact (K _ (by omega)).trans (H.right j hj S hS)
  · exact (K _ (by omega)).trans H.headerLeft
  · exact (K _ (by omega)).trans H.headerRight

def At (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut : ℕ) (p shift : ℤ) (i : ℕ) : Prop :=
  LightBlockSourceCatalog.Stored μ h J (baseAt base h J cut i) cut p shift
    (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
    (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)

theorem At.of_kept {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i bound : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (K : Kept μ ν bound) (hb : baseAt base h J cut (i+1) ≤ bound) :
    At ν fL fR base NL NR g h J cut p shift i := by
  intro k hk
  exact bank_of_kept (H k hk) hk K ((work_le_end base h J cut i).trans hb)

theorem At.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut i k : ℕ}
    {p shift : ℤ} (H : At μ fL fR base NL NR g h J cut p shift i)
    (hk : k < OutputDecodeRecords.localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt base h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (OutputDecodeRecords.layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (OutputDecodeRecords.outputDefault h J)) :=
  LightBlockSourceCatalog.Stored.decoded H hk

end ThreeSum.SourceBandBankLayout
