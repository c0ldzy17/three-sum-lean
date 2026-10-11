import Submission.ThreeSum.SourceBandBankLayout

/-! # Retained common-band source catalog with one occurrence table -/

namespace ThreeSum.SourceBandBankData

open Light GlobalEncoding SourceBandBankLayout OutputDecodeRecords

def first (base : ℕ) : ℕ := base+5
def finish (base NL NR g h J cut : ℕ) : ℕ :=
  baseAt (first base) h J cut (SourceBandPairSlices.count NL NR g)

def header (base NL NR g h J cut occ : ℕ) : List ℤ :=
  [first base,SourceBandPairSlices.count NL NR g,span h J cut,
    finish base NL NR g h J cut,occ]

structure Stored (μ : ℕ → ℤ) (fL fR : ℕ → ℤ) (base NL NR g h J cut occ : ℕ) (p shift : ℤ) : Prop where
  heads : Seg μ base (header base NL NR g h J cut occ)
  banks : ∀ i < SourceBandPairSlices.count NL NR g,
    At μ fL fR (first base) NL NR g h J cut p shift i
  rows : ∀ k < LightBlockSourceCatalog.count h J, ∀ j < J,
    μ (occ+k*J+j)=((OutputDecodeOrder.indices (scheduleSize h) J k).getD j 0 : ℤ)

theorem Stored.decoded {μ : ℕ → ℤ} {fL fR : ℕ → ℤ} {base NL NR g h J cut occ i k : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift)
    (hi : i < SourceBandPairSlices.count NL NR g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ (baseAt (first base) h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k)
      p shift (SourceBandPartition.source NL g i) (fun t : Fin NL => fL t.val)
      (SourceBandPartition.source NR g i) (fun t : Fin NR => fR t.val)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  (H.banks i hi).decoded hk

theorem Stored.of_kept {μ ν : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g h J cut occ bound : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift)
    (K : Kept μ ν bound) (hocc : occ+LightBlockSourceCatalog.count h J*J ≤ base)
    (hb : finish base NL NR g h J cut ≤ bound) :
    Stored ν fL fR base NL NR g h J cut occ p shift := by
  have hbase : base+5 ≤ finish base NL NR g h J cut := Nat.le_add_right _ _
  refine ⟨?_,?_,?_⟩
  · intro i hi
    have hi' : i < 5 := by simpa only [header,List.length_cons,List.length_nil] using hi
    exact (K _ (by omega)).trans (H.heads i hi)
  · intro i hi
    exact (H.banks i hi).of_kept K
      ((baseAt_mono (first base) h J cut (by omega)).trans hb)
  · intro k hk j hj
    have hp := Nat.mul_le_mul_right J (show k+1 ≤ LightBlockSourceCatalog.count h J by omega)
    exact (K _ (by nlinarith)).trans (H.rows k hk j hj)

theorem Stored.heads_read {μ : ℕ → ℤ} {fL fR : ℕ → ℤ}
    {base NL NR g h J cut occ : ℕ} {p shift : ℤ}
    (H : Stored μ fL fR base NL NR g h J cut occ p shift) :
    μ base=(first base : ℤ) ∧ μ (base+1)=(SourceBandPairSlices.count NL NR g : ℤ) ∧
    μ (base+2)=(span h J cut : ℤ) ∧ μ (base+3)=(finish base NL NR g h J cut : ℤ) ∧
    μ (base+4)=(occ : ℤ) :=
  ⟨by simpa [header] using H.heads.getD (i := 0) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 1) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 2) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 3) (by simp [header]) 0,
    by simpa [header] using H.heads.getD (i := 4) (by simp [header]) 0⟩

end ThreeSum.SourceBandBankData
