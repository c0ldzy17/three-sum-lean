import Submission.ThreeSum.EncodedColorSourcesCosts
import Submission.ThreeSum.SourceFiniteRetention

/-! # Retained finite normalization and actual source controls in one contract -/

namespace ThreeSum.LightEncodedColorFiniteSources

open Light Scales TrimScales BandScales

def base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : ℕ :=
  LightEncodedColorSources.sourceBase free p M (microHalf (inputBits n))
    (blockCount (inputBits n)) xs

def args (free bv be cv ce n p len : ℕ) : List ℤ :=
  [microHalf (inputBits n),blockCount (inputBits n),mu n,bv,be,cv,ce,bandSize n,p,
    LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) len,free]

theorem free_le_base (free n p M : ℕ) [NeZero M] (xs : List ℤ) : free ≤ base free n p M xs := by
  have h := EncodedColorWantedData.header_le_nextFree
    (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length)
    M (LightGuardedWanted.left p xs)
    (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
    (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
    (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ)
  have hk := EncodedColorCoverData.header_end free (microHalf (inputBits n)) (blockCount (inputBits n))
  change _ ≤ base free n p M xs at h
  unfold LightGuardedWanted.wantedFree at h
  omega

variable {lim : Limits} {d : ℕ}

theorem program_meets {μ : ℕ → ℤ} {free av ae bv be cv ce tables rec vals n p U M : ℕ} [NeZero M]
    {originalA originalB originalC A B C xs : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {rA : ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+256*mu n+17 ≤ lim.depth) (hn : 0 < n) (hp : 0 < p)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ free) (hae : ae+2+2*n ≤ free)
    (hbv : bv+n ≤ free) (hbe : be+2+2*n ≤ free)
    (hcv : cv+n ≤ free) (hce : ce+2+2*n ≤ free)
    (htables : tables+ColorBandBounds.count n (bandSize n) ≤ free)
    (hrecords : rec+4*ColorBandBounds.count n (bandSize n) ≤ free)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n (bandSize n)) (bandSize n) ≤ free)
    (hspace : SourceFiniteCosts.space (base free n p M xs) n p U M ≤ lim.space)
    (hword : (SourceFiniteCosts.word n p U M : ℤ) ≤ lim.word)
    (hboundB : ∀ z ∈ originalB, |z| ≤ (U : ℤ)) (hboundC : ∀ z ∈ originalC, |z| ≤ (U : ℤ))
    (H : SourceFiniteData.Normalized μ av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
      originalA originalB originalC A B C hsA hsB hsC rA)
    (hcover : LightCoverKeyData.Stored μ free (microHalf (inputBits n)) (blockCount (inputBits n)))
    (hwanted : LightWantedSetup.Output μ
      (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
      (LightGuardedWanted.left p xs) (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
      (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
      (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)))) :
    Meets lim LightEncodedColorSources.program 80 d (args free bv be cv ce n p xs.length) μ
      (EncodedColorSourcesCosts.time n p U M)
      (fun r ν =>
        SourceFiniteData.Normalized ν av ae bv be cv ce tables rec vals (bandSize n) (bandSize_pos n)
          originalA originalB originalC A B C hsA hsB hsC rA ∧
        SourceFiniteData.Stored ν (base free n p M xs) (bandSize n) p
          (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) B C
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n)) : ℤ) r ∧
        LightCoverKeyData.Stored ν free (microHalf (inputBits n)) (blockCount (inputBits n)) ∧
        LightWantedSetup.Output ν
          (LightGuardedWanted.wantedFree free (microHalf (inputBits n)) (blockCount (inputBits n)) xs.length) M
          (LightGuardedWanted.left p xs) (LightGuardedWanted.right (microHalf (inputBits n)) (blockCount (inputBits n)))
          (3*xs.length) (LightGuardedWanted.totalKeys (microHalf (inputBits n)) (blockCount (inputBits n)))
          (RawAKeyLists.selected M p xs (microHalf (inputBits n)) (blockCount (inputBits n))) ∧
        Kept μ ν (base free n p M xs)) := by
  have repB := H.2.2.1
  have repC := H.2.2.2.1
  have hnB : B.length ≤ n := repB.2.1.trans hB
  have hnC : C.length ≤ n := repC.2.1.trans hC
  have hbase := free_le_base free n p M xs
  have hdepth : d+blockCount (inputBits n)*(512*microHalf (inputBits n))+17 ≤ lim.depth := by
    rwa [BlockSourceSharing.width_eq]
  have hcut : mu n ≤ blockCount (inputBits n)*(512*microHalf (inputBits n)) := by
    rw [BlockSourceSharing.width_eq]
    omega
  have hs := (SourceFiniteCosts.space_le (base := base free n p M xs) (p := p) (U := U) (D := M)
    hn hnB hnC).trans hspace
  have hw' : (LightSourceControlsHost.word B.length C.length (bandSize n) p
      (microHalf (inputBits n)) (blockCount (inputBits n)) (mu n) U M : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (SourceFiniteCosts.word_le hnB hnC)).trans hword
  have run := LightEncodedColorSources.program_meets (μ := μ) (free := free)
    (p := p) (h := microHalf (inputBits n)) (J := blockCount (inputBits n)) (cut := mu n) (U := U) (M := M)
    (xs := xs) hw hdepth hp hcut (by omega) (by omega) (by omega) (by omega) hs hw'
    repB repC hboundB hboundC hcover hwanted
  apply run.mono (EncodedColorSourcesCosts.time_le hn hnB hnC)
  intro r ν ⟨sources,cover,wanted,kept⟩
  exact ⟨H.keep kept hA hB hC (hav.trans hbase) (hae.trans hbase) (hbv.trans hbase) (hbe.trans hbase)
    (hcv.trans hbase) (hce.trans hbase) (htables.trans hbase) (hrecords.trans hbase) (hcatalog.trans hbase),
    sources,cover,wanted,kept⟩

end ThreeSum.LightEncodedColorFiniteSources
