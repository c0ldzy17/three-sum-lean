import Submission.ThreeSum.EncodedColorPipelineData

/-! # Keep the complete selected-color payload while later stages extend memory -/

namespace ThreeSum.EncodedColorPipelineData

open Light Scales BandScales ColorClassLists EncodedColorNormalizedData

set_option maxHeartbeats 1400000
set_option maxRecDepth 10000

theorem Stored.heads_read {μ : ℕ → ℤ} {free n : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : Stored μ free n color x A B C hsA hsB hsC) :
    let out := finish free n A B C hsA hsB hsC
    μ out=(EncodedColorLayout.prime free n (bandSize n) : ℤ) ∧
    μ (out+1)=(coverBase free n : ℤ) ∧
    μ (out+2)=(wantedHeader free n (incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+3)=(controls free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+4)=(bankHeader free n A B C hsA hsB hsC : ℤ) ∧
    μ (out+5)=(out+8 : ℕ) ∧
    μ (out+6)=((incidences n A B C hsA hsB hsC).length : ℤ) ∧
    μ (out+7)=(EncodedColorPrimeReadyData.selected n A B C hsA hsB hsC : ℤ) := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 0) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 1) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 2) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 3) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 4) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 5) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 6) (by simp [values,LightEncodedColorResult.values]) 0
  · simpa [values,LightEncodedColorResult.values] using H.heads.getD (i := 7) (by simp [values,LightEncodedColorResult.values]) 0

theorem Stored.of_kept {μ ν : ℕ → ℤ} {free n stop : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)}
    (H : Stored μ free n color x A B C hsA hsB hsC) (K : Kept μ ν stop)
    (hstop : finish free n A B C hsA hsB hsC+8 ≤ stop) :
    Stored ν free n color x A B C hsA hsB hsC := by
  obtain ⟨hprime,hfree,hcover,hwanted,hcontrol,hbank⟩ := ordered free n A B C hsA hsB hsC
  have hcoverStop : EncodedColorLayout.cover free n (bandSize n) (radix n) (primeWindow n) ≤ stop := by
    change coverBase free n ≤ stop
    omega
  obtain ⟨hav,hae,hbv,hbe,hcv,hce,htables,hrecords,hcatalog⟩ :=
    EncodedColorLayout.normalized_ends_cover free n (bandSize n) (radix n) (primeWindow n)
  have hkey : LightCoverKeyData.keyEnd (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n)) ≤ stop := by
    have hh : wantedHeader free n (incidences n A B C hsA hsB hsC).length=
        LightCoverKeyData.keyEnd (coverBase free n) (microHalf (inputBits n)) (blockCount (inputBits n))+
          3*(incidences n A B C hsA hsB hsC).length := rfl
    omega
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact H.heads.of_kept K (by simpa [values,LightEncodedColorResult.values] using hstop)
  · exact H.normalizedHeads.of_kept K (by
      simpa [EncodedColorLayout.normalizedHeads] using (show free+8 ≤ stop by omega))
  · rw [K _ (by unfold EncodedColorLayout.prime at hprime; omega)]
    exact H.countCell
  · exact H.normalized.keep K (length_classList_le color x 0 1) (length_classList_le color x 1 1)
      (length_classList_le color x 2 (-1)) (hav.trans hcoverStop) (hae.trans hcoverStop)
      (hbv.trans hcoverStop) (hbe.trans hcoverStop) (hcv.trans hcoverStop) (hce.trans hcoverStop)
      (htables.trans hcoverStop) (hrecords.trans hcoverStop) (hcatalog.trans hcoverStop)
  · exact H.primes.of_kept K (by change coverBase free n ≤ stop; omega)
  · exact H.cover.of_kept (fun i hi => K i (hi.trans_le hkey))
  · exact EncodedColorWantedData.of_kept H.wanted K (by change controls free n A B C hsA hsB hsC ≤ stop; omega)
  · exact H.sources.of_kept K (by change finish free n A B C hsA hsB hsC ≤ stop; omega)
  · rw [K _ (by omega)]
    exact H.countBound
  · apply H.lifts.of_kept K
    rw [RawAKeyLists.keys_length]
    change wantedHeader free n (incidences n A B C hsA hsB hsC).length ≤ stop
    omega

theorem Output.of_kept {μ ν : ℕ → ℤ} {free n stop : ℕ} {color : Coloring.Parameter (inputBits n+1)}
    {x : Fin n → ℤ} {r : ℤ} (H : Output μ free n color x r) (K : Kept μ ν stop)
    (hstop : r.toNat+8 ≤ stop) : Output ν free n color x r := by
  obtain ⟨A,hsA,B,hsB,C,hsC,hr,H⟩ := H
  rw [hr,Int.toNat_natCast] at hstop
  exact ⟨A,hsA,B,hsB,C,hsC,hr,H.of_kept K hstop⟩

end ThreeSum.EncodedColorPipelineData
