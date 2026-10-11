import Submission.ThreeSum.SourceFiniteData

/-! # Preservation of the original finite normalization and incidence data -/

namespace ThreeSum.SourceFiniteData

open Light BandPartition BandCandidateRows BandRawA

theorem Normalized.keep {μ ν : ℕ → ℤ} {av ae bv be cv ce tables rec vals g n bound : ℕ}
    {hg : 0 < g} {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {r : ℤ}
    (H : Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r)
    (hk : Kept μ ν bound)
    (hA : originalA.length ≤ n) (hB : originalB.length ≤ n) (hC : originalC.length ≤ n)
    (hav : av+n ≤ bound) (hae : ae+2+2*n ≤ bound)
    (hbv : bv+n ≤ bound) (hbe : be+2+2*n ≤ bound)
    (hcv : cv+n ≤ bound) (hce : ce+2+2*n ≤ bound)
    (htables : tables+ColorBandBounds.count n g ≤ bound)
    (hrecords : rec+4*ColorBandBounds.count n g ≤ bound)
    (hcatalog : LightBandRawA.space vals (ColorBandBounds.count n g) g ≤ bound) :
    Normalized ν av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r := by
  obtain ⟨hr,repA,repB,repC,tablesAt,recordRows,incidences⟩ := H
  have hnA := repA.2.1.trans hA
  have hnB := repB.2.1.trans hB
  have hnC := repC.2.1.trans hC
  let FA := family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA)
  let FB := family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB)
  let FC := family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)
  let rs := sortedRecords A B C g hg hsA hsB hsC
  have ha : FA.size ≤ size n g := size_mono hnA
  have hb : FB.size ≤ size n g := size_mono hnB
  have hc : FC.size ≤ size n g := size_mono hnC
  have hcount : LightBandEnumeration.count FA.size FB.size FC.size ≤ ColorBandBounds.count n g := by
    have hm := LightBandEnumeration.count_mono ha hb hc
    have he : LightBandEnumeration.count (size n g) (size n g) (size n g)=ColorBandBounds.count n g := by
      unfold LightBandEnumeration.count ColorBandBounds.count
      ring
    rwa [he] at hm
  have hlen : rs.length ≤ ColorBandBounds.count n g := by
    simpa only [rs,sortedRecords,records_length,FA,FB,FC] using hcount
  have hitems : (items A.length g rs).length ≤ g*rs.length := items_length_le ..
  have hgc := Nat.mul_le_mul_left g hlen
  have hfour := Nat.mul_le_mul_left 4 hlen
  dsimp only [rs] at hitems hgc
  refine ⟨hr,repA.keep hk (by omega) (by omega),repB.keep hk (by omega) (by omega),
    repC.keep hk (by omega) (by omega),?_,?_,?_⟩
  · exact LightBandRawAColor.tables_keep tablesAt hk ((Nat.add_le_add_left hcount tables).trans htables)
  · exact recordRows.of_kept hk (by simpa only [cells_length] using (show rec+4*rs.length ≤ bound by omega))
  · apply incidences.of_kept hk
    all_goals
      change _ ≤ bound
      simp only [LightBandRawA.space,LightBandRawA.positionBase,LightBandRawA.ownerBase,LightBandRawA.capacity] at hcatalog ⊢
      omega

end ThreeSum.SourceFiniteData
