import Submission.ThreeSum.SourceFiniteInputs
import Submission.ThreeSum.LightSourceControlsHostProgram

/-! # Retained source banks for the concrete normalized finite arrays -/

namespace ThreeSum.SourceFiniteData

open Light GlobalEncoding OutputDecodeRecords BandPartition BandCandidateRows BandRawA

structure Stored (μ : ℕ → ℤ) (base g p h J cut : ℕ) (B C : List ℤ) (shift r : ℤ) : Prop where
  returned : r=(LightSourceControlsHost.finish base B.length C.length g h J cut : ℤ)
  controls : Seg μ base (SourceControlLayout.values h J cut)
  buckets : SourceBandPairData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0)
    (LightSourceControlsHost.sourceBase base) B.length C.length g p (BlockSourceEncoding.modulus h J) shift
  banks : SourceBandBankData.Stored μ (fun j => B.getD j 0) (fun j => C.getD j 0)
    (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J)
    B.length C.length g h J cut
    (LightSourceBandHost.occurrenceBase (LightSourceControlsHost.sourceBase base) B.length C.length g h J)
    (p : ℤ) shift

theorem Stored.occurrence {μ : ℕ → ℤ} {base g p h J cut i k : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (hi : i < SourceBandPairSlices.count B.length C.length g) (hk : k < LightBlockSourceCatalog.count h J) :
    LightBlockSourceBatch.BankAt μ
      (SourceBandBankLayout.baseAt
        (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J+5)
        h J cut i) (LightBlockSourceCatalog.count h J) cut k (p : ℤ) shift
      (finiteBandPositions B.length g i) (fun t : Fin B.length => B.getD t.val 0)
      (finiteBandPositions C.length g i) (fun t : Fin C.length => C.getD t.val 0)
      (BlockSourceOccurrenceOrder.representative h J k) :=
  SourceBandFinite.occurrence H.banks hi hk

theorem Stored.decoded {μ : ℕ → ℤ} {base g p h J cut i k : ℕ} {B C : List ℤ} {shift r : ℤ}
    (H : Stored μ base g p h J cut B C shift r)
    (hi : i < SourceBandPairSlices.count B.length C.length g) (hk : k < localCount h^J) :
    LightBlockSourceBatch.BankAt μ
      (SourceBandBankLayout.baseAt
        (LightSourceBandHost.bankHeader (LightSourceControlsHost.sourceBase base) B.length C.length g h J+5)
        h J cut i) (LightBlockSourceCatalog.count h J) cut
      (OutputDecodeOccurrenceCode.code (scheduleSize h) (layerCount h) J k) (p : ℤ) shift
      (finiteBandPositions B.length g i) (fun t : Fin B.length => B.getD t.val 0)
      (finiteBandPositions C.length g i) (fun t : Fin C.length => C.getD t.val 0)
      ((GlobalKeyEnumeration.globalRecords h J).getD k (outputDefault h J)) :=
  SourceBandFinite.decoded H.banks hi hk

/-- The actual color/band payload with its normalized lists exposed, so
the owner records and finite source banks use the very same B/C witnesses. -/
def Normalized (μ : ℕ → ℤ) (av ae bv be cv ce tables rec vals g : ℕ) (hg : 0 < g)
    (originalA originalB originalC A B C : List ℤ)
    (hsA : A.Pairwise (· < ·)) (hsB : B.Pairwise (· < ·)) (hsC : C.Pairwise (· < ·)) (r : ℤ) : Prop :=
  let rs := sortedRecords A B C g hg hsA hsB hsC
  r=((items A.length g rs).length : ℤ) ∧
    LightBandPreprocessing.Represents μ av ae g hg originalA A hsA ∧
    LightBandPreprocessing.Represents μ bv be g hg originalB B hsB ∧
    LightBandPreprocessing.Represents μ cv ce g hg originalC C hsC ∧
    LightBandEnumeration.Tables μ tables
      (family (fun i => A.getD i 0) A.length g hg (LightSortedBands.getD_strict hsA))
      (family (fun i => B.getD i 0) B.length g hg (LightSortedBands.getD_strict hsB))
      (family (fun i => C.getD i 0) C.length g hg (LightSortedBands.getD_strict hsC)) ∧
    Seg μ rec (cells rs) ∧
    BandRawA.Stored μ vals (LightBandRawA.ownerBase vals rs.length g)
      (LightBandRawA.positionBase vals rs.length g) (fun i => A.getD i 0) (items A.length g rs)

theorem Normalized.to_output {μ : ℕ → ℤ} {av ae bv be cv ce tables rec vals g : ℕ} {hg : 0 < g}
    {originalA originalB originalC A B C : List ℤ}
    {hsA : A.Pairwise (· < ·)} {hsB : B.Pairwise (· < ·)} {hsC : C.Pairwise (· < ·)} {r : ℤ}
    (H : Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r) :
    LightBandRawAColor.Output μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC r :=
  ⟨A,hsA,B,hsB,C,hsC,H⟩

theorem Normalized.of_output {μ : ℕ → ℤ} {av ae bv be cv ce tables rec vals g : ℕ} {hg : 0 < g}
    {originalA originalB originalC : List ℤ} {r : ℤ}
    (H : LightBandRawAColor.Output μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC r) :
    ∃ (A : List ℤ) (hsA : A.Pairwise (· < ·))
      (B : List ℤ) (hsB : B.Pairwise (· < ·)) (C : List ℤ) (hsC : C.Pairwise (· < ·)),
      Normalized μ av ae bv be cv ce tables rec vals g hg originalA originalB originalC A B C hsA hsB hsC r := H

end ThreeSum.SourceFiniteData
