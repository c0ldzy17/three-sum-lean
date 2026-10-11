import Submission.ThreeSum.BandRawAFinite

/-!
# Forward enumeration equivalences for the finite owner slices

B/C local index `j` denotes retained sorted position `band*g+j`.
The A local index denotes physical incidence `count owner+j`, carrying
its exact owner and sorted A coordinate.
-/

namespace ThreeSum.BandRawA

open BandCandidateRows Finset

set_option maxHeartbeats 1500000
set_option maxRecDepth 7000

theorem local_band_mem {n g a j : ℕ} (hj : j < bandLength n g a) :
    BandPartition.start g a+j ∈ bandPositions n g a :=
  mem_image.mpr ⟨j,mem_range.mpr hj,rfl⟩

def finiteBandAt (n g a : ℕ) (j : Fin (bandLength n g a)) : Fin n :=
  ⟨BandPartition.start g a+j.val,bandPositions_lt (local_band_mem j.isLt)⟩

def finiteBandEquiv (n g a : ℕ) :
    Fin (bandLength n g a) ≃ {p : Fin n // p ∈ finiteBandPositions n g a} where
  toFun j := ⟨finiteBandAt n g a j,mem_finiteBandPositions.mpr (local_band_mem j.isLt)⟩
  invFun p := ⟨p.val.val-BandPartition.start g a,by
    have hp := mem_bandPositions.mp (mem_finiteBandPositions.mp p.property)
    unfold bandLength
    omega⟩
  left_inv j := by
    apply Fin.ext
    change BandPartition.start g a+j.val-BandPartition.start g a=j.val
    omega
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    change BandPartition.start g a+(p.val.val-BandPartition.start g a)=p.val.val
    have hp := mem_bandPositions.mp (mem_finiteBandPositions.mp p.property)
    omega

theorem finiteBandEquiv_position (n g a : ℕ) (j : Fin (bandLength n g a)) :
    (finiteBandEquiv n g a j).val.val=BandPartition.start g a+j.val := rfl

theorem finiteBandEquiv_value (n g a : ℕ) (f : ℕ → ℤ) (j : Fin (bandLength n g a)) :
    f (finiteBandEquiv n g a j).val.val=f (BandPartition.start g a+j.val) := rfl

theorem finiteBandPositions_card (n g a : ℕ) :
    (finiteBandPositions n g a).card=bandLength n g a := by
  simpa only [Fintype.card_fin,Fintype.card_coe] using (Fintype.card_congr (finiteBandEquiv n g a)).symm

def finiteAAt (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) : Fin (items n g rs).length :=
  ⟨count n g rs s+j.val,index_lt_items hs j.isLt⟩

def finiteAEquiv (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length) :
    Fin (row n g s (rs.getD s default)).length ≃
      {p : Fin (items n g rs).length // p ∈ finiteAIndices n g rs s} where
  toFun j := ⟨finiteAAt n g rs s hs j,
    mem_finiteAIndices.mpr (mem_aIndices.mpr ⟨j.val,j.isLt,rfl⟩)⟩
  invFun p := ⟨p.val.val-count n g rs s,by
    obtain ⟨j,hj,he⟩ := mem_aIndices.mp (mem_finiteAIndices.mp p.property)
    omega⟩
  left_inv j := by
    apply Fin.ext
    change count n g rs s+j.val-count n g rs s=j.val
    omega
  right_inv p := by
    apply Subtype.ext
    apply Fin.ext
    change count n g rs s+(p.val.val-count n g rs s)=p.val.val
    obtain ⟨j,hj,he⟩ := mem_aIndices.mp (mem_finiteAIndices.mp p.property)
    omega

theorem finiteAEquiv_index (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) :
    (finiteAEquiv n g rs s hs j).val.val=count n g rs s+j.val := rfl

theorem finiteAEquiv_label (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (j : Fin (row n g s (rs.getD s default)).length) :
    labelAt n g rs (finiteAEquiv n g rs s hs j).val.val=
      ⟨s,BandPartition.start g (rs.getD s default).a+j.val⟩ :=
  items_getD hs j.isLt

theorem finiteAEquiv_value (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length)
    (A : ℕ → ℤ) (j : Fin (row n g s (rs.getD s default)).length) :
    valueAt n g rs A (finiteAEquiv n g rs s hs j).val.val=
      A (BandPartition.start g (rs.getD s default).a+j.val) :=
  valueAt_owner A hs j.isLt

theorem finiteAIndices_card (n g : ℕ) (rs : List Record) (s : ℕ) (hs : s < rs.length) :
    (finiteAIndices n g rs s).card=(row n g s (rs.getD s default)).length := by
  simpa only [Fintype.card_fin,Fintype.card_coe] using
    (Fintype.card_congr (finiteAEquiv n g rs s hs)).symm

theorem finiteOwnerProduct_card (nA nB nC g : ℕ) (rs : List Record) (s : ℕ)
    (hs : s < rs.length) :
    (finiteOwnerProduct nA nB nC g rs s).card=
      (row nA g s (rs.getD s default)).length*
        bandLength nB g (rs.getD s default).b*bandLength nC g (rs.getD s default).c := by
  simp only [finiteOwnerProduct,card_product,finiteAIndices_card _ _ _ _ hs,
    finiteBandPositions_card,Nat.mul_assoc]

theorem finiteAllProducts_card (nA nB nC g : ℕ) (rs : List Record) :
    (finiteAllProducts nA nB nC g rs).card=(allProducts nA nB nC g rs).card := by
  simpa only [sum_const,smul_eq_mul,mul_one] using sum_finiteAllProducts (fun _ => 1) nA nB nC g rs

end ThreeSum.BandRawA
