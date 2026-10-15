import Submission.ThreeSum.TernaryArenaSeedPrimitiveGuards
import Submission.ThreeSum.TernaryArenaSeedData

noncomputable section
namespace ThreeSum.TernaryArenaSeedDataReads
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryArenaLayout TernaryArenaSeedCandidate
open LightTernarySeedScoreFactory TernaryArenaSeedData TernaryExtensionEncoding TernaryOriginalRowMenu
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]
set_option maxHeartbeats 6000000

/-- The old packed keys and backend menu coefficients need no extra range
or digit-span assumptions beyond their actual mathematical construction. -/
theorem reads (I : Input) (A : Inputs) (r b ordinal positionCap : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seed : E×E)
    (row : ℕ→(Fin (A.J+2)→ZMod p)→ₗ[ZMod p] ZMod p)
    (L R O : ℕ→Fin (A.J+2)→ℤ) (rows : List (Fin A.J→ZMod p))
    (catalog : ℕ→ℕ→ℕ) (μ : ℕ→ℤ)
    (hBend : A.Bmatrix+I.nB*(A.J+2)≤I.free)
    (hCend : A.Cmatrix+I.nC*(A.J+2)≤I.free)
    (hOend : A.Omatrix+I.requesterCount*(A.J+2)≤I.free)
    (hMenuEnd : A.menu+ordinal*(A.J+2)+(A.J+2)≤I.free)
    (hPositionEnd : A.positions+I.requesterCount≤I.free)
    (hb : b<p)
    (bL : ∀i<I.nB,∀t, |L i t|≤(b : ℤ))
    (bR : ∀i<I.nC,∀t, |R i t|≤(b : ℤ))
    (bO : ∀i<I.requesterCount,∀t, |O i t|≤(b : ℤ))
    (hL : ∀i<I.nB,∀k<A.J+2, μ (A.Bmatrix+i*(A.J+2)+k)=physical L i k)
    (hR : ∀i<I.nC,∀k<A.J+2, μ (A.Cmatrix+i*(A.J+2)+k)=physical R i k)
    (hO : ∀i<I.requesterCount,∀k<A.J+2, μ (A.Omatrix+i*(A.J+2)+k)=physical O i k)
    (hCoeff : ∀(k : ℕ) (hk : k<A.J+2), μ (A.menu+ordinal*(A.J+2)+k)=
      (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨k,hk⟩)).val)
    (oldB : ∀i<I.nB, μ (addr I.free I.capacity 4+i)=(coefficientCode (hash row r L i) : ℤ))
    (oldC : ∀i<I.nC, μ (addr I.free I.capacity 5+i)=(coefficientCode (hash row r R i) : ℤ))
    (oldO : ∀i<I.requesterCount, μ (addr I.free I.capacity 6+i)=(coefficientCode (hash row r O i) : ℤ))
    (hRep : TernaryStoredSpan.Represents catalog (p^r) (rows.map (TernaryPhysicalDigitSpan.reversal A.J)))
    (hCatalog : ∀k<p^r,∀i<A.J, catalog k i<p)
    (hCatalogRead : ∀k<p^r,∀i<A.J, μ (addr I.free I.capacity 7+A.J*k+i)=(catalog k i : ℤ))
    (hPos : ∀i<I.requesterCount, μ (A.positions+i)=(I.positions i : ℤ))
    (hPosBound : ∀i<I.requesterCount, I.positions i≤positionCap) :
    TernaryArenaSeedPrimitiveGuards.Reads I A ordinal
      (data I A r b ordinal ℓ seed row L R O rows catalog) μ positionCap := by
  have value_bound {n : ℕ} (V : ℕ→Fin (A.J+2)→ℤ)
      (h : ∀i<n,∀t, |V i t|≤(b : ℤ)) :
      ∀i<n,∀k<A.J+2, |physical V i k|≤(b : ℤ) := by
    intro i hi k hk
    simpa only [physical,dif_pos hk] using h i hi (digitOrder A.J ⟨k,hk⟩)
  refine {
    matrixB:=hBend
    matrixC:=hCend
    matrixO:=hOend
    menu:=hMenuEnd
    positions:=hPositionEnd
    bB:=hb
    bC:=hb
    bO:=hb
    Bbound:=value_bound L bL
    Cbound:=value_bound R bR
    Obound:=value_bound O bO
    coeffBound:=?_
    oldB:=?_
    oldC:=?_
    oldO:=?_
    BRead:=hL
    CRead:=hR
    ORead:=hO
    coeffRead:=?_
    oldBRead:=oldB
    oldCRead:=oldC
    oldORead:=oldO
    represents:=by
      change TernaryStoredSpan.Represents catalog (p^((r+1)-1)) (rows.map (TernaryPhysicalDigitSpan.reversal A.J))
      set_option backward.isDefEq.respectTransparency false in
        simpa only [Nat.add_sub_cancel] using hRep
    catalogBound:=by simpa only [data,config,Nat.add_sub_cancel] using hCatalog
    catalogRead:=by simpa only [data,config,Nat.add_sub_cancel] using hCatalogRead
    digits:=?_
    positionRead:=hPos
    positionBound:=hPosBound }
  · intro k hk
    simpa only [data,dif_pos hk] using (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨k,hk⟩)).val_lt.le
  · intro i hi
    simpa only [data,config,Nat.add_sub_cancel] using coefficientCode_lt (hash row r L i)
  · intro i hi
    simpa only [data,config,Nat.add_sub_cancel] using coefficientCode_lt (hash row r R i)
  · intro i hi
    simpa only [data,config,Nat.add_sub_cancel] using coefficientCode_lt (hash row r O i)
  · intro k hk
    simpa only [data,dif_pos hk,Config.row,config] using hCoeff k hk
  · intro i hi
    change (if hk : i<A.J+2 then (seedRow (A.J+2) ℓ seed (digitOrder A.J ⟨i,hk⟩)).val else 0)=
      LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits (seedRow (A.J+2) ℓ seed)) i
    rw [dif_pos (show i<A.J+2 by omega),LightStoredSpan.rowValues,dif_pos hi,
      TernaryPhysicalDigitSpan.physicalDigits_val]
    congr 2
    apply Fin.ext
    simp only [digitOrder,Equiv.coe_fn_mk,TernarySignedLayout.offset]
    rw [if_pos hi]

end ThreeSum.TernaryArenaSeedDataReads
