import Submission.ThreeSum.TernaryArenaSeedData

noncomputable section
namespace ThreeSum.TernaryArenaPrefixInputs
open Light TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaSeedData TernaryExtensionEncoding
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

/-- Reads made by the original-feature and extension-menu initializers. All
addresses are in the immutable input prefix, before the arena. -/
structure Originals (I : Input) (A : Inputs) (seedCount featureBound tagBound positionCap : ℕ)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (L R O : ℕ→ℕ→ℤ) (initial : ℕ→ℤ) : Prop where
  BEnd : A.Bmatrix+I.nB*(A.J+2)≤I.free
  CEnd : A.Cmatrix+I.nC*(A.J+2)≤I.free
  OEnd : A.Omatrix+I.requesterCount*(A.J+2)≤I.free
  menuEnd : A.menu+seedCount*(A.J+2)≤I.free
  positionEnd : A.positions+I.requesterCount≤I.free
  leftEnd : A.leftTagged+I.nB*(A.J+2)≤I.free
  rightEnd : A.rightTagged+I.nC*(A.J+2)≤I.free
  feature : featureBound<p
  BBound : ∀i<I.nB,∀t<A.J+2, |L i t|≤(featureBound : ℤ)
  CBound : ∀i<I.nC,∀t<A.J+2, |R i t|≤(featureBound : ℤ)
  OBound : ∀i<I.requesterCount,∀t<A.J+2, |O i t|≤(featureBound : ℤ)
  leftBound : ∀i<I.nB,∀t<A.J+2, |L i t|≤(tagBound : ℤ)
  rightBound : ∀i<I.nC,∀t<A.J+2, |R i t|≤(tagBound : ℤ)
  BRead : ∀i<I.nB,∀k<A.J+2, initial (A.Bmatrix+i*(A.J+2)+k)=
    physical (J := A.J) (fun i t => L i t.val) i k
  CRead : ∀i<I.nC,∀k<A.J+2, initial (A.Cmatrix+i*(A.J+2)+k)=
    physical (J := A.J) (fun i t => R i t.val) i k
  ORead : ∀i<I.requesterCount,∀k<A.J+2, initial (A.Omatrix+i*(A.J+2)+k)=
    physical (J := A.J) (fun i t => O i t.val) i k
  menuRead : ∀ordinal<seedCount,∀(k : ℕ) (hk : k<A.J+2),
    initial (A.menu+ordinal*(A.J+2)+k)=
      (TernaryOriginalRowMenu.seedRow (A.J+2) ℓ (seeds ordinal) (digitOrder A.J ⟨k,hk⟩)).val
  positionRead : ∀i<I.requesterCount,initial (A.positions+i)=(I.positions i : ℤ)
  positionBound : ∀i<I.requesterCount,I.positions i≤positionCap
  leftRead : ∀i<I.nB,∀t<A.J+2,
    initial (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J t)=L i t
  rightRead : ∀i<I.nC,∀t<A.J+2,
    initial (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J t)=R i t


/-- Actual arena/header initialization preserves the original prefix
certificate whenever it keeps all cells before the arena free pointer. -/
theorem Originals.of_kept {I : Input} {A : Inputs} {seedCount featureBound tagBound positionCap : ℕ}
    {ℓ : E→ₗ[ZMod p] ZMod p} {seeds : ℕ→E×E} {L R O : ℕ→ℕ→ℤ} {μ ν : ℕ→ℤ}
    (H : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O μ)
    (hk : Kept μ ν I.free) : Originals I A seedCount featureBound tagBound positionCap ℓ seeds L R O ν := by
  have cell_lt {base count i k : ℕ} (hend : base+count*(A.J+2)≤I.free)
      (hi : i<count) (hki : k<A.J+2) : base+i*(A.J+2)+k<I.free := by nlinarith
  exact { H with
    BRead:=fun i hi k hki => (hk _ (cell_lt H.BEnd hi hki)).trans (H.BRead i hi k hki)
    CRead:=fun i hi k hki => (hk _ (cell_lt H.CEnd hi hki)).trans (H.CRead i hi k hki)
    ORead:=fun i hi k hki => (hk _ (cell_lt H.OEnd hi hki)).trans (H.ORead i hi k hki)
    menuRead:=fun ordinal ho k hki => (hk _ (cell_lt H.menuEnd ho hki)).trans (H.menuRead ordinal ho k hki)
    positionRead:=fun i hi => (hk _ (by have hh:=H.positionEnd;omega)).trans (H.positionRead i hi)
    leftRead:=fun i hi t ht => (hk _ (cell_lt H.leftEnd hi (TernarySignedLayout.offset_lt ht))).trans (H.leftRead i hi t ht)
    rightRead:=fun i hi t ht => (hk _ (cell_lt H.rightEnd hi (TernarySignedLayout.offset_lt ht))).trans (H.rightRead i hi t ht) }

end ThreeSum.TernaryArenaPrefixInputs
