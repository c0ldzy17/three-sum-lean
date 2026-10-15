import Submission.ThreeSum.TernaryArenaOriginalInputs
import Submission.ThreeSum.LightTernaryColorPreparationProof
import Submission.ThreeSum.TernaryComputedExtensionMenu
import Submission.ThreeSum.TernaryArenaSelectedSigned

noncomputable section
namespace ThreeSum.TernaryPreparedOriginals
open Light LightTernaryColorPreparation LightTernaryColorPreparationProof
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryArenaLayout
open TernaryArenaSeedData TernarySignedReduction TernarySignedLayout
open TernaryArenaSelectedSigned TernaryExtensionEncoding
set_option maxHeartbeats 6000000
variable {p : ℕ} [Fact p.Prime]
variable {E : Type*} [Field E] [Fintype E] [DecidableEq E] [Algebra (ZMod p) E]

def input (free n U J C0 weightCap queryTime : ℕ) (A B C : List ℤ) : Input where
  free:=arenaFree free n (LightColorParametersCosts.width n) A.length B.length C.length J U
  capacity:=C0
  prefixFree:=addr (arenaFree free n (LightColorParametersCosts.width n) A.length B.length C.length J U) C0 13
  nB:=B.length
  nC:=C.length
  leftInput:=0
  rightInput:=0
  targets:=0
  positions:=TernaryNativeRequesterCoverage.position J
  requesterCount:=A.length*2^J
  weightCap:=weightCap
  queryTime:=queryTime

def inputs (free n J menu : ℕ) (A B C : List ℤ) : Inputs where
  menu:=menu
  J:=J
  Bmatrix:=bMatrix free n (LightColorParametersCosts.width n)
  Cmatrix:=cMatrix free n (LightColorParametersCosts.width n) B.length J
  Omatrix:=oMatrix free n (LightColorParametersCosts.width n) A.length B.length C.length J
  positions:=positions free n (LightColorParametersCosts.width n) A.length B.length C.length J
  leftTagged:=bMatrix free n (LightColorParametersCosts.width n)
  rightTagged:=cMatrix free n (LightColorParametersCosts.width n) B.length J

@[simp] theorem base_input (free n U J C0 weightCap queryTime : ℕ) (A B C : List ℤ) :
    TernaryArenaSelectedSigned.base (input free n U J C0 weightCap queryTime A B C) J A.length=
      input free n U J C0 weightCap queryTime A B C := rfl

private theorem physical_row {J : ℕ} (raw : Coordinate J→ℤ) (k : ℕ) (hk : k<J+2) :
    physical (J := J) (fun _ t => feature raw t.val) 0 k=feature raw (offset J k) := by
  simp only [physical,dif_pos hk,digitOrder,Equiv.coe_fn_mk]

/-- Every original signed/tagged row and every requester/carry row is read
from the concrete preprocessing matrices, with all endpoints proved. -/
theorem of_matrices (free n U J radix C0 weightCap queryTime menu seedCount : ℕ)
    (A B C : List ℤ) (μ : ℕ→ℤ) (M : Matrices μ free n U J radix A B C)
    (hA : A.length≤n) (hb : 1<radix) (hp : radix<p)
    (ℓ : E→ₗ[ZMod p] ZMod p) (seeds : ℕ→E×E)
    (hmenuEnd : menu+seedCount*(J+2)≤free)
    (hmenu : ∀ordinal<seedCount,∀(k : ℕ)(hk : k<J+2), μ (menu+ordinal*(J+2)+k)=
      (TernaryOriginalRowMenu.seedRow (J+2) ℓ (seeds ordinal) (digitOrder J ⟨k,hk⟩)).val) :
    TernaryArenaPrefixInputs.Originals (input free n U J C0 weightCap queryTime A B C)
      (inputs free n J menu A B C) seedCount radix radix n ℓ seeds
      (left U radix J (fun i => B.getD i 0)) (right U radix J (fun i => C.getD i 0))
      (requester U radix J (fun i => A.getD i 0)) μ := by
  have hEnds := TernaryColorPreparationLayout.matrices_before_work free n
    (LightColorParametersCosts.width n) A.length B.length C.length J
  have hwork : work free n (LightColorParametersCosts.width n) A.length B.length C.length J≤
      (input free n U J C0 weightCap queryTime A B C).free := by
    unfold input arenaFree
    exact Nat.le_add_right _ _
  have hfree : free≤(input free n U J C0 weightCap queryTime A B C).free := by
    change free≤arenaFree free n (LightColorParametersCosts.width n) A.length B.length C.length J U
    unfold arenaFree work oMatrix positions carry cMatrix bMatrix headerAt
    omega
  have hbnd (f : Coordinate J→ℤ) (h : ∀k,|f k|≤(radix:ℤ)) (t : ℕ) :
      |feature f t|≤(radix:ℤ) := feature_abs h t
  refine {
    BEnd:=hEnds.1.trans hwork
    CEnd:=hEnds.2.1.trans hwork
    OEnd:=hEnds.2.2.1.trans hwork
    menuEnd:=hmenuEnd.trans hfree
    positionEnd:=hEnds.2.2.2.1.trans hwork
    leftEnd:=hEnds.1.trans hwork
    rightEnd:=hEnds.2.1.trans hwork
    feature:=hp
    BBound:=?_
    CBound:=?_
    OBound:=?_
    leftBound:=?_
    rightBound:=?_
    BRead:=?_
    CRead:=?_
    ORead:=?_
    menuRead:=hmenu
    positionRead:=?_
    positionBound:=?_
    leftRead:=?_
    rightRead:=?_ }
  · intro i hi t ht
    exact hbnd _ (TernarySignedModes.leftRaw_abs hb _) t
  · intro i hi t ht
    exact hbnd _ (TernarySignedModes.rightRaw_abs hb _) t
  · intro i hi t ht
    exact hbnd _ (TernarySignedModes.requesterRaw_abs hb _ _) t
  · intro i hi t ht
    exact hbnd _ (TernarySignedModes.leftRaw_abs hb _) t
  · intro i hi t ht
    exact hbnd _ (TernarySignedModes.rightRaw_abs hb _) t
  · intro i hi k hk
    change k<J+2 at hk
    set_option backward.isDefEq.respectTransparency false in
      simpa [inputs,left,physical,digitOrder,hk] using
      row_physical_read (M.left i hi) hk
  · intro i hi k hk
    change k<J+2 at hk
    set_option backward.isDefEq.respectTransparency false in
      simpa [inputs,right,physical,digitOrder,hk] using
      row_physical_read (M.right i hi) hk
  · intro i hi k hk
    change k<J+2 at hk
    set_option backward.isDefEq.respectTransparency false in
      simpa [inputs,requester,physical,digitOrder,hk,TernaryNativeRequesterCoverage.position] using row_physical_read (M.requesters i hi).1 hk
  · intro i hi
    exact (M.requesters i hi).2
  · intro i hi
    exact (TernaryNativeRequesterCoverage.position_lt hi).le.trans hA
  · intro i hi t ht
    exact row_logical_read (M.left i hi) ht
  · intro i hi t ht
    exact row_logical_read (M.right i hi) ht

structure Metadata (n U : ℕ) (A B C : List ℤ) : Prop where
  lengthA : A.length≤n
  lengthB : B.length≤n
  lengthC : C.length≤n
  boundA : ∀i<A.length,|A.getD i 0|≤(U:ℤ)
  boundB : ∀i<B.length,|B.getD i 0|≤(U:ℤ)
  boundC : ∀i<C.length,|C.getD i 0|≤(U:ℤ)
  injectiveB : Function.Injective (fun i : Fin B.length => B.getD i.val 0)
  injectiveC : Function.Injective (fun i : Fin C.length => C.getD i.val 0)

theorem sorted_injective (L : List ℤ) (h : L.Pairwise (· < ·)) :
    Function.Injective (fun i : Fin L.length => L.getD i.val 0) := by
  have hn : L.Nodup := h.imp (fun hab => ne_of_lt hab)
  have he : (fun i : Fin L.length => L.getD i.val 0)=L.get := by
    funext i
    simp only [List.getD_eq_getElem _ _ i.isLt,List.get_eq_getElem]
  rw [he]
  exact hn.injective_get

theorem metadata {n U free : ℕ} (color : Coloring.Parameter (LightColorParametersCosts.width n))
    (x : Fin n→ℤ) (A B C : List ℤ) (μ : ℕ→ℤ)
    (hA : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.av free n) n
      (ColorClassLists.classList color x 0 1) A)
    (hB : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.bv free n) n
      (ColorClassLists.classList color x 1 1) B)
    (hC : LightTernaryColorPrelude.Normalized μ (LightTernaryColorPrelude.cv free n) n
      (ColorClassLists.classList color x 2 (-1)) C)
    (hx : ∀i,|x i|≤(U:ℤ)) : Metadata n U A B C := by
  have listBound (L : List ℤ) (h : ∀z∈L,|z|≤(U:ℤ)) (i : ℕ) (hi : i<L.length) : |L.getD i 0|≤(U:ℤ) := by
    rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  refine ⟨hA.length,hB.length,hC.length,?_,?_,?_,sorted_injective B hB.sorted,sorted_injective C hC.sorted⟩
  · apply listBound
    intro z hz
    have hh := (ColorClassLists.mem_classList color x 0 z).mp ((hA.mem z).mp hz)
    rw [Coloring.mem_values] at hh
    obtain ⟨i,hi,rfl⟩ := hh
    exact hx i
  · apply listBound
    intro z hz
    have hh := (ColorClassLists.mem_classList color x 1 z).mp ((hB.mem z).mp hz)
    rw [Coloring.mem_values] at hh
    obtain ⟨i,hi,rfl⟩ := hh
    exact hx i
  · apply listBound
    intro z hz
    have hh := (ColorClassLists.mem_negClassList color x z).mp ((hC.mem z).mp hz)
    rw [Coloring.mem_negValues] at hh
    obtain ⟨i,hi,rfl⟩ := hh
    simpa only [abs_neg] using hx i

variable {d c : ℕ} [Fact (Irreducible (TernaryComputedExtensionMenu.modulus p d c))]

/-- Positive actual color preparation supplies the entire original-input
prefix certificate for the exact finite field found by the global backend.
The coefficient reads are derived from its real menu, not supplied as advice. -/
theorem of_output {n free U R J backend radix C0 weightCap queryTime : ℕ}
    (hd : 0<d) (μ ν : ℕ→ℤ) (color : Coloring.Parameter (LightColorParametersCosts.width n))
    (x : Fin n→ℤ) (ret : ℤ)
    (H : LightTernaryColorPreparationProof.Output μ ν free U R J (p^d)
      (LightExtensionBackendLayout.physical backend d (p^d) J) radix color x ret)
    (hret : ret≠0) (hx : ∀i,|x i|≤(U:ℤ)) (hb : 1<radix) (hp : radix<p)
    (hbackend : backend+LightExtensionBackendLayout.reserve d p (p^d) J≤free)
    (hMenu : LightTernaryGlobalPreludeProof.Menu μ backend d p (p^d) J c) :
    ∃A B C : List ℤ,
      Metadata n U A B C ∧ A≠[] ∧ B≠[] ∧ C≠[] ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.av free n) n
        (ColorClassLists.classList color x 0 1) A ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.bv free n) n
        (ColorClassLists.classList color x 1 1) B ∧
      LightTernaryColorPrelude.Normalized ν (LightTernaryColorPrelude.cv free n) n
        (ColorClassLists.classList color x 2 (-1)) C ∧
      Seg ν (headerAt free n (LightColorParametersCosts.width n))
        (header free n U R J (p^d) (LightExtensionBackendLayout.physical backend d (p^d) J) A B C) ∧
      TernaryArenaPrefixInputs.Originals (input free n U J C0 weightCap queryTime A B C)
        (inputs free n J (LightExtensionBackendLayout.physical backend d (p^d) J) A B C)
        ((p^d)*(p^d)) radix radix n (TernaryComputedExtensionMenu.functional (p:=p) (c:=c) hd)
        (TernaryArenaFamilyBudget.seedAt (TernaryComputedExtensionMenu.seeds (p:=p) (d:=d) (c:=c)))
        (left U radix J (fun i => B.getD i 0)) (right U radix J (fun i => C.getD i 0))
        (requester U radix J (fun i => A.getD i 0)) ν := by
  obtain ⟨hkept,A,B,C,hA,hB,hC,hcase⟩ := H
  rcases hcase with hz|hpos
  · exact (hret hz.1).elim
  rcases hpos with ⟨hr,hneA,hneB,hneC,hheader,hmat⟩
  have hend : LightExtensionBackendLayout.physical backend d (p^d) J+(p^d)*(p^d)*(J+2)≤free := by
    have he := LightExtensionBackendLayout.end_le backend d p (p^d) J
    have hle : LightExtensionBackendLayout.physical backend d (p^d) J+(p^d)*(p^d)*(J+2)≤
        LightExtensionBackendLayout.sum backend d (p^d) J+2*d := by
      unfold LightExtensionBackendLayout.sum LightExtensionBackendLayout.prod LightExtensionBackendLayout.r
        LightExtensionBackendLayout.h LightExtensionBackendLayout.b LightExtensionBackendLayout.a
      omega
    exact hle.trans (he.trans hbackend)
  refine ⟨A,B,C,metadata color x A B C ν hA hB hC hx,hneA,hneB,hneC,hA,hB,hC,hheader,?_⟩
  apply of_matrices free n U J radix C0 weightCap queryTime _ _ A B C ν hmat hA.length hb hp
    (TernaryComputedExtensionMenu.functional (p:=p) (c:=c) hd)
    (TernaryArenaFamilyBudget.seedAt (TernaryComputedExtensionMenu.seeds (p:=p) (d:=d) (c:=c))) hend
  intro ordinal ho k hk
  have hx : LightExtensionBackendLayout.physical backend d (p^d) J+ordinal*(J+2)+k<free := by
    have hh := Nat.mul_le_mul_right (J+2) (show ordinal+1≤(p^d)*(p^d) by omega)
    nlinarith
  exact (hkept _ hx).trans (TernaryComputedExtensionMenu.coefficient_read hd μ hMenu ordinal ho k hk)

end ThreeSum.TernaryPreparedOriginals
