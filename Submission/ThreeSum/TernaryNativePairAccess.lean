import Submission.ThreeSum.TernaryCanonicalNativeCompleteness
import Submission.ThreeSum.TernaryCompactPairedSupport

noncomputable section
namespace ThreeSum.TernaryNativePairAccess
open Finset TernaryJointType TernaryNativePairMoments TernarySourceHostModel
set_option maxHeartbeats 2000000

@[simp] theorem mem_pair {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (i b c j k : ℕ) : ((b,j),(c,k))∈pairs S i ↔
      (b,j)∈S.left.records ∧ S.left.group j=S.front.group i ∧
      (c,k)∈S.right.records ∧ S.right.group k=S.front.group i ∧
      TernaryConvolution.Adds (S.front.E.word (S.left.key j))
        (S.front.E.word (S.right.key k)) (S.front.Q i) := by
  classical
  unfold pairs TernaryPhysicalTensorChannels.records leftSet rightSet channel leftWord rightWord
  simp only [Finset.mem_filter,Finset.mem_product,Prod.fst,Prod.snd]
  tauto

/-- The physical pair type always refers to valid original source positions. -/
theorem sound {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (A B C : ℕ→ℤ) (position : ℕ→ℕ) (nA : ℕ)
    (hpos : ∀ i<S.front.count, position i<nA) :
    (∃ i<S.front.count, ∃ p : Pair S i, mode B C p=A (position i)) →
    ∃ i<nA, ∃ j<S.left.NL, ∃ k<S.right.NL, C k=A i+B j := by
  rintro ⟨i,hi,p,hp⟩
  refine ⟨position i,hpos i hi,p.val.1.1,
    TernaryCompactPairedSupport.native_left_lt p,p.val.2.1,
    TernaryCompactPairedSupport.native_right_lt p,?_⟩
  unfold mode at hp
  omega

/-- Equal dictionary keys and exact address/group lookups produce a literal
physical pair. Both source records retain their original position IDs. -/
theorem exists_pair {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (i b c j k : ℕ) (W V : TritWord N)
    (hb : b<S.left.NL) (hc : c<S.right.NL)
    (hj : j<LightTernarySourceHost.size S.left.xs S.left.J)
    (hk : k<LightTernarySourceHost.size S.right.xs S.right.J)
    (hL : S.left.input b=LightTernarySourceHost.dictionary S.left.xs S.left.p0 S.left.J j)
    (hR : S.right.input c=LightTernarySourceHost.dictionary S.right.xs S.right.p0 S.right.J k)
    (hGL : S.left.group j=S.front.group i) (hGR : S.right.group k=S.front.group i)
    (hWL : TernaryCodeSemantics.address (S.front.E.word (S.left.key j))=
      TernaryCodeSemantics.address W)
    (hWR : TernaryCodeSemantics.address (S.front.E.word (S.right.key k))=
      TernaryCodeSemantics.address V)
    (hadd : TernaryConvolution.Adds W V (S.front.Q i)) :
    ∃ p : Pair S i, p.val.1.1=b ∧ p.val.2.1=c := by
  have hwordL := TernaryCodeSemantics.address_injective N hWL
  have hwordR := TernaryCodeSemantics.address_injective N hWR
  have hleft : (b,j)∈S.left.records := by
    apply (mem_records _ _ _ _ _ _).mpr
    exact ⟨hb,hj,by rw [hL,sub_self]; exact dvd_zero _⟩
  have hright : (c,k)∈S.right.records := by
    apply (mem_records _ _ _ _ _ _).mpr
    exact ⟨hc,hk,by rw [hR,sub_self]; exact dvd_zero _⟩
  have hp : ((b,j),(c,k))∈pairs S i := (mem_pair S i b c j k).mpr
    ⟨hleft,hGL,hright,hGR,by rw [hwordL,hwordR]; exact hadd⟩
  exact ⟨⟨((b,j),(c,k)),hp⟩,rfl,rfl⟩

end ThreeSum.TernaryNativePairAccess
