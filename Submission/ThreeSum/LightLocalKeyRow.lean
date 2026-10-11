import Submission.ThreeSum.LightMaskHashes
import Submission.ThreeSum.LightArray

/-!
# Computing one complete row of signed local output keys

For every stored output mask, this fixed program sums the true and false
coefficients outside that mask and subtracts the two sums. It constructs
its own zero row and powers table. Both input coefficient rows and the
literal output-mask enumeration remain intact.
-/

namespace ThreeSum.LightLocalKeyRow

open Light LightSubsetAddress

set_option maxHeartbeats 2400000
set_option maxRecDepth 10000

/-- Width, masks, mask count, false coefficients, true coefficients, free. -/
def body (pFill pHashes pLinear : ℕ) : Stmt :=
  .set 6 (v 5 +' v 0) ;;
  .set 7 (v 6 +' v 2) ;;
  .set 8 (v 7 +' v 2) ;;
  .call pFill [v 5,v 0,k 0] 9 ;;
  .call pHashes [v 0,v 1,v 6,v 2,v 4,v 5,v 8] 9 ;;
  .call pHashes [v 0,v 1,v 7,v 2,v 3,v 5,v 8] 9 ;;
  .call pLinear [v 6,v 7,v 6,v 2,k 0 -' k 1] 9 ;;
  .set 0 (v 6)

def time (L n : ℕ) : ℕ := fillTime L+2*LightMaskHashes.time L n+LightArray.linearTime n+300
def space (free L n : ℕ) : ℕ := free+L+2*n+(L+1)
def word (L U : ℕ) : ℕ := 2*LightOneHot.word L U+2

structure Procs (P : Program) (pMain : ℕ) where
  pFill : ℕ
  pHashes : ℕ
  pPowers : ℕ
  pHash : ℕ
  pLinear : ℕ
  main : P[pMain]? = some (body pFill pHashes pLinear)
  fill : P[pFill]? = some fillBody
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pHash)
  powers : P[pPowers]? = some powTableBody
  hash : P[pHash]? = some (LightOneHot.body pHash)
  linear : P[pLinear]? = some LightArray.linearBody

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L masks n srcFalse srcTrue free U : ℕ}
    (mask wFalse wTrue : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+L+2 ≤ lim.depth)
    (hspace : space free L n ≤ lim.space)
    (hmasks : masks+n ≤ free) (hfalse : srcFalse+L ≤ free) (htrue : srcTrue+L ≤ free)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^L)
    (hreadFalse : ∀ i < L, μ (srcFalse+i) = (wFalse i : ℤ))
    (hreadTrue : ∀ i < L, μ (srcTrue+i) = (wTrue i : ℤ))
    (hboundFalse : ∀ i < L, wFalse i ≤ U) (hboundTrue : ∀ i < L, wTrue i ≤ U) :
    Meets lim P pMain d [L,masks,n,srcFalse,srcTrue,free] μ (time L n)
      (fun r ν => r=((free+L : ℕ) : ℤ) ∧
        (∀ i < n, ν (free+L+i) =
          (OneHotMask.eval wTrue (fun _ => 0) L (mask i) : ℤ)-
          (OneHotMask.eval wFalse (fun _ => 0) L (mask i) : ℤ)) ∧ Kept μ ν free) := by
  let dst := free+L
  let tmp := dst+n
  let work := tmp+n
  have hs : work+(L+1) ≤ lim.space := by dsimp [work,tmp,dst]; unfold space at hspace; omega
  have hhashWord : (LightOneHot.word L U : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (show LightOneHot.word L U ≤ word L U by unfold word; omega)).trans hword
  have hv : 2*((L*U : ℕ) : ℤ) ≤ lim.word := by
    have hu : L*U ≤ LightOneHot.word L U :=
      (Nat.mul_le_mul_right U (Nat.le_succ L)).trans (Nat.le_add_left _ _)
    have hn : 2*(L*U) ≤ word L U :=
      (Nat.mul_le_mul_left 2 hu).trans (Nat.le_add_right _ _)
    exact (by exact_mod_cast hn : 2*((L*U : ℕ) : ℤ) ≤ (word L U : ℤ)).trans hword
  have hzero : ∀ i < L, (0 : ℕ) ≤ U := by simp
  apply Meets.of_body S.main
  unfold body time
  light_set (dst : ℕ)
  light_set (tmp : ℕ)
  light_set (work : ℕ)
  have hf := fill_meets (d := d+1) (μ := μ) (dst := free) (n := L) (x := 0) S.fill hw (by omega)
  light_call hf using LightMaskHashes.time,LightArray.linearTime with r₁ μ₁ ⟨hfilled,hkeep₁⟩
  have hz₁ (i : ℕ) (hi : i < L) : μ₁ (free+i)=(0 : ℤ) := by
    exact (hfilled i (by simpa using hi)).trans (List.getElem_replicate ..)
  have hm₁ (i : ℕ) (hi : i < n) : μ₁ (masks+i)=(mask i : ℤ) :=
    (hkeep₁ _ (Or.inl (by omega))).trans (hmaskRead i hi)
  have ht₁ (i : ℕ) (hi : i < L) : μ₁ (srcTrue+i)=(wTrue i : ℤ) :=
    (hkeep₁ _ (Or.inl (by omega))).trans (hreadTrue i hi)
  have hfirst := LightMaskHashes.meets (d := d+1) (μ := μ₁) (L := L) (masks := masks)
    (dst := dst) (n := n) (src0 := srcTrue) (src1 := free) (work := work) (U := U)
    S.hashes S.powers S.hash mask wTrue (fun _ => 0) hw (by omega) hs
    (by dsimp [dst]; omega) (by dsimp [dst]; omega) le_rfl (by dsimp [work,tmp]; omega)
    hhashWord hm₁ hmaskLt ht₁ hz₁ hboundTrue hzero
  light_call hfirst using LightMaskHashes.time,LightArray.linearTime with r₂ μ₂ ⟨hvaluesTrue,hpow₂,hkeep₂⟩
  have hm₂ (i : ℕ) (hi : i < n) : μ₂ (masks+i)=(mask i : ℤ) :=
    (hkeep₂ _ ⟨by dsimp [work,tmp,dst]; omega,Or.inl (by dsimp [dst]; omega)⟩).trans (hm₁ i hi)
  have hf₂ (i : ℕ) (hi : i < L) : μ₂ (srcFalse+i)=(wFalse i : ℤ) := by
    rw [hkeep₂ _ ⟨by dsimp [work,tmp,dst]; omega,Or.inl (by dsimp [dst]; omega)⟩,
      hkeep₁ _ (Or.inl (by omega))]
    exact hreadFalse i hi
  have hz₂ (i : ℕ) (hi : i < L) : μ₂ (free+i)=(0 : ℤ) :=
    (hkeep₂ _ ⟨by dsimp [work,tmp,dst]; omega,Or.inl (by dsimp [dst]; omega)⟩).trans (hz₁ i hi)
  have hsecond := LightMaskHashes.meets (d := d+1) (μ := μ₂) (L := L) (masks := masks)
    (dst := tmp) (n := n) (src0 := srcFalse) (src1 := free) (work := work) (U := U)
    S.hashes S.powers S.hash mask wFalse (fun _ => 0) hw (by omega) hs
    (by dsimp [tmp,dst]; omega) (by dsimp [tmp,dst]; omega)
    (by dsimp [tmp,dst]; omega) le_rfl hhashWord hm₂ hmaskLt hf₂ hz₂ hboundFalse hzero
  light_call hsecond using LightMaskHashes.time,LightArray.linearTime with r₃ μ₃ ⟨hvaluesFalse,hpow₃,hkeep₃⟩
  have ht₃ (i : ℕ) (hi : i < n) :
      μ₃ (dst+i)=(OneHotMask.eval wTrue (fun _ => 0) L (mask i) : ℤ) :=
    (hkeep₃ _ ⟨by dsimp [work,tmp]; omega,Or.inl (by dsimp [tmp]; omega)⟩).trans (hvaluesTrue i hi)
  have hvalues : ∀ i < n, |μ₃ (dst+i)| ≤ ((L*U : ℕ) : ℤ) ∧
      |μ₃ (tmp+i)| ≤ ((L*U : ℕ) : ℤ) := by
    intro i hi
    rw [ht₃ i hi,hvaluesFalse i hi]
    simp only [Int.abs_natCast]
    exact ⟨Int.ofNat_le.mpr (OneHotMask.eval_le hboundTrue hzero),
      Int.ofNat_le.mpr (OneHotMask.eval_le hboundFalse hzero)⟩
  have hl := LightArray.linear_bounded_meets (d := d+1) (μ := μ₃)
    (srcA := dst) (srcB := tmp) (dst := dst) (n := n) (U := L*U) (c := -1)
    S.linear hw (by omega) (by omega) (by omega) (Or.inl rfl)
    (Or.inr (Or.inr (by dsimp [tmp]; omega))) (by norm_num) hv hvalues
  light_call hl using LightMaskHashes.time,LightArray.linearTime with r₄ μ₄ ⟨hout,hkeep₄⟩
  light_set (dst : ℕ) using LightMaskHashes.time,LightArray.linearTime
  refine ⟨by simp [dst],?_,?_⟩
  · intro i hi
    change μ₄ (dst+i)=_
    rw [hout i hi,ht₃ i hi,hvaluesFalse i hi]
    ring
  · intro a ha
    change μ₄ a=μ a
    rw [hkeep₄ _ (Or.inl (by dsimp [dst]; omega)),
      hkeep₃ _ ⟨by dsimp [work,tmp,dst]; omega,Or.inl (by dsimp [tmp,dst]; omega)⟩,
      hkeep₂ _ ⟨by dsimp [work,tmp,dst]; omega,Or.inl (by dsimp [dst]; omega)⟩,
      hkeep₁ _ (Or.inl ha)]

def program : Program := [body 1 2 5,fillBody,LightMaskHashes.body 3 4,
  powTableBody,LightOneHot.body 4,LightArray.linearBody]

def programProcs : Procs program 0 := ⟨1,2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem time_bound (L n : ℕ) : time L n ≤ 950*(L+1)*(n+1) := by
  have h := LightMaskHashes.time_bound L n
  unfold time fillTime LightArray.linearTime
  nlinarith

end ThreeSum.LightLocalKeyRow
