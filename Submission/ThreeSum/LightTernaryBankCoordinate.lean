import Submission.ThreeSum.TernaryBankStageModel

/-! One actual compact bank coordinate: construct metadata, then execute its pass. -/
namespace ThreeSum.LightTernaryBankCoordinate
open Light ThreeSum.LightSubsetAddress ThreeSum.TernaryJointType ThreeSum.TernaryBankStageModel
open ThreeSum.TernaryCodeSemantics ThreeSum.TernaryQuery
set_option maxHeartbeats 5000000
variable {lim : Limits} {P : Program}

def body (pMeta pPass : ℕ) : Stmt :=
  .call pMeta [k 2 *' v 0,v 1,v 2,v 3,v 4,v 5,v 7] 10 ;;
  .call pPass [v 3,v 4,v 5,v 6,v 7,v 8,v 9] 0

def time (N L n : ℕ) : ℕ :=LightTernaryMetadata.time (2*N) n+LightTernaryPass.time L n+100

def Preserved (μ μ' : ℕ→ℤ) (keyBase n dst : ℕ) : Prop :=
  ∀ x, (x<keyBase ∨ keyBase+4*n≤x) → (x<dst ∨ dst+n≤x) → μ' x=μ x

theorem zeta_meets {N T n pMain pMeta pZero pDigit pErase pPass pCell pSearch pValue
    a powers L keyBase src dst d U : ℕ}
    (hmain : P[pMain]?=some (body pMeta pPass))
    (hmetaProg : P[pMeta]?=some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hpass : P[pPass]?=some (LightTernaryPass.body pCell))
    (hcell : P[pCell]?=some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]?=some LightTernaryCell.zetaBody)
    (E : Enumeration N T n) (i : Fin N) (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤src) (hsrc : src+n≤dst) (hdst : dst+n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (src+j)=F (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ j<n, |F (E.word j)|≤(U : ℤ)) (hvalword : 4*(U : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+4≤lim.depth) :
    Meets lim P pMain d [N,low i,high i,a,n,powers,L,keyBase,src,dst] μ (time N L n)
      (fun _ μ' => (∀ j<n, μ' (dst+j)=coordinateZeta i F (E.word j)) ∧ Preserved μ μ' keyBase n dst) := by
  have hwordPow : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word := by
    exact (Int.ofNat_le.mpr (show 2^(2*N+1)≤n+2^(2*N+1)+16 by omega)).trans hword
  have hlow : low i≤2*N := Nat.le_of_lt (low_lt i)
  have hhigh : high i≤2*N := Nat.le_of_lt (high_lt i)
  have hc := LightTernaryMetadata.meets (d := d+1) hmetaProg hzero hdigit herase μ
    (fun j => address (E.word j)) hw ha hmeta (by omega) hwordPow hcodes hpowers
    (fun j _ => address_lt_pow_two _) hlow hhigh (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hc using LightTernaryMetadata.time with r μm ⟨hrows,hkeep⟩
  have hcm : ∀ j<n, μm (a+j)=(address (E.word j) : ℤ) := by
    intro j hj
    exact (hkeep _ (Or.inl (by omega))).trans (hcodes j hj)
  have hsm : ∀ j<n, μm (src+j)=F (E.word j) := by
    intro j hj
    exact (hkeep _ (Or.inr (by omega))).trans (hsource j hj)
  have hpm : Powers μm powers (2*N) := by
    intro j hj
    exact (hkeep _ (Or.inr (by omega))).trans (hpowers j hj)
  have hsort : ∀ j k, j<k → k<n → (address (E.word j) : ℤ)<(address (E.word k) : ℤ) := by
    intro j k hj hk
    exact_mod_cast hsorted j k hj hk
  have hmd : ∀ j<n, μm (keyBase+j)=((E.word j i).val : ℤ) := by
    intro j hj
    simpa only [digit_eq] using (hrows j hj).1
  have hm0 : ∀ j<n, μm (keyBase+n+j)=(address (E.word (index E i 0 j)) : ℤ) := by
    intro j hj
    rw [index_zero_code E i j hj]
    exact (hrows j hj).2.1
  have hm1 : ∀ j<n, μm (keyBase+2*n+j)=(address (E.word (index E i 1 j)) : ℤ) := by
    intro j hj
    rw [index_one_code E i j hj]
    exact (hrows j hj).2.2.1
  have hm2 : ∀ j<n, μm (keyBase+3*n+j)=(address (E.word (index E i 2 j)) : ℤ) := by
    intro j hj
    rw [index_two_code E i j hj]
    exact (hrows j hj).2.2.2
  have hp := LightTernaryPass.meets (d := d+1) hpass hcell hsearch hvalue μm
    (fun j => (address (E.word j) : ℤ)) (fun j => F (E.word j))
    (fun j => E.word j i) (index E i) hw (by omega) hsrc (by omega) (by omega) hdst
    hword hcm hsm hpm hsort (fun e j hj => (index_spec E i e j hj).1)
    hmd hm0 hm1 hm2 hF hvalword hL hn (by omega)
  light_call hp using LightTernaryPass.time,LightTernaryMetadata.time with r' μ' ⟨hout,hpassKeep⟩
  dsimp only
  refine ⟨?_,?_⟩
  · intro j hj
    rw [hout j hj]
    exact LightTernaryPass.values_eq_coordinateZeta E.word i (fun j => E.word j i)
      (index E i) F j rfl (fun e he => index_update E i e j hj he)
  · intro x hxMeta hxDst
    exact (hpassKeep x hxDst).trans (hkeep x hxMeta)

theorem inverse_meets {N T n pMain pMeta pZero pDigit pErase pPass pCell pSearch pValue
    a powers L keyBase src dst d U : ℕ}
    (hmain : P[pMain]?=some (body pMeta pPass))
    (hmetaProg : P[pMeta]?=some (LightTernaryMetadata.body pZero pDigit pErase))
    (hzero : P[pZero]?=some (LightTernaryCodes.zeroBody pErase))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (hpass : P[pPass]?=some (LightTernaryInversePass.body pCell))
    (hcell : P[pCell]?=some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]?=some LightTernaryCell.inverseBody)
    (E : Enumeration N T n) (i : Fin N) (F : TritWord N→ℤ) (μ : ℕ→ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+n≤keyBase) (hmeta : keyBase+4*n≤powers)
    (hpows : powers+(2*N+1)≤src) (hsrc : src+n≤dst) (hdst : dst+n≤lim.space)
    (hword : ((n+2^(2*N+1)+16 : ℕ) : ℤ)≤lim.word)
    (hNword : 2*(N : ℤ)+3≤lim.word)
    (hcodes : ∀ j<n, μ (a+j)=(address (E.word j) : ℤ))
    (hsource : ∀ j<n, μ (src+j)=F (E.word j))
    (hpowers : Powers μ powers (2*N))
    (hsorted : ∀ j k, j<k → k<n → address (E.word j)<address (E.word k))
    (hF : ∀ j<n, |F (E.word j)|≤(U : ℤ)) (hvalword : 4*(U : ℤ)+3≤lim.word)
    (hL : L≤2*N) (hn : n<2^L) (hd : d+2*N+L+4≤lim.depth) :
    Meets lim P pMain d [N,low i,high i,a,n,powers,L,keyBase,src,dst] μ (time N L n)
      (fun _ μ' => (∀ j<n, μ' (dst+j)=coordinateInverse i F (E.word j)) ∧ Preserved μ μ' keyBase n dst) := by
  have hwordPow : ((2^(2*N+1) : ℕ) : ℤ)≤lim.word := by
    exact (Int.ofNat_le.mpr (show 2^(2*N+1)≤n+2^(2*N+1)+16 by omega)).trans hword
  have hlow : low i≤2*N := Nat.le_of_lt (low_lt i)
  have hhigh : high i≤2*N := Nat.le_of_lt (high_lt i)
  have hc := LightTernaryMetadata.meets (d := d+1) hmetaProg hzero hdigit herase μ
    (fun j => address (E.word j)) hw ha hmeta (by omega) hwordPow hcodes hpowers
    (fun j _ => address_lt_pow_two _) hlow hhigh (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hc using LightTernaryMetadata.time with r μm ⟨hrows,hkeep⟩
  have hcm : ∀ j<n, μm (a+j)=(address (E.word j) : ℤ) := by
    intro j hj
    exact (hkeep _ (Or.inl (by omega))).trans (hcodes j hj)
  have hsm : ∀ j<n, μm (src+j)=F (E.word j) := by
    intro j hj
    exact (hkeep _ (Or.inr (by omega))).trans (hsource j hj)
  have hpm : Powers μm powers (2*N) := by
    intro j hj
    exact (hkeep _ (Or.inr (by omega))).trans (hpowers j hj)
  have hsort : ∀ j k, j<k → k<n → (address (E.word j) : ℤ)<(address (E.word k) : ℤ) := by
    intro j k hj hk
    exact_mod_cast hsorted j k hj hk
  have hmd : ∀ j<n, μm (keyBase+j)=((E.word j i).val : ℤ) := by
    intro j hj
    simpa only [digit_eq] using (hrows j hj).1
  have hm0 : ∀ j<n, μm (keyBase+n+j)=(address (E.word (index E i 0 j)) : ℤ) := by
    intro j hj
    rw [index_zero_code E i j hj]
    exact (hrows j hj).2.1
  have hm1 : ∀ j<n, μm (keyBase+2*n+j)=(address (E.word (index E i 1 j)) : ℤ) := by
    intro j hj
    rw [index_one_code E i j hj]
    exact (hrows j hj).2.2.1
  have hm2 : ∀ j<n, μm (keyBase+3*n+j)=(address (E.word (index E i 2 j)) : ℤ) := by
    intro j hj
    rw [index_two_code E i j hj]
    exact (hrows j hj).2.2.2
  have hp := LightTernaryInversePass.meets (d := d+1) hpass hcell hsearch hvalue μm
    (fun j => (address (E.word j) : ℤ)) (fun j => F (E.word j))
    (fun j => E.word j i) (index E i) hw (by omega) hsrc (by omega) (by omega) hdst
    hword hcm hsm hpm hsort (fun e j hj => (index_spec E i e j hj).1)
    hmd hm0 hm1 hm2 hF hvalword hL hn (by omega)
  light_call hp using LightTernaryPass.time,LightTernaryInversePass.time,LightTernaryMetadata.time with r' μ' ⟨hout,hpassKeep⟩
  dsimp only
  refine ⟨?_,?_⟩
  · intro j hj
    rw [hout j hj]
    exact LightTernaryInversePass.values_eq_coordinateInverse E.word i (fun j => E.word j i)
      (index E i) F j rfl (fun e he => index_update E i e j hj he)
  · intro x hxMeta hxDst
    exact (hpassKeep x hxDst).trans (hkeep x hxMeta)

end ThreeSum.LightTernaryBankCoordinate
