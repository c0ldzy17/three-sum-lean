import Submission.ThreeSum.LightHistogram

/-!
# Signed source weights, retaining original join records

The compact key array is accompanied by the actual interleaved join records.
For each record the machine reads its original position, loads the original
source weight, and adds it to the corresponding compact histogram cell.
-/

namespace ThreeSum.LightTernaryWeightedHistogram

open Light Finset
open scoped BigOperators

set_option maxHeartbeats 2000000

def total (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n : ℕ) : ℤ :=
  ∑ i ∈ range n, if key i=r then weight i else 0

@[simp] theorem total_zero (key : ℕ → ℕ) (weight : ℕ → ℤ) (r : ℕ) :
    total key weight r 0=0 := by simp [total]

theorem total_succ (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n : ℕ) :
    total key weight r (n+1)=total key weight r n+
      if key n=r then weight n else 0 := by
  unfold total
  rw [sum_range_succ]

theorem total_abs_le (key : ℕ → ℕ) (weight : ℕ → ℤ) (r n U : ℕ)
    (h : ∀ i < n, |weight i| ≤ U) : |total key weight r n| ≤ (n : ℤ)*U := by
  unfold total
  calc
    _ ≤ ∑ i ∈ range n, |if key i=r then weight i else 0| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range n, (U : ℤ) := by
      apply sum_le_sum
      intro i hi
      split_ifs
      · exact h i (mem_range.mp hi)
      · simp
    _ = (n : ℤ)*U := by simp

variable {lim : Limits} {P : Program} {d : ℕ}

def countBody : Stmt := .for 7 (v 3)
  (.store (v 4 +' M (v 0 +' v 7))
    (M (v 4 +' M (v 0 +' v 7)) +' M (v 2 +' M (v 1 +' k 2 *' v 7))))

def countTime (n : ℕ) : ℕ := 40*n+10

theorem count_ends {μ : ℕ → ℤ} {loc : ℕ → ℤ}
    {keys pairs source n dst bank sourceCount U : ℕ}
    (key position : ℕ → ℕ) (weight : ℕ → ℤ)
    (hloc : loc 0=keys ∧ loc 1=pairs ∧ loc 2=source ∧ loc 3=n ∧ loc 4=dst)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeys : keys+n ≤ dst) (hpairs : pairs+2*n ≤ dst)
    (hsource : source+sourceCount ≤ dst) (hdst : dst+bank ≤ lim.space)
    (hkeyRead : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hposRead : ∀ i < n, μ (pairs+2*i) = (position i : ℤ))
    (hsourceRead : ∀ i < n, μ (source+position i) = weight i)
    (hkeyLt : ∀ i < n, key i < bank) (hposLt : ∀ i < n, position i < sourceCount)
    (hzero : ∀ r < bank, μ (dst+r)=0)
    (hweights : ∀ i < n, |weight i| ≤ U)
    (hword : ((n+1 : ℕ) : ℤ)*U ≤ lim.word) :
    Ends lim P d countBody ⟨loc,μ⟩ (countTime n) (fun σ' =>
      (∀ r < bank, σ'.mem (dst+r)=total key weight r n) ∧
        SameOutside μ σ'.mem dst bank) := by
  rcases hloc with ⟨hl0,hl1,hl2,hl3,hl4⟩
  let Inv := fun i (ν : ℕ → ℤ) =>
    (∀ r < bank, ν (dst+r)=total key weight r i) ∧ SameOutside μ ν dst bank
  unfold countBody
  apply Ends.forMem Inv n 30 (hn := by omega) (hT := by unfold countTime; light_time)
  · exact ⟨by simpa only [total_zero] using hzero,fun _ _ => rfl⟩
  · intro i ν hi hI
    rcases hI with ⟨hcounts,hkeep⟩
    have hkeyi := hkeyLt i hi
    have hposi := hposLt i hi
    have hkread : ν (keys+i)=(key i : ℤ) :=
      (hkeep _ (Or.inl (by omega))).trans (hkeyRead i hi)
    have hpread : ν (pairs+2*i)=(position i : ℤ) :=
      (hkeep _ (Or.inl (by omega))).trans (hposRead i hi)
    have hsread : ν (source+position i)=weight i :=
      (hkeep _ (Or.inl (by omega))).trans (hsourceRead i hi)
    have hcell := hcounts (key i) hkeyi
    have hsum := total_abs_le key weight (key i) i U (fun j hj => hweights j (by omega))
    have hwi := hweights i hi
    have hval : |total key weight (key i) i+weight i| ≤ lim.word := by
      have hh : |total key weight (key i) i+weight i| ≤ (i : ℤ)*U+U :=
        (abs_add_le _ _).trans (add_le_add hsum hwi)
      have hnword : (i : ℤ)*U+U ≤ ((n+1 : ℕ) : ℤ)*U := by
        have hii : (i : ℤ)+1 ≤ ((n+1 : ℕ) : ℤ) := by omega
        nlinarith [Int.natCast_nonneg U]
      exact hh.trans (hnword.trans hword)
    have hvalbounds := abs_le.mp hval
    have hwiWord : |weight i| ≤ lim.word := by
      have hU : (U : ℤ) ≤ ((n+1 : ℕ) : ℤ)*U := by
        have hh := mul_le_mul_of_nonneg_right
          (show (1 : ℤ) ≤ ((n+1 : ℕ) : ℤ) by omega) (Int.natCast_nonneg U)
        simpa using hh
      exact hwi.trans (hU.trans hword)
    have hwiBounds := abs_le.mp hwiWord
    have hpairAddr : ((pairs : ℤ)+2*(i : ℤ)).toNat=pairs+2*i := by norm_cast
    have hsourceAddr : ((source : ℤ)+(position i : ℤ)).toNat=source+position i := by norm_cast
    have hkeyAddr : ((dst : ℤ)+(key i : ℤ)).toNat=dst+key i := by norm_cast
    have ha : (v 4 +' M (v 0 +' v 7)).val ⟨Function.update loc 7 (i : ℤ),ν⟩ =
        ((dst+key i : ℕ) : ℤ) := by
      simp [Expr.val,v,k,M,hl0,hl4,hkread]
    have hv : (M (v 4 +' M (v 0 +' v 7)) +' M (v 2 +' M (v 1 +' k 2 *' v 7))).val
        ⟨Function.update loc 7 (i : ℤ),ν⟩ = total key weight (key i) i+weight i := by
      simp [Expr.val,v,k,M,hl0,hl1,hl2,hl4,hkread,hpread,hsread,hcell,
        hpairAddr,hsourceAddr,hkeyAddr]
    refine Ends.storeLast ?_
      (by light_side [hl0,hl1,hl2,hl4,hkread,hpread,hsread,hcell,
        hpairAddr,hsourceAddr,hkeyAddr,ha,hv]) (by light_time)
    change Function.update loc 7 (i : ℤ)=Function.update loc 7 (i : ℤ) ∧
      Inv (i+1) (Function.update ν
        ((v 4 +' M (v 0 +' v 7)).val ⟨Function.update loc 7 (i : ℤ),ν⟩).toNat
        ((M (v 4 +' M (v 0 +' v 7)) +' M (v 2 +' M (v 1 +' k 2 *' v 7))).val
          ⟨Function.update loc 7 (i : ℤ),ν⟩))
    rw [ha,hv,Int.toNat_natCast]
    refine ⟨rfl,?_,?_⟩
    · intro r hr
      rw [total_succ]
      by_cases he : key i=r
      · subst r
        simp
      · rw [Function.update_of_ne (by omega),hcounts r hr]
        simp [he]
    · intro a hx
      rw [Function.update_of_ne (by omega)]
      exact hkeep a hx
  · intro ν hI
    exact hI
  · intro i ν hi hI
    simp [hl3]

def body (pFill : ℕ) : Stmt := .call pFill [v 4,v 5,k 0] 8 ;; countBody

def time (n bank : ℕ) : ℕ := fillTime bank+countTime n+50

theorem meets {pMain pFill keys pairs source n dst bank sourceCount U : ℕ}
    (hmain : P[pMain]?=some (body pFill)) (hfill : P[pFill]?=some fillBody)
    (μ : ℕ → ℤ) (key position : ℕ → ℕ) (weight : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hkeys : keys+n ≤ dst) (hpairs : pairs+2*n ≤ dst)
    (hsource : source+sourceCount ≤ dst) (hdst : dst+bank ≤ lim.space)
    (hkeyRead : ∀ i < n, μ (keys+i) = (key i : ℤ))
    (hposRead : ∀ i < n, μ (pairs+2*i) = (position i : ℤ))
    (hsourceRead : ∀ i < n, μ (source+position i) = weight i)
    (hkeyLt : ∀ i < n, key i < bank) (hposLt : ∀ i < n, position i < sourceCount)
    (hweights : ∀ i < n, |weight i| ≤ U)
    (hword : ((n+1 : ℕ) : ℤ)*U ≤ lim.word) :
    Meets lim P pMain d [keys,pairs,source,n,dst,bank,sourceCount] μ (time n bank)
      (fun _ ν => (∀ r < bank, ν (dst+r)=total key weight r n) ∧
        SameOutside μ ν dst bank) := by
  apply Meets.of_body hmain
  unfold body time
  light_call (fill_meets hfill (μ := μ) (x := 0) hw hdst) with res μ₁ ⟨hfilled,hkeep⟩
  have hk : ∀ i < n, μ₁ (keys+i)=(key i : ℤ) := by
    intro i hi
    exact (hkeep _ (Or.inl (by omega))).trans (hkeyRead i hi)
  have hp : ∀ i < n, μ₁ (pairs+2*i)=(position i : ℤ) := by
    intro i hi
    exact (hkeep _ (Or.inl (by omega))).trans (hposRead i hi)
  have hs : ∀ i < n, μ₁ (source+position i)=weight i := by
    intro i hi
    exact (hkeep _ (Or.inl (by have hh := hposLt i hi; omega))).trans (hsourceRead i hi)
  have hz : ∀ r < bank, μ₁ (dst+r)=0 := by
    intro r hr
    exact (hfilled r (by simpa using hr)).trans (List.getElem_replicate ..)
  apply Ends.pieceLast (count_ends key position weight (by simp) hw hkeys hpairs
    hsource hdst hk hp hs hkeyLt hposLt hz hweights hword)
  · intro σ' hpost
    exact ⟨hpost.1,fun a ha => (hpost.2 a ha).trans (hkeep a ha)⟩

def program : Program := [body 1,fillBody]

theorem time_bound (n bank : ℕ) : time n bank ≤ 100*(n+bank+1) := by
  unfold time countTime fillTime
  omega

end ThreeSum.LightTernaryWeightedHistogram
