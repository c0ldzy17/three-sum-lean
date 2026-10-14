import Submission.ThreeSum.LightTernaryLookup

/-!
# Actual frozen-query table leaves

The same procedure loads a suffix inverse-stage value from a bank (stage
argument positive or zero), or the original product from the near-word memo
(stage zero). The compact code ordinal is computed by the actual checked
binary search before the memory read.
-/

namespace ThreeSum.LightTernaryQueryLookup

open Light ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments: sorted code base/count, requested code, value-table base,
powers base, lookup width, remaining inverse stage. -/
def body (pSearch : ℕ) : Stmt :=
  .call pSearch [v 0,v 1,v 2,v 4,v 5,k 0] 7 ;;
  .set 0 (M (v 3 +' v 6 *' v 1 +' v 7 -' k 1))

def time (L : ℕ) : ℕ := LightBandLookup.searchTime L + 100

theorem meets {pMain pSearch a n powers W L src stage j d U : ℕ}
    (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes : ℕ → ℤ) (value : ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hsrc : src+(stage+1)*n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = codes i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k)
    (hj : j < n) (hvalue : μ (src+stage*n+j) = value)
    (hval : |value| ≤ U) (hU : (U : ℤ) ≤ lim.word)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,n,codes j,src,powers,L,stage] μ (time L)
      (fun r μ' => r = value ∧ μ' = μ) := by
  have hc := LightTernaryLookup.code_meets (d := d+1) hsearch μ codes hw
    ha hspace hword hread hpowers hsorted hj hL hn (by omega)
  have haddr : (src : ℤ)+(stage : ℤ)*(n : ℤ)+((j+1 : ℕ) : ℤ)-1 =
      ((src+stage*n+j : ℕ) : ℤ) := by push_cast; ring
  have haddrNat : ((src : ℤ)+(stage : ℤ)*(n : ℤ)+((j+1 : ℕ) : ℤ)-1).toNat =
      src+stage*n+j := by rw [haddr,Int.toNat_natCast]
  have haddrNat' : ((src : ℤ)+(stage : ℤ)*(n : ℤ)+((j+1 : ℕ) : ℤ)).toNat-1 =
      src+stage*n+j := by
    have hp : (src : ℤ)+(stage : ℤ)*(n : ℤ)+((j+1 : ℕ) : ℤ) =
        ((src+stage*n+j+1 : ℕ) : ℤ) := by push_cast; ring
    rw [hp,Int.toNat_natCast]
    omega
  have haddrNat'' : ((src : ℤ)+(stage : ℤ)*(n : ℤ)+((j : ℤ)+1)).toNat-1 =
      src+stage*n+j := by
    simpa only [Nat.cast_add,Nat.cast_one] using haddrNat'
  have hvalue' : μ (((src : ℤ)+(stage : ℤ)*(n : ℤ)+((j : ℤ)+1)).toNat-1) = value := by
    rw [haddrNat'']
    exact hvalue
  have hbounds := abs_le.mp (hval.trans hU)
  have hmul : stage*n ≤ (stage+1)*n := Nat.mul_le_mul_right n (Nat.le_succ stage)
  have hmulWord : (stage : ℤ)*(n : ℤ) ≤ lim.word := by
    have hh : stage*n ≤ lim.space := by omega
    exact (show (stage : ℤ)*(n : ℤ) ≤ (lim.space : ℤ) by exact_mod_cast hh).trans hw
  have hsum : src+stage*n+j+1 ≤ lim.space := by
    rw [Nat.succ_mul] at hsrc
    omega
  apply Meets.of_body hmain
  unfold body time
  light_call hc using LightBandLookup.searchTime with r μ' ⟨hr,hm⟩
  subst μ'
  light_set value using hr,haddrNat,haddrNat',haddrNat'',hvalue,hvalue',LightBandLookup.searchTime
  exact ⟨rfl,rfl⟩

def program : Program := [body 1,LightBandLookup.searchBody 1]

theorem time_bound (L : ℕ) : time L ≤ 300*(L+1) := by
  unfold time LightBandLookup.searchTime
  omega

end ThreeSum.LightTernaryQueryLookup
