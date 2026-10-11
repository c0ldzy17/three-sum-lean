import Submission.ThreeSum.LightPascal
import Submission.ThreeSum.SubsetAddress
import Submission.ThreeSumApsp.Lang.Lib.PowTable

/-!
# Machine evaluation of compact subset addresses

The current width decreases by one in each recursive call. Its highest
power of two is read from a table, so neither division nor a loop proportional
to the numeric bit-mask value occurs. Pascal coefficients are single reads
from the constructed rectangular table.
-/

namespace ThreeSum.LightSubsetAddress

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal

variable {lim : Limits} {P : Program}

def Powers (μ : ℕ → ℤ) (base W : ℕ) : Prop :=
  ∀ i ≤ W, μ (base+i) = ((2^i : ℕ) : ℤ)

theorem powers_of_segment {μ : ℕ → ℤ} {base W : ℕ}
    (h : Seg μ base (powList 2 (W+1))) : Powers μ base W := by
  intro i hi
  have hs := h i (by simp; omega)
  simpa only [getElem_powList] using hs

theorem cell_offset_lt {W i j : ℕ} (hi : i ≤ W) (hj : j ≤ W) :
    i*(W+1)+j < tableSize W := by
  have hm := Nat.mul_le_mul_right (W+1) hi
  unfold tableSize
  nlinarith

/-- Arguments: remaining width, cardinality, mask, original width,
Pascal table, and power table. The seventh local stores the next bit index.
The return value replaces the first argument. -/
def rankBody (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.set 6 (v 0 -' k 1) ;;
      .ite (v 2 <' M (v 5 +' v 6))
        (.call pSelf [v 6,v 1,v 2,v 3,v 4,v 5] 0)
        (.call pSelf [v 6,v 1 -' k 1,v 2 -' M (v 5 +' v 6),v 3,v 4,v 5] 0 ;;
          .set 0 (v 0 +' M (v 4 +' v 6 *' (v 3 +' k 1) +' v 1))))
    (.set 0 (k 0))

def rankTime (L : ℕ) : ℕ := 100*L+30

theorem rank_meets {pRank W table powers : ℕ}
    (hprog : P[pRank]? = some (rankBody pRank)) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (htspace : table+tableSize W ≤ lim.space)
    (hpspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : Table μ table W) (hpowers : Powers μ powers W) :
    ∀ L k m : ℕ, L ≤ W → IsMask L k m →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pRank d [L,k,m,W,table,powers] μ (rankTime L)
        (fun r μ' => r = (layerRank L k m : ℤ) ∧ μ' = μ) := by
  have hpowW : ((2^W : ℕ) : ℤ) ≤ lim.word := by
    have hh : (2^W : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hhZ : ((2^W : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ) := by exact_mod_cast hh
    exact hhZ.trans hword
  have hwidth : W < lim.space := by omega
  intro L
  induction L with
  | zero =>
    intro k m hL hm d hd
    have hk : k=0 := by have := hm.le_width; omega
    have hmask : m=0 := by have := hm.1; simp only [pow_zero] at this; omega
    subst k
    subst m
    apply Meets.of_body hprog
    unfold rankBody rankTime
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
    light_set (0 : ℕ)
    exact ⟨rfl,rfl⟩
  | succ L ih =>
    intro k m hL hm d hd
    have hLW : L ≤ W := by omega
    have hkW : k ≤ W := hm.le_width.trans hL
    have hpowBound : (2^L : ℕ) ≤ 2^W := Nat.pow_le_pow_right (by decide) hLW
    have hmaskBound : m < 2^W := hm.1.trans_le (Nat.pow_le_pow_right (by decide) hL)
    have hmaskZ : (m : ℤ) < ((2^W : ℕ) : ℤ) := by exact_mod_cast hmaskBound
    have hpowZ : ((2^L : ℕ) : ℤ) ≤ lim.word := by
      have hh : ((2^L : ℕ) : ℤ) ≤ ((2^W : ℕ) : ℤ) := by exact_mod_cast hpowBound
      exact hh.trans hpowW
    have hpRead := hpowers L hLW
    have hpNonneg : (0 : ℤ) ≤ μ (powers+L) := by
      rw [hpRead]
      exact Int.natCast_nonneg _
    have htRead := htable L hLW k hkW
    have haddr : table+L*(W+1)+k < lim.space := by
      have hh := cell_offset_lt hLW hkW
      omega
    have hcast : (L : ℤ)*((W : ℤ)+1) = ((L*(W+1) : ℕ) : ℤ) := by
      push_cast
      rfl
    have haddrEq : ((table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(k : ℤ)).toNat =
        table+L*(W+1)+k := by
      have he : (table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(k : ℤ) =
          ((table+L*(W+1)+k : ℕ) : ℤ) := by push_cast; rfl
      rw [he, Int.toNat_natCast]
    have htReadZ : μ (((table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(k : ℤ)).toNat) =
        (L.choose k : ℤ) := by rw [haddrEq, htRead]
    apply Meets.of_body hprog
    unfold rankBody rankTime
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
    light_set (L : ℕ)
    light_if hloZ hhiZ : (m : ℤ) < μ (powers+L) using rankTime
    · have hlo : m < 2^L := by rw [hpRead] at hloZ; exact_mod_cast hloZ
      have hchild := ih k m hLW (hm.low hlo) (d+1) (by omega)
      light_call hchild using rankTime with res μ₁ ⟨hres,hmem⟩
      subst μ₁
      exact ⟨by simpa [layerRank,hlo] using hres,rfl⟩
    · have hhi : ¬m < 2^L := by
        intro hh
        apply hhiZ
        rw [hpRead]
        exact_mod_cast hh
      obtain ⟨hkpos,hchildMask⟩ := hm.high (Nat.le_of_not_gt hhi)
      have hchild := ih (k-1) (m-2^L) hLW hchildMask (d+1) (by omega)
      have hrank := (layerRank_lt hm).trans_le
        ((Nat.choose_le_two_pow (L+1) k).trans (Nat.pow_le_pow_right (by decide) hL))
      rw [layerRank, if_neg hhi] at hrank
      have hrankZ : ((L.choose k + layerRank L (k-1) (m-2^L) : ℕ) : ℤ) <
          ((2^W : ℕ) : ℤ) := by exact_mod_cast hrank
      have hchooseNonneg : (0 : ℤ) ≤ (L.choose k : ℤ) := Int.natCast_nonneg _
      have hrestNonneg : (0 : ℤ) ≤ (layerRank L (k-1) (m-2^L) : ℤ) := Int.natCast_nonneg _
      light_call hchild using rankTime with res μ₁ ⟨hres,hmem⟩
      subst μ₁
      light_set ((L.choose k + layerRank L (k-1) (m-2^L) : ℕ))
        using hres, htReadZ, rankTime, Nat.add_comm
      exact ⟨by simp [layerRank,hhi],rfl⟩

def rankProgram : Program := [rankBody 0]

theorem rankProgram_meets {W table powers L k m d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (htspace : table+tableSize W ≤ lim.space)
    (hpspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : Table μ table W) (hpowers : Powers μ powers W)
    (hL : L ≤ W) (hm : IsMask L k m) (hd : d+L ≤ lim.depth) :
    Meets lim rankProgram 0 d [L,k,m,W,table,powers] μ (rankTime L)
      (fun r μ' => r = (layerRank L k m : ℤ) ∧ μ' = μ) :=
  rank_meets rfl μ hw htspace hpspace hword htable hpowers L k m hL hm d hd

end ThreeSum.LightSubsetAddress
