import Submission.ThreeSum.LightSubsetAddress

/-! # The layer-offset scan for compact downset addresses -/

namespace ThreeSum.LightSubsetOffset

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program} {d : ℕ}

theorem layerOffset_bound (L k : ℕ) : layerOffset L k ≤ k*2^L := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [layerOffset_succ]
    have hb := Nat.choose_le_two_pow L k
    nlinarith

def body : Stmt :=
  .set 5 (k 0) ;;
  .for 4 (v 2) (
    .set 5 (v 5 +' M (v 0 +' v 1 *' (v 3 +' k 1) +' v 4))) ;;
  .set 0 (v 5)

def time (k : ℕ) : ℕ := 30*k+20

theorem meets {pOffset table W L k : ℕ}
    (hprog : P[pOffset]? = some body) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : table+tableSize W ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (htable : Table μ table W) (hL : L ≤ W) (hk : k ≤ W) :
    Meets lim P pOffset d [table,L,k,W] μ (time k)
      (fun r μ' => r = (layerOffset L k : ℤ) ∧ μ' = μ) := by
  have hsize : W+1 ≤ tableSize W := by unfold tableSize; nlinarith
  have hpow : (2^L : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hacc (i : ℕ) (hi : i ≤ k) :
      (layerOffset L i : ℤ) ≤ lim.word := by
    have hm := Nat.mul_le_mul (show i ≤ W+1 by omega) hpow
    have hb := (layerOffset_bound L i).trans hm
    have hbZ : (layerOffset L i : ℤ) ≤ (((W+1)*2^(W+1) : ℕ) : ℤ) := by
      exact_mod_cast hb
    exact hbZ.trans hword
  have hcast : (L : ℤ)*((W : ℤ)+1) = ((L*(W+1) : ℕ) : ℤ) := by push_cast; rfl
  apply Meets.of_body hprog
  unfold body time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for (T := 30*k+6)
    (Q := fun σ => σ = ⟨frame [table,L,k,W,k,(layerOffset L k : ℕ)],μ⟩)
    (fun i σ => σ = ⟨frame [table,L,k,W,i,(layerOffset L i : ℕ)],μ⟩)
    k 22 ?_ ?_ ?_ ?_ (hT := by light_time)) ?_
  · simp [update_frame_setLocal]
  · rintro i _ hi _ rfl
    have hiW : i ≤ W := by omega
    have htRead := htable L hL i hiW
    have haddr : table+L*(W+1)+i < lim.space := by
      have hh := cell_offset_lt hL hiW
      omega
    have haddrEq : ((table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(i : ℤ)).toNat =
        table+L*(W+1)+i := by
      have he : (table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(i : ℤ) =
          ((table+L*(W+1)+i : ℕ) : ℤ) := by push_cast; rfl
      rw [he, Int.toNat_natCast]
    have htReadZ : μ (((table : ℤ)+(L : ℤ)*((W : ℤ)+1)+(i : ℤ)).toNat) =
        (L.choose i : ℤ) := by rw [haddrEq, htRead]
    have hsum := hacc (i+1) (by omega)
    rw [layerOffset_succ, Nat.cast_add] at hsum
    have hnonneg : (0 : ℤ) ≤ (layerOffset L i : ℤ) := Int.natCast_nonneg _
    have hcNonneg : (0 : ℤ) ≤ (L.choose i : ℤ) := Int.natCast_nonneg _
    refine Ends.setLast ?_ (hs := by light_side [htReadZ]) (hT := by light_time)
    simp [update_frame_setLocal, htReadZ, layerOffset_succ]
  · intro σ hc hs
    exact hs
  · rintro i _ hi _ rfl
    light_side
  · intro σ hs
    rw [hs]
    have hf := hacc k le_rfl
    have hn : (0 : ℤ) ≤ (layerOffset L k : ℤ) := Int.natCast_nonneg _
    light_set (layerOffset L k : ℕ)
    exact ⟨rfl,rfl⟩

end ThreeSum.LightSubsetOffset
