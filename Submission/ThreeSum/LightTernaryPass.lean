import Submission.ThreeSum.LightTernaryLookup

/-!
# Actual pass over a compressed ternary bank

The metadata contains a digit and three lower word codes per stored address.
The machine searches the compact sorted-code segment, reads source values,
performs the three-state zeta arithmetic, and writes exactly one output cell
per stored address. This module charges lookup and value work. Construction
of the enumerated codes and metadata is a separate prerequisite.
-/

namespace ThreeSum.LightTernaryPass

set_option maxHeartbeats 2000000

open Light ThreeSum.TernaryQuery ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

def roundBody (pCell : ℕ) : Stmt :=
  .call pCell [v 0,v 1,v 2,v 3,M (v 4 +' v 7),
    M (v 4 +' v 1 +' v 7),M (v 4 +' k 2 *' v 1 +' v 7),
    M (v 4 +' k 3 *' v 1 +' v 7),v 5] 8 ;;
  .store (v 6 +' v 7) (v 8)

/-- Arguments: code base, count, powers base, lookup width, four-row metadata,
source values, destination values. Only the compressed count is traversed. -/
def body (pCell : ℕ) : Stmt := .for 7 (v 1) (roundBody pCell)

def time (L n : ℕ) : ℕ := n * (LightTernaryLookup.time L + 100) + 20

def values (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ) (f : ℕ → ℤ) (j : ℕ) : ℤ :=
  zetaDigit (fun e => f (ix e j)) (digits j)

/-- A semantic bridge from the compact metadata to the exact coordinate stage.
Only lower digit metadata must agree; higher slots can duplicate an address.
-/
theorem values_eq_coordinateZeta {N : ℕ} (enumeration : ℕ →
    ThreeSum.TernaryJointType.TritWord N) (i : Fin N)
    (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ)
    (F : ThreeSum.TernaryJointType.TritWord N → ℤ) (j : ℕ)
    (hdigit : digits j = enumeration j i)
    (hindex : ∀ e ≤ digits j, enumeration (ix e j) =
      Function.update (enumeration j) i e) :
    values digits ix (fun k => F (enumeration k)) j =
      coordinateZeta i F (enumeration j) := by
  unfold values coordinateZeta
  rw [← hdigit]
  apply zetaDigit_congr_below
  intro e he
  dsimp only
  rw [hindex e he]

def Inv (μ : ℕ → ℤ) (a n powers L keyBase src dst : ℕ)
    (digits : ℕ → Fin 3) (ix : Fin 3 → ℕ → ℕ) (f : ℕ → ℤ)
    (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [a,n,powers,L,keyBase,src,dst,j,r],
    wrote μ dst (values digits ix f) j⟩

theorem meets {pMain pCell pSearch pValue a n powers W L keyBase src dst d U : ℕ}
    (hmain : P[pMain]? = some (body pCell))
    (hcell : P[pCell]? = some (LightTernaryLookup.body pSearch pValue))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hvalue : P[pValue]? = some LightTernaryCell.zetaBody)
    (μ : ℕ → ℤ) (codes f : ℕ → ℤ) (digits : ℕ → Fin 3)
    (ix : Fin 3 → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ dst) (hsrc : src+n ≤ dst)
    (hmeta : keyBase+4*n ≤ dst) (hpows : powers+(W+1) ≤ dst)
    (hdst : dst+n ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hcodes : ∀ i < n, μ (a+i) = codes i)
    (hsource : ∀ i < n, μ (src+i) = f i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k)
    (hindex : ∀ e j, j < n → ix e j < n)
    (hmd : ∀ j < n, μ (keyBase+j) = ((digits j).val : ℤ))
    (hm0 : ∀ j < n, μ (keyBase+n+j) = codes (ix 0 j))
    (hm1 : ∀ j < n, μ (keyBase+2*n+j) = codes (ix 1 j))
    (hm2 : ∀ j < n, μ (keyBase+3*n+j) = codes (ix 2 j))
    (hf : ∀ j < n, |f j| ≤ U) (hvalword : 4*(U : ℤ)+3 ≤ lim.word)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+2 ≤ lim.depth) :
    Meets lim P pMain d [a,n,powers,L,keyBase,src,dst] μ (time L n)
      (fun _ μ' => (∀ j < n, μ' (dst+j) = values digits ix f j) ∧
        SameOutside μ μ' dst n) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ a n powers L keyBase src dst digits ix f) n
    (LightTernaryLookup.time L + 85) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0, ?_⟩
    simp [Inv, update_frame_setLocal, wrote_zero]
    change frame [(a : ℤ),n,powers,L,keyBase,src,dst,0] =
      frame ([(a : ℤ),n,powers,L,keyBase,src,dst,0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r,rfl⟩
    let μj := wrote μ dst (values digits ix f) j
    have hkeep : ∀ x < dst, μj x = μ x := by
      intro x hx
      exact wrote_rest (Or.inl hx)
    have hc0 : ∀ i < n, μj (a+i) = codes i := by
      intro i hi
      rw [hkeep _ (by omega),hcodes i hi]
    have hs0 : ∀ i < n, μj (src+i) = f i := by
      intro i hi
      rw [hkeep _ (by omega),hsource i hi]
    have hp0 : Powers μj powers W := by
      intro i hi
      rw [hkeep _ (by omega),hpowers i hi]
    have hdig : μj (keyBase+j) = ((digits j).val : ℤ) := by
      rw [hkeep _ (by omega),hmd j hj]
    have hm0j : μj (keyBase+n+j) = codes (ix 0 j) := by
      rw [hkeep _ (by omega),hm0 j hj]
    have hm1j : μj (keyBase+2*n+j) = codes (ix 1 j) := by
      rw [hkeep _ (by omega),hm1 j hj]
    have hm2j : μj (keyBase+3*n+j) = codes (ix 2 j) := by
      rw [hkeep _ (by omega),hm2 j hj]
    have ha0 : ((keyBase : ℤ)+(n : ℤ)+(j : ℤ)).toNat = keyBase+n+j := by
      rw [← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast]
    have ha1 : ((keyBase : ℤ)+2*(n : ℤ)+(j : ℤ)).toNat = keyBase+2*n+j := by
      rw [show (2 : ℤ)*(n : ℤ) = ((2*n : ℕ) : ℤ) by push_cast; rfl,
        ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast]
    have ha2 : ((keyBase : ℤ)+3*(n : ℤ)+(j : ℤ)).toNat = keyBase+3*n+j := by
      rw [show (3 : ℤ)*(n : ℤ) = ((3*n : ℕ) : ℤ) by push_cast; rfl,
        ← Nat.cast_add, ← Nat.cast_add, Int.toNat_natCast]
    have hc := LightTernaryLookup.zeta_meets (d := d+1) hcell hsearch hvalue
      μj codes (digits j) (fun e => f (ix e j)) hw
      (by omega) (by omega) (by omega) hword hc0 hp0 hsorted
      (hindex 0 j hj) (hindex 1 j hj) (hindex 2 j hj)
      (hs0 _ (hindex 0 j hj)) (hs0 _ (hindex 1 j hj)) (hs0 _ (hindex 2 j hj))
      (fun e => hf _ (hindex e j hj)) hvalword hL hn (by omega)
    have hv : |values digits ix f j| ≤ 4*(U : ℤ) := by
      unfold values zetaDigit
      dsimp only
      split_ifs <;> have h0 := hf _ (hindex 0 j hj) <;>
        have h1 := hf _ (hindex 1 j hj) <;> have h2 := hf _ (hindex 2 j hj)
      · omega
      · exact (abs_add_le _ _).trans (by omega)
      · have hm : |2 * f (ix 1 j)| ≤ 2 * (U : ℤ) := by
          rw [abs_mul]
          norm_num
          omega
        calc
          |f (ix 0 j) + 2 * f (ix 1 j) + f (ix 2 j)| ≤
              |f (ix 0 j) + 2 * f (ix 1 j)| + |f (ix 2 j)| := abs_add_le _ _
          _ ≤ (|f (ix 0 j)| + |2 * f (ix 1 j)|) + |f (ix 2 j)| :=
            add_le_add (abs_add_le _ _) le_rfl
          _ ≤ 4*(U : ℤ) := by omega
    unfold roundBody
    light_call hc using μj,hdig,ha0,ha1,ha2,hm0j,hm1j,hm2j,LightTernaryLookup.time,
      LightBandLookup.searchTime,LightTernaryCell.time with out μ' ⟨hout,hmem⟩
    subst μ'
    light_store (dst+j) (values digits ix f j) using hout,values,
      LightTernaryLookup.time,LightBandLookup.searchTime,LightTernaryCell.time
    refine ⟨by simp,out,?_⟩
    simp [Inv, update_frame_setLocal, wrote_succ, μj]
  case done =>
    rintro _ _ ⟨r,rfl⟩
    refine ⟨fun j hj => wrote_done hj, ?_⟩
    intro x hx
    exact wrote_rest hx
  case bound =>
    rintro j _ hj _ ⟨r,rfl⟩
    light_side

def program : Program := [body 1, LightTernaryLookup.body 2 3,
  LightBandLookup.searchBody 2, LightTernaryCell.zetaBody]

theorem time_bound (L n : ℕ) : time L n ≤ 800*(L+1)*(n+1) := by
  have h := LightTernaryLookup.time_bound L
  unfold time
  nlinarith

end ThreeSum.LightTernaryPass
