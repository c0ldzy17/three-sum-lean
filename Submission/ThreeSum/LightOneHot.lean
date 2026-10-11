import Submission.ThreeSum.OneHotMask
import Submission.ThreeSum.LightSubsetAddress

/-!
# A fixed word-RAM one-hot hash evaluator

The recursive procedure visits the mask's bit positions in decreasing order,
reads the selected coefficient, and adds it. Its time is linear in the width,
independent of the mask's numeric magnitude. The public wrapper constructs
its own powers-of-two table and preserves both coefficient arrays.
-/

namespace ThreeSum.LightOneHot

open Light ThreeSum.OneHotMask ThreeSum.LightSubsetAddress

set_option linter.deprecated false
set_option linter.unusedSimpArgs false

variable {lim : Limits} {P : Program}

/-- Arguments are current width, mask, original width, power table, and the
two coefficient arrays. Local 6 retains the current coordinate. -/
def body (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.set 6 (v 0 -' k 1) ;;
      .ite (v 1 <' M (v 3 +' v 6))
        (.call pSelf [v 6,v 1,v 2,v 3,v 4,v 5] 0 ;;
          .set 0 (v 0 +' M (v 4 +' v 6)))
        (.call pSelf [v 6,v 1 -' M (v 3 +' v 6),v 2,v 3,v 4,v 5] 0 ;;
          .set 0 (v 0 +' M (v 5 +' v 6))))
    (.set 0 (k 0))

def time (L : ℕ) : ℕ := 100*L+30

def word (W U : ℕ) : ℕ := 2^(W+1)+(W+1)*U

theorem meets {pHash W powers src0 src1 U : ℕ}
    (hprog : P[pHash]? = some (body pHash))
    (μ : ℕ → ℤ) (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hsrc0 : src0+W ≤ lim.space) (hsrc1 : src1+W ≤ lim.space)
    (hword : (word W U : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W)
    (hread0 : ∀ i < W, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < W, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < W, w0 i ≤ U) (hbound1 : ∀ i < W, w1 i ≤ U) :
    ∀ L m : ℕ, L ≤ W → m < 2^L →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pHash d [L,m,W,powers,src0,src1] μ (time L)
        (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧ μ' = μ) := by
  have hpBound : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(W+1) ≤ word W U := by unfold word; omega
    exact (by exact_mod_cast hh : ((2^(W+1) : ℕ) : ℤ) ≤ (word W U : ℤ)).trans hword
  have hvBound : ((W*U : ℕ) : ℤ) ≤ lim.word := by
    have hh : W*U ≤ word W U := by
      calc
        W*U ≤ (W+1)*U := Nat.mul_le_mul_right U (Nat.le_succ W)
        _ ≤ 2^(W+1)+(W+1)*U := Nat.le_add_left _ _
    exact (by exact_mod_cast hh : ((W*U : ℕ) : ℤ) ≤ (word W U : ℤ)).trans hword
  intro L
  induction L with
  | zero =>
    intro m hL hm d hd
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
    light_set (0 : ℕ)
    exact ⟨rfl,rfl⟩
  | succ L ih =>
    intro m hL hm d hd
    have hLW : L ≤ W := by omega
    have hLt : L < W := by omega
    have hpm := hpowers L hLW
    have h0 := hread0 L hLt
    have h1 := hread1 L hLt
    have h0U := hbound0 L hLt
    have h1U := hbound1 L hLt
    have h0Nonneg : (0 : ℤ) ≤ w0 L := Int.natCast_nonneg _
    have h1Nonneg : (0 : ℤ) ≤ w1 L := Int.natCast_nonneg _
    have hpLe : (2^L : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hpZ : ((2^L : ℕ) : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast hpLe : ((2^L : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hpBound
    have hmLe : m < 2^(W+1) := hm.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
    have hmZ : (m : ℤ) < ((2^(W+1) : ℕ) : ℤ) := by exact_mod_cast hmLe
    have hpNonneg : (0 : ℤ) ≤ μ (powers+L) := by rw [hpm]; exact Int.natCast_nonneg _
    have h0' : ∀ i < L, w0 i ≤ U := fun i hi => hbound0 i (by omega)
    have h1' : ∀ i < L, w1 i ≤ U := fun i hi => hbound1 i (by omega)
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hpm hpZ hmZ hpBound
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
    light_set (L : ℕ)
    light_if hloZ hhiZ : (m : ℤ) < μ (powers+L) using time
    · have hlo : m < 2^L := by rw [hpm] at hloZ; exact_mod_cast hloZ
      have hchild := ih m hLW hlo (d+1) (by omega)
      have he := OneHotMask.eval_le (m := m) h0' h1'
      have hs : OneHotMask.eval w0 w1 L m + w0 L ≤ W*U := by nlinarith
      have hsZ : (OneHotMask.eval w0 w1 L m : ℤ)+(w0 L : ℤ) ≤ ((W*U : ℕ) : ℤ) := by
        exact_mod_cast hs
      have heNonneg : (0 : ℤ) ≤ OneHotMask.eval w0 w1 L m := Int.natCast_nonneg _
      light_call hchild using time with res μ₁ ⟨hr,hmem⟩
      subst μ₁
      light_set (OneHotMask.eval w0 w1 L m+w0 L : ℕ) using hr,h0,time
      exact ⟨by simp [OneHotMask.eval,hlo],rfl⟩
    · have hhi : ¬m < 2^L := by
        intro hh
        apply hhiZ
        rw [hpm]
        exact_mod_cast hh
      have hpM : 2^L ≤ m := Nat.le_of_not_gt hhi
      have hrest : m-2^L < 2^L := by rw [pow_succ] at hm; omega
      have hsub : (m : ℤ)-((2^L : ℕ) : ℤ) = ((m-2^L : ℕ) : ℤ) := by omega
      simp only [Nat.cast_pow, Nat.cast_ofNat] at hsub
      have hchild := ih (m-2^L) hLW hrest (d+1) (by omega)
      have he := OneHotMask.eval_le (m := m-2^L) h0' h1'
      have hs : OneHotMask.eval w0 w1 L (m-2^L)+w1 L ≤ W*U := by nlinarith
      have hsZ : (OneHotMask.eval w0 w1 L (m-2^L) : ℤ)+(w1 L : ℤ) ≤ ((W*U : ℕ) : ℤ) := by
        exact_mod_cast hs
      have heNonneg : (0 : ℤ) ≤ OneHotMask.eval w0 w1 L (m-2^L) := Int.natCast_nonneg _
      light_call hchild using hpm,hsub,time with res μ₁ ⟨hr,hmem⟩
      subst μ₁
      light_set (OneHotMask.eval w0 w1 L (m-2^L)+w1 L : ℕ) using hr,h1,time
      exact ⟨by simp [OneHotMask.eval,hhi],rfl⟩

def setupBody (pPowers pHash : ℕ) : Stmt :=
  .call pPowers [v 4,v 0 +' k 1,k 2] 5 ;;
  .call pHash [v 0,v 1,v 0,v 4,v 2,v 3] 0

def setupTime (L : ℕ) : ℕ := powTableTime (L+1)+time L+40

theorem setup_meets {pMain pPowers pHash : ℕ}
    (hmain : P[pMain]? = some (setupBody pPowers pHash))
    (hpowers : P[pPowers]? = some powTableBody)
    (hhash : P[pHash]? = some (body pHash))
    {μ : ℕ → ℤ} {L m src0 src1 work U d : ℕ} (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hm : m < 2^L) (hd : d+L+1 ≤ lim.depth)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim P pMain d [L,m,src0,src1,work] μ (setupTime L)
      (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧
        Powers μ' work L ∧ SameOutside μ μ' work (L+1)) := by
  have hpBound : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word := by
    have hh : 2^(L+1) ≤ word L U := by unfold word; omega
    exact (by exact_mod_cast hh : ((2^(L+1) : ℕ) : ℤ) ≤ (word L U : ℤ)).trans hword
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hz : (2 : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ) := by exact_mod_cast hh
    exact hz.trans hpBound
  apply Meets.of_body hmain
  unfold setupBody setupTime
  have hpow := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := L+1) (b := 2) hpowers hw hspace (by
      intro j hj
      have hh : (2^j : ℕ) ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) hj
      exact (by exact_mod_cast hh : ((2^j : ℕ) : ℤ) ≤ ((2^(L+1) : ℕ) : ℤ)).trans hpBound)
  light_call hpow using powTableTime,time with _ μ₁ ⟨hpowSeg,hsame⟩
  have hcall := meets (W := L) (powers := work) (src0 := src0) (src1 := src1) (U := U)
    hhash μ₁ w0 w1 hw hspace (by omega) (by omega) hword
    (powers_of_segment hpowSeg)
    (by intro i hi; rw [hsame (src0+i) (Or.inl (by omega))]; exact hread0 i hi)
    (by intro i hi; rw [hsame (src1+i) (Or.inl (by omega))]; exact hread1 i hi)
    hbound0 hbound1 L m le_rfl hm (d+1) (by omega)
  light_call hcall using powTableTime,time with res μ₂ ⟨hres,hmem⟩
  subst μ₂
  exact ⟨by simpa using hres,powers_of_segment hpowSeg,hsame⟩

def program : Program := [setupBody 1 2,powTableBody,body 2]

theorem program_meets {μ : ℕ → ℤ} {L m src0 src1 work U d : ℕ} (w0 w1 : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : work+(L+1) ≤ lim.space)
    (hsrc0 : src0+L ≤ work) (hsrc1 : src1+L ≤ work)
    (hword : (word L U : ℤ) ≤ lim.word)
    (hm : m < 2^L) (hd : d+L+1 ≤ lim.depth)
    (hread0 : ∀ i < L, μ (src0+i) = (w0 i : ℤ))
    (hread1 : ∀ i < L, μ (src1+i) = (w1 i : ℤ))
    (hbound0 : ∀ i < L, w0 i ≤ U) (hbound1 : ∀ i < L, w1 i ≤ U) :
    Meets lim program 0 d [L,m,src0,src1,work] μ (setupTime L)
      (fun r μ' => r = (OneHotMask.eval w0 w1 L m : ℤ) ∧
        Powers μ' work L ∧ SameOutside μ μ' work (L+1)) :=
  setup_meets rfl rfl rfl w0 w1 hw hspace hsrc0 hsrc1 hword hm hd
    hread0 hread1 hbound0 hbound1

theorem setupTime_bound (L : ℕ) : setupTime L ≤ 200*(L+1) := by
  unfold setupTime powTableTime time
  omega

end ThreeSum.LightOneHot
