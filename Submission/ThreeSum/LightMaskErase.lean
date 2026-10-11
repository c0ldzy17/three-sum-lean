import Submission.ThreeSum.MaskErase
import Submission.ThreeSum.LightSubsetAddress

/-!
# Machine deletion of one mask coordinate

Each call decreases the remaining width. Powers of two are table reads;
there is no division, advice, or loop proportional to the mask value.
-/

namespace ThreeSum.LightMaskErase

open Light ThreeSum.MaskErase ThreeSum.LightSubsetAddress

variable {lim : Limits} {P : Program}

/-- Arguments are remaining width, coordinate, mask, original width, power
base. Local 5 retains the next bit index across the recursive call. -/
def body (pSelf : ℕ) : Stmt :=
  .ite (k 0 <' v 0)
    (.set 5 (v 0 -' k 1) ;;
      .ite (v 2 <' M (v 4 +' v 5))
        (.call pSelf [v 5,v 1,v 2,v 3,v 4] 0)
        (.ite (v 1 =' v 5)
          (.set 0 (v 2 -' M (v 4 +' v 5)))
          (.call pSelf [v 5,v 1,v 2 -' M (v 4 +' v 5),v 3,v 4] 0 ;;
            .set 0 (M (v 4 +' v 5) +' v 0))))
    (.set 0 (k 0))

def time (L : ℕ) : ℕ := 100*L+30

theorem meets {pErase W powers : ℕ} (hprog : P[pErase]? = some (body pErase))
    (μ : ℕ → ℤ) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hpowers : Powers μ powers W) :
    ∀ L a m : ℕ, L ≤ W → a ≤ W → m < 2^L →
      ∀ d, d+L ≤ lim.depth →
      Meets lim P pErase d [L,a,m,W,powers] μ (time L)
        (fun r μ' => r = (eraseMask L a m : ℤ) ∧ μ' = μ) := by
  have hpowW : ((2^W : ℕ) : ℤ) ≤ lim.word := by
    have h : (2^W : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast h : ((2^W : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  intro L
  induction L with
  | zero =>
    intro a m hL ha hm d hd
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun h => False.elim (by simpa using h)) (fun _ => ?_)
    light_set (0 : ℕ)
    exact ⟨rfl,rfl⟩
  | succ L ih =>
    intro a m hL ha hm d hd
    have hLW : L ≤ W := by omega
    have hpm := hpowers L hLW
    have hpow : (2^L : ℕ) ≤ 2^W := Nat.pow_le_pow_right (by decide) hLW
    have hpowZ : ((2^L : ℕ) : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast hpow : ((2^L : ℕ) : ℤ) ≤ ((2^W : ℕ) : ℤ)).trans hpowW
    have hpowN : (0 : ℤ) ≤ μ (powers+L) := by rw [hpm]; exact Int.natCast_nonneg _
    have hmW : m < 2^W := hm.trans_le (Nat.pow_le_pow_right (by decide) hL)
    have hmZ : (m : ℤ) < ((2^W : ℕ) : ℤ) := by exact_mod_cast hmW
    simp only [Nat.cast_pow, Nat.cast_ofNat] at hpm hpowZ hmZ hpowW
    apply Meets.of_body hprog
    unfold body time
    refine Ends.iteLast (fun _ => ?_) (fun h => False.elim (by simpa using h))
    light_set (L : ℕ)
    light_if hloZ hhiZ : (m : ℤ) < μ (powers+L) using time
    · have hlo : m < 2^L := by rw [hpm] at hloZ; exact_mod_cast hloZ
      have hchild := ih a m hLW ha hlo (d+1) (by omega)
      light_call hchild using time with res μ₁ ⟨hr,hmem⟩
      subst μ₁
      exact ⟨by simpa [eraseMask,hlo] using hr,rfl⟩
    · have hhi : ¬m < 2^L := by
        intro hh
        apply hhiZ
        rw [hpm]
        exact_mod_cast hh
      have hpLe : 2^L ≤ m := Nat.le_of_not_gt hhi
      have hpLeZ : ((2^L : ℕ) : ℤ) ≤ m := by exact_mod_cast hpLe
      have hrest : m-2^L < 2^L := by rw [pow_succ] at hm; omega
      have hsub : (m : ℤ)-((2^L : ℕ) : ℤ) = ((m-2^L : ℕ) : ℤ) := by omega
      simp only [Nat.cast_pow, Nat.cast_ofNat] at hpLeZ hsub
      light_if haZ hnaZ : (a : ℤ) = (L : ℤ) using time
      · have haL : a = L := by exact_mod_cast haZ
        light_set (m-2^L : ℕ) using hpm,hsub,time
        exact ⟨by simp [eraseMask,hhi,haL],rfl⟩
      · have haL : a ≠ L := by exact_mod_cast hnaZ
        have hchild := ih a (m-2^L) hLW ha hrest (d+1) (by omega)
        have hb := eraseMask_le (a := a) hrest
        have hs : 2^L + eraseMask L a (m-2^L) ≤ m := by omega
        have hsZ : ((2^L : ℕ) : ℤ)+(eraseMask L a (m-2^L) : ℤ) ≤ m := by
          exact_mod_cast hs
        simp only [Nat.cast_pow, Nat.cast_ofNat] at hsZ
        have heNonneg : (0 : ℤ) ≤ eraseMask L a (m-2^L) := Int.natCast_nonneg _
        light_call hchild using hpm,hsub,time with res μ₁ ⟨hr,hmem⟩
        subst μ₁
        light_set (2^L + eraseMask L a (m-2^L) : ℕ) using hpm,hr,time
        exact ⟨by simp [eraseMask,hhi,haL],rfl⟩

def program : Program := [body 0]

theorem program_meets {μ : ℕ → ℤ} {L a m W powers d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hpowers : Powers μ powers W)
    (hL : L ≤ W) (ha : a ≤ W) (hm : m < 2^L) (hd : d+L ≤ lim.depth) :
    Meets lim program 0 d [L,a,m,W,powers] μ (time L)
      (fun r μ' => r = (eraseMask L a m : ℤ) ∧ μ' = μ) :=
  meets rfl μ hw hspace hword hpowers L a m hL ha hm d hd

end ThreeSum.LightMaskErase
