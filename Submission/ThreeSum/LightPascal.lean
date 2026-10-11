import Submission.ThreeSum.LightArray
import Mathlib.Data.Nat.Choose.Bounds

/-!
# A rectangular Pascal table in the benchmark language

Every coefficient is built once by addition from the preceding row.
The row-major representation supports one multiplication and two additions
per later lookup. No recursive binomial-coefficient evaluation is used.
-/

namespace ThreeSum.LightPascal

open Light

variable {lim : Limits} {P : Program} {d : ℕ}

def tableSize (L : ℕ) : ℕ := (L+1)^2

def Table (μ : ℕ → ℤ) (dst L : ℕ) : Prop :=
  ∀ i ≤ L, ∀ j ≤ L, μ (dst + i*(L+1) + j) = (i.choose j : ℤ)

def rowBody (pLinear : ℕ) : Stmt :=
  .call pLinear [v 0, v 0 +' k 1, v 1 +' k 1, v 2, k 1] 3 ;;
  .store (v 1) (k 1)

def rowTime (L : ℕ) : ℕ := LightArray.linearTime L + 20

theorem row_meets {pRow pLinear : ℕ}
    (hrow : P[pRow]? = some (rowBody pLinear))
    (hlinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst L i : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hsrc : src+(L+1) ≤ lim.space) (hdst : dst+(L+1) ≤ lim.space)
    (hsep : Apart src (L+1) dst (L+1)) (hi : i ≤ L)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalues : ∀ j ≤ L, μ (src+j) = (i.choose j : ℤ)) :
    Meets lim P pRow d [src,dst,L] μ (rowTime L) fun _ μ' =>
      (∀ j ≤ L, μ' (dst+j) = ((i+1).choose j : ℤ)) ∧
        SameOutside μ μ' dst (L+1) := by
  have hb (j : ℕ) : i.choose j ≤ 2^L :=
    (Nat.choose_le_two_pow i j).trans (Nat.pow_le_pow_right (by decide) hi)
  have hbound (j : ℕ) (hj : j ≤ L) : |μ (src+j)| ≤ ((2^L : ℕ) : ℤ) := by
    rw [hvalues j hj, abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast hb j
  have htwice : 2*((2^L : ℕ) : ℤ) ≤ lim.word := by
    simpa only [pow_succ, Nat.cast_mul, Nat.cast_ofNat, mul_comm] using hword
  have hcall := LightArray.linear_bounded_meets (d := d+1) (μ := μ)
    (srcA := src) (srcB := src+1) (dst := dst+1) (n := L) (U := 2^L) (c := 1)
    hlinear hw (by omega) (by omega) (by omega)
    (Or.inr (by omega)) (Or.inr (by omega)) (by norm_num) htwice (by
      intro j hj
      refine ⟨hbound j (by omega), ?_⟩
      simpa only [Nat.add_assoc, Nat.add_comm 1 j] using hbound (j+1) (by omega))
  apply Meets.of_body hrow
  unfold rowBody rowTime
  light_call hcall using LightArray.linearTime with _ μ₁ ⟨hadded,hkept⟩
  light_store dst 1 using LightArray.linearTime
  refine ⟨?_, ?_⟩
  · intro j hj
    cases j with
    | zero => simp
    | succ j =>
      change Function.update μ₁ dst 1 (dst+(j+1)) = _
      rw [Function.update_of_ne (by omega)]
      have hjL : j < L := by omega
      have hh := hadded j hjL
      rw [hvalues j (by omega), show src+1+j=src+(j+1) by omega,
        hvalues (j+1) (by omega), one_mul] at hh
      simpa only [Nat.add_assoc, Nat.add_comm 1 j, Nat.choose_succ_succ,
        Nat.cast_add] using hh
  · intro a ha
    change Function.update μ₁ dst 1 a = _
    rw [Function.update_of_ne (by omega)]
    exact hkept a (by omega)

def buildBody (pFill pRow : ℕ) : Stmt :=
  .set 2 (v 1 +' k 1) ;;
  .call pFill [v 0,v 2,k 0] 4 ;;
  .store (v 0) (k 1) ;;
  .for 3 (v 1) (
    .call pRow [v 0 +' v 3 *' v 2,
      v 0 +' (v 3 +' k 1) *' v 2, v 1] 4)

def buildTime (L : ℕ) : ℕ := fillTime (L+1) + L*(rowTime L+100)+100

def Inv (μ : ℕ → ℤ) (dst L i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ), σ = ⟨frame [dst,L,L+1,i,r],μ'⟩ ∧
    (∀ a ≤ i, ∀ j ≤ L, μ' (dst+a*(L+1)+j) = (a.choose j : ℤ)) ∧
      SameOutside μ μ' dst (tableSize L)

theorem build_meets {pBuild pFill pRow pLinear : ℕ}
    (hbuild : P[pBuild]? = some (buildBody pFill pRow))
    (hfill : P[pFill]? = some fillBody)
    (hrow : P[pRow]? = some (rowBody pLinear))
    (hlinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {dst L : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hspace : dst+tableSize L ≤ lim.space)
    (hword : ((2^(L+1) : ℕ) : ℤ) ≤ lim.word) :
    Meets lim P pBuild d [dst,L] μ (buildTime L) fun _ μ' =>
      Table μ' dst L ∧ SameOutside μ μ' dst (tableSize L) := by
  have hsize : L+1 ≤ tableSize L := by unfold tableSize; nlinarith
  have hfirst : dst+(L+1) ≤ lim.space := by omega
  apply Meets.of_body hbuild
  unfold buildBody buildTime
  light_set (L+1 : ℕ) using rowTime, LightArray.linearTime
  light_call (fill_meets (d := d+1) hfill (μ := μ) (dst := dst) (n := L+1) (x := 0)
    hw hfirst) using rowTime, LightArray.linearTime with res μ₁ ⟨hzero,hkept₁⟩
  light_store dst 1 using rowTime, LightArray.linearTime
  let μ₂ := Function.update μ₁ dst 1
  refine Ends.for (Inv μ dst L) L (rowTime L+50) ?start ?round ?done ?bound
    (hT := by light_time [rowTime, LightArray.linearTime])
  case start =>
    refine ⟨res,μ₂,?_,?_,?_⟩
    · simp [μ₂, update_frame_setLocal]
    · intro a ha j hj
      have haz : a=0 := by omega
      subst a
      simp only [Nat.zero_mul, Nat.add_zero]
      by_cases hjz : j=0
      · subst j
        simp [μ₂]
      · rw [show μ₂ (dst+j) = μ₁ (dst+j) by
          exact Function.update_of_ne (by omega) _ _]
        have hh := hzero j (by simp; omega)
        simpa only [List.getElem_replicate,
          Nat.choose_eq_zero_of_lt (show 0 < j by omega), Nat.cast_zero] using hh
    · intro a ha
      rw [show μ₂ a = μ₁ a by exact Function.update_of_ne (by omega) _ _]
      exact hkept₁ a (by omega)
  case round =>
    rintro i _ hi _ ⟨r,μ',rfl,htable,hkept⟩
    have hrowBound : (i+2)*(L+1) ≤ tableSize L := by
      have hm := Nat.mul_le_mul_right (L+1) (show i+2 ≤ L+1 by omega)
      simpa only [tableSize, pow_two] using hm
    have hlow : 0 ≤ i*(L+1) := Nat.zero_le _
    have hnext : (i+1)*(L+1) = i*(L+1)+(L+1) := by ring
    have hlast : (i+2)*(L+1) = (i+1)*(L+1)+(L+1) := by ring
    have hcastI : (i : ℤ)*((L : ℤ)+1) = ((i*(L+1) : ℕ) : ℤ) := by push_cast; rfl
    have hcastNext : ((i : ℤ)+1)*((L : ℤ)+1) = (((i+1)*(L+1) : ℕ) : ℤ) := by
      push_cast
      rfl
    have hcall := row_meets (d := d+1) (μ := μ') (src := dst+i*(L+1))
      (dst := dst+(i+1)*(L+1)) (L := L) (i := i)
      hrow hlinear hw hd (by omega) (by omega) (by left; omega) (by omega)
      hword (htable i le_rfl)
    light_call hcall using rowTime, LightArray.linearTime with resNew μ₃ ⟨hnew,hkept₂⟩
    refine ⟨by simp, resNew,μ₃,by simp [update_frame_setLocal],?_,?_⟩
    · intro a ha j hj
      by_cases hai : a=i+1
      · subst a
        exact hnew j hj
      · have hai' : a ≤ i := by omega
        have hmul := Nat.mul_le_mul_right (L+1) hai'
        rw [hkept₂ _ (by omega)]
        exact htable a hai' j hj
    · intro a ha
      exact (hkept₂ a (by omega)).trans (hkept a ha)
  case done =>
    rintro _ _ ⟨r,μ',rfl,htable,hkept⟩
    exact ⟨htable,hkept⟩
  case bound =>
    rintro i _ _ _ ⟨r,μ',rfl,_,_⟩
    simp

theorem buildTime_bound (L : ℕ) : buildTime L ≤ 1000*(L+1)^2 := by
  unfold buildTime rowTime LightArray.linearTime
  simp only [fillTime]
  nlinarith

end ThreeSum.LightPascal
