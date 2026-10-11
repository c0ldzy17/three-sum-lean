import Submission.ThreeSum.BandPartition
import Submission.ThreeSum.LightSmallDivide
import Submission.ThreeSumApsp.Lang.Lib.Copy

/-!
# Constructing consecutive band endpoints in actual memory

The program computes the number of bands itself. Its quotient loop is charged
linearly in that number, and both endpoint passes issue bounded-address
loads from the sorted source. Output arrays reserve `n` cells each; only the
computed band count is populated.
-/

namespace ThreeSum.LightBandPartition

open Light ThreeSum.BandPartition

variable {lim : Limits} {P : Program}

def lowerBody : Stmt :=
  pass 4 (v 2) (v 1) (M (v 0 +' v 4 *' v 3))

def lowerTime (m : ℕ) : ℕ := 25*m+6

theorem lower_meets {p src dst n g d : ℕ} (hp : P[p]? = some lowerBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hdst : dst+size n g ≤ lim.space)
    (hread : ∀ i < n, μ (src+i) = f i) :
    Meets lim P p d [src,dst,size n g,g] μ (lowerTime (size n g))
      (fun _ μ' => (∀ i < size n g, μ' (dst+i) = f (start g i)) ∧
        SameOutside μ μ' dst (size n g)) := by
  apply Meets.of_body hp
  unfold lowerBody
  refine Ends.pass (fun i => f (start g i)) (fun i hi => ?_)
    ⟨fun i hi => by exact wrote_done (μ := μ) (dst := dst) (f := fun i => f (start g i)) hi,
      by light_keep⟩ hw hdst rfl rfl (hT := by light_time [lowerTime])
  have hidx : i*g < n := start_lt hg hi
  have haddr : ((src : ℤ)+(i : ℤ)*(g : ℤ)).toNat = src+i*g := by
    rw [← Nat.cast_mul,toNat_natCast_add_natCast]
  have hr : wrote μ dst (fun i => f (start g i)) i (src+i*g) = f (start g i) := by
    rw [wrote_rest (by omega)]
    exact hread _ hidx
  have hmulN : (0 : ℤ) ≤ (i : ℤ)*(g : ℤ) := by positivity
  have hmulBound : (i : ℤ)*(g : ℤ) < (n : ℤ) := by exact_mod_cast hidx
  light_side [haddr,hr]

def upperBody : Stmt :=
  .for 5 (v 4) (
    .set 6 ((v 5 +' k 1) *' v 2) ;;
    .ite (v 1 <' v 6) (.set 6 (v 1)) .skip ;;
    .store (v 3 +' v 5) (M (v 0 +' v 6 -' k 1)))

def upperTime (m : ℕ) : ℕ := 100*m+6

theorem upper_meets {p src dst n g d : ℕ} (hp : P[p]? = some upperBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hdst : dst+size n g ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) :
    Meets lim P p d [src,n,g,dst,size n g] μ (upperTime (size n g))
      (fun _ μ' => (∀ i < size n g, μ' (dst+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (size n g)) := by
  let F := fun i => f (stop n g i-1)
  apply Meets.of_body hp
  unfold upperBody upperTime
  refine Ends.for
    (fun i σ => ∃ q : ℕ,
      σ = ⟨frame [src,n,g,dst,size n g,i,q],wrote μ dst F i⟩)
    (size n g) 92 ?start ?round ?done ?bound
  case start =>
    refine ⟨0,?_⟩
    simp [update_frame_setLocal,wrote_zero]
    simpa using (frame_append_zeros [src,n,g,dst,size n g,0] 1).symm
  case round =>
    rintro i _ hi _ ⟨q,rfl⟩
    have hidx : i*g < n := start_lt hg hi
    have hsmall : size n g ≤ n := size_le _ _
    have hnextBound : (i+1)*g ≤ n+g := by nlinarith
    have hnextNonneg : (0 : ℤ) ≤ ((i : ℤ)+1)*(g : ℤ) := by positivity
    have hnextWord : ((i : ℤ)+1)*(g : ℤ) ≤ lim.word := by
      exact (by exact_mod_cast (show (i+1)*g ≤ n+g+2 by omega) :
        ((i : ℤ)+1)*(g : ℤ) ≤ ((n+g+2 : ℕ) : ℤ)).trans hword
    have hstopN := stop_le n g i
    have hstopPos : 0 < stop n g i := by have := start_lt_stop hg hi; omega
    have hstopI := stop_sub_one_lt hg hi
    have hstore (q : ℕ) (hq : q = stop n g i) :
        Ends lim P d (.store (v 3 +' v 5) (M (v 0 +' v 6 -' k 1)))
          ⟨frame [src,n,g,dst,size n g,i,q],wrote μ dst F i⟩ 40
          (fun σ => σ.loc 5 = (i : ℤ) ∧ ∃ r : ℕ,
            {σ with loc := Function.update σ.loc 5 ((i : ℤ)+1)} =
              ⟨frame [src,n,g,dst,size n g,i+1,r],wrote μ dst F (i+1)⟩) := by
      subst q
      have haddr : ((src : ℤ)+(stop n g i : ℤ)-1).toNat = src+(stop n g i-1) := by
        rw [show (src : ℤ)+(stop n g i : ℤ)-1 = ((src+(stop n g i-1) : ℕ) : ℤ) by omega,
          Int.toNat_natCast]
      have hr : wrote μ dst F i (src+(stop n g i-1)) = F i := by
        rw [wrote_rest (by omega)]
        exact hread _ hstopI
      light_store (dst+i) (F i) using haddr,hr
      exact ⟨by simp,stop n g i,by simp [update_frame_setLocal,wrote_succ]⟩
    light_set ((i+1)*g : ℕ)
    light_if hn hn : (n : ℤ) < (((i+1)*g : ℕ) : ℤ)
    · have hmin : stop n g i = n := by unfold stop; omega
      light_set (n : ℕ)
      light_piece (hstore n hmin.symm)
    · have hmin : stop n g i = (i+1)*g := by unfold stop; omega
      light_piece (hstore ((i+1)*g) hmin.symm)
  case done =>
    rintro _ _ ⟨q,rfl⟩
    exact ⟨fun i hi => wrote_done (μ := μ) (dst := dst) (f := F) hi,by light_keep⟩
  case bound =>
    rintro i _ _ _ ⟨q,rfl⟩
    simp

def body (pDivide pLower pUpper : ℕ) : Stmt :=
  .ite (k 0 <' v 1)
    (.call pDivide [v 1 -' k 1,v 2] 4 ;;
      .set 4 (v 4 +' k 1) ;;
      .set 5 (v 3 +' v 1) ;;
      .call pLower [v 0,v 3,v 4,v 2] 6 ;;
      .call pUpper [v 0,v 1,v 2,v 5,v 4] 6 ;;
      .set 0 (v 4))
    (.set 0 (k 0))

def time (n g : ℕ) : ℕ :=
  LightSmallDivide.time (n-1) g+lowerTime (size n g)+upperTime (size n g)+100

theorem meets {pMain pDivide pLower pUpper src dst n g d : ℕ}
    (hmain : P[pMain]? = some (body pDivide pLower pUpper))
    (hdiv : P[pDivide]? = some LightSmallDivide.body)
    (hlower : P[pLower]? = some lowerBody) (hupper : P[pUpper]? = some upperBody)
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hspace : dst+2*n ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hd : d+1 ≤ lim.depth) :
    Meets lim P pMain d [src,n,g,dst] μ (time n g)
      (fun r μ' => r = (size n g : ℤ) ∧
        (∀ i < size n g, μ' (dst+i) = f (start g i)) ∧
        (∀ i < size n g, μ' (dst+n+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (2*n)) := by
  have hm := size_le n g
  have hdv := Nat.div_le_self (n-1) g
  apply Meets.of_body hmain
  unfold body time
  light_if hn hn : (0 : ℤ) < (n : ℤ) using lowerTime,upperTime,LightSmallDivide.time
  · have hnN : n ≠ 0 := by omega
    have hmval : size n g = (n-1)/g+1 := by simp [size,hnN]
    light_call (LightSmallDivide.meets (d := d+1) (a := n-1) (b := g) hdiv μ
      ((Int.ofNat_le.mpr (by omega : n-1+g+2 ≤ n+g+2)).trans hword))
      using lowerTime,upperTime,LightSmallDivide.time with q μ₀ ⟨hq,hmem₀⟩
    subst μ₀
    light_set (size n g : ℕ) using hmval,hq,lowerTime,upperTime,LightSmallDivide.time
    light_set (dst+n : ℕ) using lowerTime,upperTime,LightSmallDivide.time
    light_call (lower_meets (d := d+1) hlower μ f hw hg hsrc (by omega) hread)
      using lowerTime,upperTime,LightSmallDivide.time with unused μ₁ ⟨hlo,hkeep₁⟩
    have hread₁ : ∀ i < n, μ₁ (src+i) = f i := by
      intro i hi
      rw [hkeep₁ (src+i) (Or.inl (by omega))]
      exact hread i hi
    light_call (upper_meets (d := d+1) (dst := dst+n) hupper μ₁ f hw hg
      (by omega) (by omega) hword hread₁)
      using lowerTime,upperTime,LightSmallDivide.time with unused μ₂ ⟨hhi,hkeep₂⟩
    light_set (size n g : ℕ) using lowerTime,upperTime,LightSmallDivide.time
    refine ⟨rfl,?_,hhi,?_⟩
    · intro i hi
      change μ₂ (dst+i) = _
      rw [hkeep₂ (dst+i) (Or.inl (by omega))]
      exact hlo i hi
    · intro a ha
      change μ₂ a = μ a
      rw [hkeep₂ a (by omega),hkeep₁ a (by omega)]
  · have hnN : n = 0 := by omega
    light_set (0 : ℕ) using lowerTime,upperTime,LightSmallDivide.time
    refine ⟨by simp [size,hnN],?_,?_,SameOutside.refl⟩ <;> simp [size,hnN]

def program : Program := [body 1 2 3,LightSmallDivide.body,lowerBody,upperBody]

theorem program_meets {src dst n g d : ℕ} (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hg : 0 < g)
    (hsrc : src+n ≤ dst) (hspace : dst+2*n ≤ lim.space)
    (hword : ((n+g+2 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (src+i) = f i) (hd : d+1 ≤ lim.depth) :
    Meets lim program 0 d [src,n,g,dst] μ (time n g)
      (fun r μ' => r = (size n g : ℤ) ∧
        (∀ i < size n g, μ' (dst+i) = f (start g i)) ∧
        (∀ i < size n g, μ' (dst+n+i) = f (stop n g i-1)) ∧
        SameOutside μ μ' dst (2*n)) :=
  meets rfl rfl rfl rfl μ f hw hg hsrc hspace hword hread hd

theorem time_bound (n g : ℕ) : time n g ≤ 200*n+200 := by
  have hm := size_le n g
  have hdiv := LightSmallDivide.time_bound (n-1) g
  have hsub : n-1 ≤ n := Nat.sub_le _ _
  unfold time lowerTime upperTime
  omega

end ThreeSum.LightBandPartition
