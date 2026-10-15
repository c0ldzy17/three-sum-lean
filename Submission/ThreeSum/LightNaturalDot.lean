import Submission.ThreeSum.LightBooleanDot
import Submission.ThreeSum.LightRadixDigit

namespace ThreeSum.LightNaturalDot
open Light Finset
open scoped BigOperators

abbrev dot := LightBooleanDot.dot
abbrev body := LightBooleanDot.body
abbrev loopBody := LightBooleanDot.loopBody
abbrev time := LightBooleanDot.time

theorem dot_le (f g : ℕ → ℕ) {n j U V : ℕ}
    (hf : ∀ i<n, f i≤U) (hg : ∀ i<n, g i≤V) (hj : j≤n) :
    dot f g j≤j*(U*V) := by
  unfold dot LightBooleanDot.dot
  calc
    ∑ i ∈ range j, f i*g i≤∑ _i ∈ range j, U*V := by
      apply sum_le_sum
      intro i hi
      have hin := (mem_range.mp hi).trans_le hj
      exact Nat.mul_le_mul (hf i hin) (hg i hin)
    _ = _ := by simp

variable {lim : Limits} {P : Program} {depth : ℕ}

theorem meets {proc srcA srcB n U V : ℕ} (hp : P[proc]?=some body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hA : srcA+n≤lim.space) (hB : srcB+n≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<n, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i≤U) (hg : ∀ i<n, g i≤V)
    (hword : (((n+1)*(U+1)*(V+1)+10 : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n] μ (time n)
      (fun r ν => r=(dot f g n : ℤ) ∧ ν=μ) := by
  have hprod : U*V≤(U+1)*(V+1) := Nat.mul_le_mul (by omega) (by omega)
  have hsum : n*(U*V)≤(n+1)*(U+1)*(V+1)+10 := by
    have hh := Nat.mul_le_mul (show n≤n+1 by omega) hprod
    simpa only [Nat.mul_assoc] using hh.trans (Nat.le_add_right _ 10)
  have hbudget (z : ℕ) (hz : z≤(n+1)*(U+1)*(V+1)+10) : (z : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hfit (j : ℕ) (hj : j≤n) : (dot f g j : ℤ)≤lim.word :=
    hbudget _ ((dot_le f g hf hg hj).trans ((Nat.mul_le_mul_right (U*V) hj).trans hsum))
  apply Meets.of_body hp
  unfold body LightBooleanDot.body time LightBooleanDot.time
  light_set (0 : ℕ)
  refine Ends.pieceThen (Ends.for (T := 32*n+6)
    (Q := fun σ => σ=⟨frame [srcA,srcB,n,dot f g n,n],μ⟩)
    (fun j σ => σ=⟨frame [srcA,srcB,n,dot f g j,j],μ⟩)
    n 24 ?start ?round ?done ?bound (hT := by light_time)) ?finish
  case start => simp [LightBooleanDot.dot_zero,update_frame_setLocal]
  case round =>
    rintro j _ hj _ rfl
    have ha := hreadA j hj
    have hb := hreadB j hj
    have hmul : f j*g j≤n*(U*V) := by
      exact (Nat.mul_le_mul (hf j hj) (hg j hj)).trans (Nat.le_mul_of_pos_left _ (by omega))
    have hmulWord : ((f j*g j : ℕ) : ℤ)≤lim.word := hbudget _ (hmul.trans hsum)
    have hs0 := hfit j (by omega)
    have hs1 := hfit (j+1) (by omega)
    have hsCast : (dot f g j : ℤ)+(f j : ℤ)*(g j : ℤ)=(dot f g (j+1) : ℤ) := by
      simp [LightBooleanDot.dot_succ]
    unfold LightBooleanDot.loopBody
    refine Ends.setLast ?_ (hs := by light_side [ha,hb,hsCast]) (hT := by light_time)
    simp [ha,hb,hsCast,update_frame_setLocal]
  case done => intro σ hcounter hshape; exact hshape
  case bound => rintro j _ hj _ rfl; light_side
  case finish =>
    intro σ hshape
    rw [hshape]
    light_set (dot f g n : ℕ)
    exact ⟨rfl,rfl⟩

def reducedBody (pDot pDigit : ℕ) : Stmt :=
  .call pDot [v 0,v 1,v 2] 4 ;; .call pDigit [v 4,k 1,v 3] 0

def reducedTime (n U V : ℕ) : ℕ := time n+40*(n*(U*V)+1)+200

theorem reduced_meets {proc pDot pDigit pDivide srcA srcB n p U V : ℕ}
    (hmain : P[proc]?=some (reducedBody pDot pDigit))
    (hdot : P[pDot]?=some body) (hdigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]?=some LightSmallDivide.body)
    (μ : ℕ → ℤ) (f g : ℕ → ℕ) (hw : (lim.space : ℤ)≤lim.word)
    (hd : depth+1<lim.depth)
    (hA : srcA+n≤lim.space) (hB : srcB+n≤lim.space)
    (hreadA : ∀ i<n, μ (srcA+i)=(f i : ℤ))
    (hreadB : ∀ i<n, μ (srcB+i)=(g i : ℤ))
    (hf : ∀ i<n, f i≤U) (hg : ∀ i<n, g i≤V)
    (hword : ((20*((n+1)*(U+1)*(V+1)+p+10) : ℕ) : ℤ)≤lim.word) :
    Meets lim P proc depth [srcA,srcB,n,p] μ (reducedTime n U V)
      (fun z ν => z=(((dot f g n)%p : ℕ) : ℤ) ∧ ν=μ) := by
  have hdotBound := dot_le f g hf hg (j := n) le_rfl
  have htotal : n*(U*V)≤(n+1)*(U+1)*(V+1) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul (show n≤n+1 by omega)
      (Nat.mul_le_mul (show U≤U+1 by omega) (show V≤V+1 by omega))
  have hwordDot : (((n+1)*(U+1)*(V+1)+10 : ℕ) : ℤ)≤lim.word := by omega
  have hwordDigit : (LightRadixDigit.word (dot f g n) 1 p : ℤ)≤lim.word := by
    apply le_trans (Int.ofNat_le.mpr ?_) hword
    unfold LightRadixDigit.word
    omega
  have hvalue : (dot f g n : ℤ)≤lim.word := by unfold LightRadixDigit.word at hwordDigit; omega
  have hpWord : (p : ℤ)≤lim.word := by unfold LightRadixDigit.word at hwordDigit; omega
  have h1 : (1 : ℤ)≤lim.word := by omega
  have htime : LightRadixDigit.time (dot f g n)≤40*(n*(U*V)+1)+100 := by
    unfold LightRadixDigit.time
    omega
  apply Meets.of_body hmain
  unfold reducedBody reducedTime
  light_call (meets (depth := depth+1) hdot μ f g hw hA hB hreadA hreadB hf hg hwordDot)
    using time,LightBooleanDot.time with z ν ⟨hz,hν⟩
  subst ν
  subst z
  light_call (LightRadixDigit.meets (d := depth+1) hdigit hdivide μ hd hwordDigit)
    using LightRadixDigit.time with z ν ⟨hz,hν⟩
  subst ν
  subst z
  simp

end ThreeSum.LightNaturalDot
