import Submission.ThreeSum.LightRadixDigit
import Submission.ThreeSum.WeightEnumeration
import Submission.ThreeSumApsp.Lang.Lib.PowTable

/-!
# Actual little-endian coefficient decoding

The power table is ordinary memory. Each output coefficient is computed by
the checked radix-digit procedure; the caller supplies the table's exact
contents and this procedure preserves every cell outside its output row.
-/

namespace ThreeSum.LightCoefficientDecode

open Light

set_option maxHeartbeats 1200000

def digit (p code coordinate : ℕ) : ℕ := code/p^coordinate%p

def body (pDigit : ℕ) : Stmt :=
  .for 8 (v 7) (
    .call pDigit [v 2,M (v 3 +' (v 4 +' v 5 *' v 8)),v 1] 9 ;;
    .store (v 6 +' v 8) (v 9))

def time (n k : ℕ) : ℕ := n*(LightRadixDigit.time k+100)+6
def word (W p k start stride : ℕ) : ℕ :=
  4*(k+p^(W+1)+p+W+start+stride+2)

def Inv (μ : ℕ → ℤ) (W p k powers start stride dst n i : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,p,k,powers,start,stride,dst,n,i,r],μ'⟩ ∧
    (∀ j < i, μ' (dst+j) = (digit p k (start+stride*j) : ℤ)) ∧
    SameOutside μ μ' dst n

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pDigit pDivide : ℕ}
    (hmain : P[pMain]? = some (body pDigit))
    (hdigit : P[pDigit]? = some (LightRadixDigit.body pDivide))
    (hdivide : P[pDivide]? = some LightSmallDivide.body)
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : Apart powers (W+1) dst n)
    (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    Meets lim P pMain d [W,p,k,powers,start,stride,dst,n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (digit p k (start+stride*i) : ℤ)) ∧
        SameOutside μ μ' dst n) := by
  have hbudget (x : ℕ) (hx : x ≤ word W p k start stride) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hkWord := hbudget k (by unfold word; omega)
  have hpWord := hbudget p (by unfold word; omega)
  have hstrideWord := hbudget stride (by unfold word; omega)
  have hstartWord := hbudget start (by unfold word; omega)
  have hWWord := hbudget W (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ W p k powers start stride dst n) n
    (LightRadixDigit.time k+92) ?_ ?_ ?_ ?_
  · refine ⟨0,μ,?_,?_,SameOutside.refl⟩
    · exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal _ _ _).trans (frame_append_zeros _ 1).symm)
    · intro i hi; omega
  · rintro i _ hi _ ⟨r,μ',rfl,written,kept⟩
    have hc := hcoords i hi
    let e := start+stride*i
    have he : e ≤ W := by unfold e; omega
    have hpbound : p^e ≤ p^(W+1) := Nat.pow_le_pow_right hp (by omega)
    have hpWord' := hbudget (p^e) (by unfold word; omega)
    have hmulWord : (stride : ℤ)*i ≤ lim.word := by
      have hh : stride*i ≤ W := by omega
      exact (by exact_mod_cast hh : (stride : ℤ)*i ≤ (W : ℤ)).trans hWWord
    have hmulNonneg : (0 : ℤ) ≤ (stride : ℤ)*i := by positivity
    have hcZ : (start : ℤ)+(stride : ℤ)*i < W := by exact_mod_cast hc
    have haddr : ((powers : ℤ)+((start : ℤ)+(stride : ℤ)*i)).toNat = powers+e := by
      unfold e
      norm_cast
    have hpower : μ' (powers+e) = ((p^e : ℕ) : ℤ) := by
      rw [kept _ (by omega)]
      exact hread e he
    have hcallWord : (LightRadixDigit.word k (p^e) p : ℤ) ≤ lim.word := by
      apply hbudget
      unfold LightRadixDigit.word word
      omega
    have hcall := LightRadixDigit.meets (d := d+1) (k := k) (b := p^e) (p := p)
      hdigit hdivide μ' (by omega) hcallWord
    light_call hcall using haddr,hpower,e,LightRadixDigit.time
      with value μ₁ ⟨hvalue,hmem⟩
    subst μ₁
    have hv : value = (digit p k (start+stride*i) : ℤ) := hvalue
    have hvBound : digit p k (start+stride*i) ≤ k :=
      (Nat.mod_le _ _).trans (Nat.div_le_self _ _)
    have hvWord : (digit p k (start+stride*i) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hvBound).trans hkWord
    light_store (dst+i) (digit p k (start+stride*i) : ℕ)
      using hv,LightRadixDigit.time
    refine ⟨by simp,value,
      Function.update μ' (dst+i) (digit p k (start+stride*i) : ℤ),
      by simp [update_frame_setLocal],?_,kept.update ⟨by omega,by omega⟩ _⟩
    intro j hj
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
    · rw [Function.update_of_ne (by omega)]
      exact written j hj
    · simp
  · rintro _ _ ⟨r,μ',rfl,written,kept⟩
    exact ⟨written,kept⟩
  · rintro i _ _ _ ⟨r,μ',rfl,_,_⟩
    light_side

def program : Program := [body 1,LightRadixDigit.body 2,LightSmallDivide.body]

theorem program_meets
    {μ : ℕ → ℤ} {W p k powers start stride dst n : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth) (hp : 1 ≤ p)
    (hspace : dst+n ≤ lim.space) (hpowers : powers+(W+1) ≤ lim.space)
    (hsep : Apart powers (W+1) dst n)
    (hword : (word W p k start stride : ℤ) ≤ lim.word)
    (hcoords : ∀ i < n, start+stride*i < W)
    (hread : ∀ e ≤ W, μ (powers+e) = ((p^e : ℕ) : ℤ)) :
    Meets lim program 0 d [W,p,k,powers,start,stride,dst,n] μ (time n k)
      (fun _ μ' =>
        (∀ i < n, μ' (dst+i) = (digit p k (start+stride*i) : ℤ)) ∧
        SameOutside μ μ' dst n) :=
  meets rfl rfl rfl hw hd hp hspace hpowers hsep hword hcoords hread

end ThreeSum.LightCoefficientDecode
