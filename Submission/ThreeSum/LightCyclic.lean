import Submission.ThreeSum.CyclicFold
import Submission.ThreeSum.KaratsubaInterface

/-!
# Costed folding of the verified polynomial product

The ordinary linear array procedure adds coefficients `r` and `r+p` for
each output residue. Its specification is the exact natural cyclic
correlation, including histogram multiplicities.
-/

namespace ThreeSum.LightCyclic

open Light Karatsuba CyclicFold LightKaratsuba

variable {lim : Limits} {P : Program} {d : ℕ}

theorem fold_meets {pLinear : ℕ} (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} {as bs : List ℤ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (ha : as.length ≤ p) (hb : bs.length ≤ p)
    (hA : CoeffBound as (U : ℤ)) (hB : CoeffBound bs (U : ℤ))
    (hprod : ProductAt μ src n (padTo n as) (padTo n bs))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) = cyclic p as bs r) ∧
        SameOutside μ μ' dst p := by
  have hfirst (r : ℕ) (hr : r < p) :
      μ (src+r) = (asPolynomial as * asPolynomial bs).coeff r := by
    simpa only [asPolynomial_padTo] using hprod r (by omega)
  have hsecond (r : ℕ) (hr : r < p) :
      μ (src+p+r) = (asPolynomial as * asPolynomial bs).coeff (r+p) := by
    simpa only [asPolynomial_padTo, Nat.add_assoc, Nat.add_comm p r] using
      hprod (r+p) (by omega)
  have hc (r : ℕ) :
      |(asPolynomial as * asPolynomial bs).coeff r| ≤ (2*p*U^2 : ℕ) := by
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      product_coeff_bound ha hb hA hB r
  have h := LightArray.linear_bounded_meets (d := d) (μ := μ)
    (srcA := src) (srcB := src+p) (dst := dst) (n := p) (U := 2*p*U^2) (c := 1)
    hLinear hw (by omega) (by omega) hdst (Or.inr (by omega)) (Or.inr (by omega))
    (by norm_num) (by push_cast; nlinarith) (by
      intro r hr
      rw [hfirst r hr, hsecond r hr]
      exact ⟨hc r, hc (r+p)⟩)
  apply h.mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr, one_mul, hfirst r hr, hsecond r hr]
  exact fold_product as bs p r ha hb hr

theorem fold_correlation_meets {pLinear : ℕ}
    (hLinear : P[pLinear]? = some LightArray.linearBody)
    {μ : ℕ → ℤ} {src dst n p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ n)
    (hsrc : src + 2*n ≤ lim.space) (hdst : dst + p ≤ lim.space)
    (hsep : Apart src (2*n) dst p)
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (hprod : ProductAt μ src n (padTo n (vector p F))
      (padTo n (vector p (fun z => H (-z)))))
    (hword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word) :
    Meets lim P pLinear d [src, src+p, dst, p, 1] μ (LightArray.linearTime p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧ SameOutside μ μ' dst p := by
  apply (fold_meets hLinear hw hpn hsrc hdst hsep
    (le_of_eq (vector_length _ _)) (le_of_eq (vector_length _ _)) hA hB hprod hword).mono le_rfl
  intro res μ' hpost
  refine ⟨?_, hpost.2⟩
  intro r hr
  rw [hpost.1 r hr]
  exact cyclic_correlation F H r hr

/-- Arguments: capacity, left array, right array, product array, output
array, Karatsuba scratch, and cyclic modulus. -/
def body (pMultiply pLinear : ℕ) : Stmt :=
  .call pMultiply [v 0, v 1, v 2, v 3, v 5] 7 ;;
  .call pLinear [v 3, v 3 +' v 6, v 4, v 6, k 1] 7

def combinedTime (k p : ℕ) : ℕ := LightKaratsuba.time k + LightArray.linearTime p + 100

theorem correlation_meets {pThis pMultiply pHalf pLinear pFill : ℕ}
    (hThis : P[pThis]? = some (body pMultiply pLinear))
    (C : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2^k ≤ work) (hbf : b + 2^k ≤ work)
    (hpf : prod + 2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+2 ≤ lim.depth) :
    Meets lim P pThis d [2^k, a, b, prod, dst, work, p] μ (combinedTime k p)
      fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by
  have hn : 0 < (2 : ℕ)^k := Nat.pow_pos (by decide)
  have hAlen : (padTo (2^k) (vector p F)).length = 2^k :=
    padTo_length _ _ (by rw [vector_length]; exact hpn)
  have hBlen : (padTo (2^k) (vector p (fun z => H (-z)))).length = 2^k :=
    padTo_length _ _ (by rw [vector_length]; exact hpn)
  have hfoldword : 4 * (p : ℤ) * (U : ℤ)^2 ≤ lim.word := by
    have ht := LightKaratsuba.ten_temp_le_word (2^k) U hn
    have hpU := Nat.mul_le_mul_right (U^2) (Nat.mul_le_mul_left 4 hpn)
    have ht' : 4*p*U^2 ≤ LightKaratsuba.wordBound (2^k) U := by nlinarith
    exact (by exact_mod_cast ht' : 4 * (p : ℤ) * (U : ℤ)^2 ≤
      (LightKaratsuba.wordBound (2^k) U : ℤ)).trans hword
  apply Meets.of_body hThis
  unfold body combinedTime
  light_call (LightKaratsuba.meets C hw hAlen hBlen hAseg hBseg
    (coeffBound_padTo hA (2^k)) (coeffBound_padTo hB (2^k))
    haf hbf hpf hspace hword (d+1) (by omega)) with res μ₁ hK
  light_call (fold_correlation_meets C.linear (μ := μ₁) (n := 2^k)
    F H hw hpn (by omega) (by omega) hsep hA hB hK.1 hfoldword)
    with res₂ μ₂ hF
  refine ⟨hF.1, ?_⟩
  intro j hj hpj hdj
  exact (hF.2 j hdj).trans (hK.2 j ⟨hj, hpj⟩)

theorem combinedTime_bound (k p : ℕ) (hp : p ≤ 2^k) :
    combinedTime k p ≤ LightKaratsuba.time k + 106 * 2^k + 106 := by
  unfold combinedTime LightArray.linearTime
  omega

/-- A fixed five-procedure program: correlation, multiplication, half,
linear combination, and fill. -/
def program : Program :=
  [body 1 3, LightKaratsuba.body 1 2 3 4, halfBody, LightArray.linearBody, fillBody]

theorem program_procs : LightKaratsuba.Procs program 1 2 3 4 := ⟨rfl, rfl, rfl, rfl⟩

theorem program_meets
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a + 2^k ≤ work) (hbf : b + 2^k ≤ work)
    (hpf : prod + 2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+2 ≤ lim.depth) :
    Meets lim program 0 d [2^k, a, b, prod, dst, work, p] μ (combinedTime k p)
      (fun _ μ' => (∀ r < p, μ' (dst+r) =
        (Balancing.correlation F H (r : ZMod p) : ℤ)) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j)) :=
  correlation_meets rfl program_procs F H hw hpn hAseg hBseg hA hB
    haf hbf hpf hdf hsep hspace hword hd

theorem rounded_time_fifth_power {p : ℕ} (hp : 0 < p) :
    combinedTime (Nat.clog 2 p) p ^ 5 ≤
      ((2530+2*106)^5 * 2^8) * p^8 := by
  exact (Nat.pow_le_pow_left
    (combinedTime_bound _ _ (KaratsubaInterface.le_capacity p)) 5).trans
      (KaratsubaInterface.rounded_time_fifth_power hp 106)

end ThreeSum.LightCyclic
