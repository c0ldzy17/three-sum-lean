import Submission.ThreeSum.LightCyclic
import Submission.ThreeSum.LightMinimum

/-!
# An actual minimum scan of the fast cyclic correlation

The returned offset obeys the exact mean bound for the supplied histograms.
The choice is made by a fixed program, not by an existential witness in the
proof. The histograms themselves are the procedure's array inputs.
-/

namespace ThreeSum.LightBalancedOffset

open Light Karatsuba CyclicFold LightKaratsuba Finset
open scoped BigOperators

def offset {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : ℕ :=
  LightMinimum.least (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) p

theorem offset_lt {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) : offset F H < p :=
  LightMinimum.least_lt _ (Nat.pos_of_ne_zero (NeZero.ne p))

theorem offset_balanced {p : ℕ} [NeZero p] (F H : ZMod p → ℕ) :
    p * Balancing.correlation F H (offset F H : ZMod p) ≤
      (∑ z, F z) * (∑ z, H z) := by
  obtain ⟨z, hz⟩ := Balancing.exists_balanced_offset F H
  have hmin := LightMinimum.least_value_le
    (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) p z.val (ZMod.val_lt z)
  have hminNat : Balancing.correlation F H (offset F H : ZMod p) ≤
      Balancing.correlation F H z := by
    simpa only [offset, ZMod.natCast_zmod_val, Nat.cast_le] using hmin
  have hcard : Fintype.card (ZMod p) = p := ZMod.card p
  rw [hcard] at hz
  exact (Nat.mul_le_mul_left p hminNat).trans hz

def body (pCyclic pMinimum : ℕ) : Stmt :=
  .call pCyclic [v 0, v 1, v 2, v 3, v 4, v 5, v 6] 7 ;;
  .call pMinimum [v 4, v 6] 0

def time (k p : ℕ) : ℕ :=
  LightCyclic.combinedTime k p + LightMinimum.time p + 100

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pCyclic pMinimum pMultiply pHalf pLinear pFill : ℕ}
    (hmain : P[pMain]? = some (body pCyclic pMinimum))
    (hcyclic : P[pCyclic]? = some (LightCyclic.body pMultiply pLinear))
    (hminimum : P[pMinimum]? = some LightMinimum.body)
    (K : LightKaratsuba.Procs P pMultiply pHalf pLinear pFill)
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a+2^k ≤ work) (hbf : b+2^k ≤ work)
    (hpf : prod+2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+3 ≤ lim.depth) :
    Meets lim P pMain d [2^k,a,b,prod,dst,work,p] μ (time k p)
      fun r μ' => r = (offset F H : ℤ) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j) := by
  have hp : 0 < p := Nat.pos_of_ne_zero (NeZero.ne p)
  apply Meets.of_body hmain
  unfold body time
  light_call (LightCyclic.correlation_meets (d := d+1) hcyclic K F H hw hpn
    hAseg hBseg hA hB haf hbf hpf hdf hsep hspace hword (by omega))
    with _ μ₁ ⟨hcorr, hkeep⟩
  light_call (LightMinimum.meets (d := d+1) (src := dst) (n := p) hminimum
    (fun r => (Balancing.correlation F H (r : ZMod p) : ℤ)) hw hp (by omega) hcorr)
    with result μ₂ ⟨hresult, hmem⟩
  subst μ₂
  exact ⟨by change result = _; exact hresult, hkeep⟩

def program : Program :=
  [body 1 6, LightCyclic.body 2 4, LightKaratsuba.body 2 3 4 5,
    halfBody, LightArray.linearBody, fillBody, LightMinimum.body]

theorem program_meets
    {μ : ℕ → ℤ} {k a b prod dst work p U : ℕ} [NeZero p]
    (F H : ZMod p → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hpn : p ≤ 2^k)
    (hAseg : Seg μ a (padTo (2^k) (vector p F)))
    (hBseg : Seg μ b (padTo (2^k) (vector p (fun z => H (-z)))))
    (hA : CoeffBound (vector p F) (U : ℤ))
    (hB : CoeffBound (vector p (fun z => H (-z))) (U : ℤ))
    (haf : a+2^k ≤ work) (hbf : b+2^k ≤ work)
    (hpf : prod+2*2^k ≤ work) (hdf : dst+p ≤ work)
    (hsep : Apart prod (2*2^k) dst p)
    (hspace : work+8*2^k ≤ lim.space)
    (hword : (LightKaratsuba.wordBound (2^k) U : ℤ) ≤ lim.word)
    (hd : d+k+3 ≤ lim.depth) :
    Meets lim program 0 d [2^k,a,b,prod,dst,work,p] μ (time k p)
      (fun r μ' => r = (offset F H : ℤ) ∧
        (∀ j < work, (j < prod ∨ prod+2*2^k ≤ j) →
          (j < dst ∨ dst+p ≤ j) → μ' j = μ j)) :=
  meets rfl rfl rfl ⟨rfl, rfl, rfl, rfl⟩ F H hw hpn
    hAseg hBseg hA hB haf hbf hpf hdf hsep hspace hword hd

theorem time_bound (k p : ℕ) (hp : p ≤ 2^k) :
    time k p ≤ LightKaratsuba.time k + 226*2^k + 226 := by
  unfold time LightCyclic.combinedTime LightMinimum.time LightArray.linearTime
  omega

theorem rounded_time_fifth_power {p : ℕ} (hp : 0 < p) :
    time (Nat.clog 2 p) p ^ 5 ≤ ((2530+2*226)^5*2^8)*p^8 := by
  exact (Nat.pow_le_pow_left (time_bound _ _ (KaratsubaInterface.le_capacity p)) 5).trans
    (KaratsubaInterface.rounded_time_fifth_power hp 226)

end ThreeSum.LightBalancedOffset
