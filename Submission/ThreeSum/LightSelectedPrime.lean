import Submission.ThreeSum.LightPrimePool
import Submission.ThreeSum.LocalCoverBounds
import Submission.ThreeSumApsp.Lang.Lib.Sqrt

/-!
# Executing the deterministic square-root prime selection

The candidate pool is scanned by the verified primality program. Its first
entry is exactly the minimum used by `LocalCoverBounds.selectedPrime`.
The input threshold is positive; the routine has no primality oracle or
externally supplied list of candidates.
-/

namespace ThreeSum.LightSelectedPrime

open Light LocalCoverBounds LightResidues

set_option maxHeartbeats 1000000

theorem prime_zero_eq_selectedPrime (N : ℕ) :
    LightPrimePool.prime (rootCeiling N) 0 = selectedPrime N := by
  apply Nat.le_antisymm
  · have hs := selectedPrime_spec N
    apply LightPrimePool.prime_zero_le_mem
    exact LightPrimePool.mem_values.mpr ⟨hs.1,hs.2.1,by omega⟩
  · unfold selectedPrime
    apply Finset.min'_le
    exact mem_primeCandidates.mpr
      (LightPrimePool.prime_zero_spec (rootCeiling_pos N))

def body (pSqrt pPool : ℕ) : Stmt :=
  .call pSqrt [v 0 -' k 1] 2 ;;
  .set 3 (v 2 +' k 1) ;;
  .call pPool [v 3,v 1] 4 ;;
  .set 0 (M (v 1))

def time (N : ℕ) : ℕ := sqrtTime (N-1)+LightPrimePool.time (rootCeiling N)+100
def space (free N : ℕ) : ℕ := LightPrimePool.space free (rootCeiling N)
def word (N : ℕ) : ℕ := 100*(N+1)

structure Procs (P : Program) (pMain : ℕ) where
  pSqrt : ℕ
  pPool : ℕ
  sqrt : P[pSqrt]? = some sqrtBody
  pool : LightPrimePool.Procs P pPool
  main : P[pMain]? = some (body pSqrt pPool)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {N free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hN : 0 < N) (hspace : space free N ≤ lim.space)
    (hword : (word N : ℤ) ≤ lim.word) :
    Meets lim P pMain d [N,free] μ (time N)
      (fun r μ' => r = (selectedPrime N : ℤ) ∧
        SegN μ' free (LightPrimePool.values (rootCeiling N)) ∧ Kept μ μ' free) := by
  have hypos := rootCeiling_pos N
  have hy : rootCeiling N ≤ N+1 := by
    unfold rootCeiling
    have hh := Nat.sqrt_le_self (N-1)
    omega
  have hwordZ : 100*((N : ℤ)+1) ≤ lim.word := by exact_mod_cast hword
  have hsub : (N : ℤ)-1 = ((N-1 : ℕ) : ℤ) := by omega
  have hrootWord : (rootCeiling N : ℤ) ≤ lim.word := by omega
  have hpoolWord : (LightPrimePool.word (rootCeiling N) : ℤ) ≤ lim.word := by
    unfold LightPrimePool.word
    push_cast
    omega
  have hfree : free < lim.space := by
    unfold space LightPrimePool.space at hspace
    omega
  have hselectedWord : (selectedPrime N : ℤ) ≤ lim.word := by
    have hp := (selectedPrime_spec N).2.2
    omega
  apply Meets.of_body S.main
  unfold body time
  light_call (sqrt_meets (d := d+1) (K := N-1) S.sqrt μ (by omega))
    using hsub,LightPrimePool.time with root μ₁ ⟨hr,hmem₁⟩
  subst μ₁
  have hr' : root+1 = (rootCeiling N : ℤ) := by
    simpa [rootCeiling] using congrArg (fun z : ℤ => z+1) hr
  light_set (rootCeiling N : ℕ) using hr',LightPrimePool.time
  light_call (S.pool.meets (d := d+1) hw hd hypos hspace hpoolWord)
    using LightPrimePool.time with count μ₂ ⟨hc,hseg,hkept⟩
  have hlen : 0 < (LightPrimePool.values (rootCeiling N)).length :=
    LightPrimePool.size_pos hypos
  have hfirst : μ₂ free = (selectedPrime N : ℤ) := by
    have hh := hseg 0 (by simp; exact hlen)
    rw [← prime_zero_eq_selectedPrime]
    change μ₂ free = ((LightPrimePool.values (rootCeiling N)).getD 0 0 : ℤ)
    rw [List.getD_eq_getElem _ _ hlen]
    simpa using hh
  light_set (selectedPrime N : ℕ) using hfirst,LightPrimePool.time
  exact ⟨rfl,hseg,hkept⟩

def program : Program :=
  [body 1 2,sqrtBody,LightPrimePool.body 3,
    LightPrimality.body 4,emodBody]

def procs : Procs program 0 :=
  ⟨1,2,rfl,⟨3,⟨4,rfl,rfl⟩,rfl⟩,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {N free : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hN : 0 < N) (hspace : space free N ≤ lim.space)
    (hword : (word N : ℤ) ≤ lim.word) :
    Meets lim program 0 d [N,free] μ (time N)
      (fun r μ' => r = (selectedPrime N : ℤ) ∧
        SegN μ' free (LightPrimePool.values (rootCeiling N)) ∧ Kept μ μ' free) :=
  procs.meets hw hd hN hspace hword

theorem pool_time_bound (y : ℕ) : LightPrimePool.time y ≤ 5000*(y+1)^3 := by
  have hlog := Nat.log_le_self 2 (4*y+1)
  have hres : residueBudget (4*y)+70 ≤ 172*y+190 := by
    unfold residueBudget
    omega
  have hprim : LightPrimality.time (4*y) (4*y) ≤ 4*y*(172*y+190)+70 := by
    unfold LightPrimality.time
    exact Nat.add_le_add_right
      (Nat.mul_le_mul (Nat.sub_le _ _) hres) _
  have hpool : LightPrimePool.time y ≤ 3*y*(4*y*(172*y+190)+170)+100 := by
    unfold LightPrimePool.time
    apply Nat.add_le_add_right
    apply Nat.mul_le_mul_left
    omega
  exact hpool.trans (by nlinarith [Nat.zero_le (y^3),Nat.zero_le (y^2)])

theorem time_bound (N : ℕ) : time N ≤ 6000*(N+2)^3 := by
  have hy : rootCeiling N ≤ N+1 := by
    unfold rootCeiling
    have hh := Nat.sqrt_le_self (N-1)
    omega
  have hp := pool_time_bound (rootCeiling N)
  have hs := Nat.sqrt_le_self (N-1)
  have hpow := Nat.pow_le_pow_left (show rootCeiling N+1 ≤ N+2 by omega) 3
  have hp' : LightPrimePool.time (rootCeiling N) ≤ 5000*(N+2)^3 :=
    hp.trans (Nat.mul_le_mul_left _ hpow)
  have hlinear : 18*Nat.sqrt (N-1)+112 ≤ 1000*(N+2)^3 := by
    have hl : 18*Nat.sqrt (N-1)+112 ≤ 1000*(N+2) := by omega
    exact hl.trans (Nat.mul_le_mul_left _ (Nat.le_self_pow (by decide : 3 ≠ 0) (N+2)))
  unfold time sqrtTime
  omega

end ThreeSum.LightSelectedPrime
