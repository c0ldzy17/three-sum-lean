import Submission.ThreeSum.TernaryPairedCarryBudget
import Submission.ThreeSum.TernaryPairedCollisionRate
import Submission.ThreeSum.LightTernaryRowSelector
import Submission.ThreeSum.TernaryPairedSupportConcrete
import Submission.ThreeSum.TernaryOriginalCollisions

noncomputable section
namespace ThreeSum.TernaryPairedSelectedChain
open Filter Real Finset TernaryPairedRecurrence TernaryPairedInitial TernaryPairedNativeDrift
open TernaryOversizePrime TernaryOversizeOverhead TernaryCoverScale TernaryLocalParameters TernaryCoverLocal
open TernaryEntropyRates
open TernarySignedPadding TernaryPairedPotential TernaryPairedSupportConcrete
open scoped Topology BigOperators
set_option maxHeartbeats 1000000

/-- The existence theorem feeds the literal scan used by the executable
selector. Every candidate is checked with its real admissibility bit. -/
theorem actual_pick_positive {N : ℕ} (S : Finset (Fin N)) (hS : S.Nonempty)
    (f : Fin 3→Fin N→ℕ) (num den : Fin 3→ℕ) (hd : ∀ i, 0<den i)
    (havg : ∀ i, den i*(∑ seed∈S, f i seed)≤3*S.card*num i)
    (flag : ℕ→ℤ) (values : Fin 3→ℕ→ℤ)
    (hflag : ∀ i : Fin N, flag i.val≠0 ↔ i∈S)
    (hvalues : ∀ j (i : Fin N), values j i.val=(f j i : ℤ)) :
    let good := LightTernaryRowSelector.Good flag (values 0) (values 1) (values 2)
      (den 0) (den 1) (den 2) (9*num 0) (9*num 1) (9*num 2)
    0<LightTernaryRowSelector.pick good N ∧
      good (LightTernaryRowSelector.pick good N-1) := by
  dsimp only
  let good := LightTernaryRowSelector.Good flag (values 0) (values 1) (values 2)
    (den 0) (den 1) (den 2) (9*num 0) (9*num 1) (9*num 2)
  obtain ⟨seed,hseed,hs⟩ := TernaryPairedSelector.exists_cross_multiplied S hS f num den hd havg
  have hgood : good seed.val := by
    refine ⟨(hflag seed).mpr hseed, ?_, ?_, ?_⟩
    · rw [hvalues]
      exact_mod_cast (by nlinarith [hs 0] : f 0 seed*den 0≤9*num 0)
    · rw [hvalues]
      exact_mod_cast (by nlinarith [hs 1] : f 1 seed*den 1≤9*num 1)
    · rw [hvalues]
      exact_mod_cast (by nlinarith [hs 2] : f 2 seed*den 2≤9*num 2)
  have hp : 0<LightTernaryRowSelector.pick good N :=
    (LightTernaryRowSelector.pick_pos_iff good N).mpr ⟨seed.val,seed.isLt,hgood⟩
  exact ⟨hp,LightTernaryRowSelector.pick_good good N hp⟩

/-- Semantics of the physical selector give the unscaled paired and both
original-source collision contractions. Query factorials cancel exactly. -/
theorem actual_good_step (a b p oldPi nextPi oldB nextB oldC nextC sOld sNext : ℕ)
    (hOld : 0<sOld) (hNext : 0<sNext)
    (flag vPi vB vC : ℕ→ℤ) (chosen : ℕ)
    (hPi : vPi chosen=(sNext*nextPi : ℕ))
    (hB : vB chosen=(nextB : ℕ)) (hC : vC chosen=(nextC : ℕ))
    (hgood : LightTernaryRowSelector.Good flag vPi vB vC (a*sOld) p p
      (b*sNext*(sOld*oldPi)) (9*oldB) (9*oldC) chosen) :
    a*nextPi≤b*oldPi ∧ p*nextB≤9*oldB ∧ p*nextC≤9*oldC := by
  rcases hgood with ⟨_,h0,h1,h2⟩
  rw [hPi] at h0
  rw [hB] at h1
  rw [hC] at h2
  have h0N' : (sNext*nextPi)*(a*sOld)≤b*sNext*(sOld*oldPi) := by exact_mod_cast h0
  have h0N : a*sOld*(sNext*nextPi)≤b*sNext*(sOld*oldPi) := by simpa only [Nat.mul_comm] using h0N'
  refine ⟨(scaled_step_iff a b oldPi nextPi sOld sNext hOld hNext).mp h0N, ?_, ?_⟩
  · have hh : nextB*p≤9*oldB := by exact_mod_cast h1
    simpa only [Nat.mul_comm] using hh
  · have hh : nextC*p≤9*oldC := by exact_mod_cast h2
    simpa only [Nat.mul_comm] using hh

/-- One complete selected chain. Its three inequalities are exactly the
ones established by the actual selector receipt above. -/
theorem selected_chain (K m n b : ℕ) (hk : 0<K) (hm : 0<m) (hn : 1<n)
    (hF : (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m)
    (hp9 : 9<nativePrime K m)
    (Pi B C : ℕ→ℕ)
    (hstepPi : ∀ j, nativePrime K m^(2*K)*Pi (j+1)≤
      (9*(nativeFamily K m (selectedMoment K)).length*outputSize m*partitionCap m^K)*Pi j)
    (hstepB : ∀ j, nativePrime K m*B (j+1)≤9*B j)
    (hstepC : ∀ j, nativePrime K m*C (j+1)≤9*C j)
    (hinit : (Pi 0)^4≤((2*K).factorial*b^(2*K))^8*n^(8*K+5))
    (hinitB : B 0≤n^2) (hinitC : C 0≤n^2)
    (hnlarge : ((2*K).factorial*b^(2*K))^8<n)
    (hrate : TernaryPairedCollisionRate.charge K m<(7483/10000 : ℝ)) :
    Pi (radixLength m n)=0 ∧
      (B (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) ∧
      (C (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by
  have hbudget := paired_native_drift K (outputSize m) (partitionCap m) (inflation K m)
    (nativePrime K m) (nativeFamily K m (selectedMoment K)).length (inflation_lower hk m)
    (nativePrime_lower K m) hF
  have hzero := paired_zero_of_initial_budget K (outputSize m) (nativePrime K m^(2*K))
    (9*(nativeFamily K m (selectedMoment K)).length*outputSize m*partitionCap m^K)
    n (((2*K).factorial*b^(2*K))^8) (pow_pos (nativePrime_prime K m).pos _) Pi hstepPi
    hbudget (radixLength m n)
    (Nat.le_pow_clog (by have := outputSize_ge_sixteen hm; omega) (n^2)) hinit hnlarge
  have hB := TernaryPairedCollisionRate.collision_bound hm hn hp9 B hstepB hinitB
  have hC := TernaryPairedCollisionRate.collision_bound hm hn hp9 C hstepC hinitC
  have hpow := Real.rpow_le_rpow_of_exponent_le (show (1 : ℝ)≤n by exact_mod_cast hn.le) hrate.le
  exact ⟨hzero,hB.trans hpow,hC.trans hpow⟩

/-- The initial score is the literal sum of original endpoint minors over
requester/carry groups. The executable selected inequalities then force
zero paired score and the paid collision bounds for every large input. -/
theorem selected_chain_eventually {K m b : ℕ} (hk : 0<K) (hm : 0<m) (hb : 1<b)
    {κ δ : ℝ} (hκ : 0≤κ) (hcarry : carryExponent m b κ<δ) (hδ : 4*δ<1)
    (hF : (9*(nativeFamily K m (selectedMoment K)).length)^4≤outputSize m)
    (hp9 : 9<nativePrime K m)
    (hrate : TernaryPairedCollisionRate.charge K m<(7483/10000 : ℝ))
    (U : ℕ→ℕ) (hU : ∀ n, 1<n → (U n : ℝ)≤(n : ℝ)^κ)
    (P G : ℕ→Type*) [∀ n, Fintype (P n)] [∀ n, Fintype (G n)]
    (A : ∀ n, G n→(Fin K→P n)→Matrix (Fin (2*K))
      (Fin (paddedLength b (U n) (radixLength m n)+2)) ℤ)
    (hA : ∀ n g e i j, (A n g e i j).natAbs≤b)
    (hG : ∀ n, Fintype.card (G n)≤n*2^(paddedLength b (U n) (radixLength m n)))
    (hP : ∀ n, Fintype.card (P n)≤n^2)
    (Pi B C : ℕ→ℕ→ℕ)
    (hPi0 : ∀ n, Pi n 0≤∑ g : G n, ∑ e : Fin K→P n, minorWeight (A n g e))
    (hB0 : ∀ n, B n 0≤n^2) (hC0 : ∀ n, C n 0≤n^2)
    (hstepPi : ∀ n j, nativePrime K m^(2*K)*Pi n (j+1)≤
      (9*(nativeFamily K m (selectedMoment K)).length*outputSize m*partitionCap m^K)*Pi n j)
    (hstepB : ∀ n j, nativePrime K m*B n (j+1)≤9*B n j)
    (hstepC : ∀ n j, nativePrime K m*C n (j+1)≤9*C n j) :
    ∀ᶠ n : ℕ in atTop,
      Pi n (radixLength m n)=0 ∧
      (B n (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) ∧
      (C n (radixLength m n) : ℝ)≤(n : ℝ)^(7483/10000 : ℝ) := by
  filter_upwards [TernaryPairedCarryBudget.initial_digit_carry_eventually hm hb hκ hcarry hδ U hU,
    eventually_gt_atTop (((2*K).factorial*b^(2*K))^8),eventually_gt_atTop (1 : ℕ)] with n hc hnlarge hn
  have hinit := initial_fourth_bound K (paddedLength b (U n) (radixLength m n)+2) b n
    (2^(paddedLength b (U n) (radixLength m n))) 1 (A n) (hA n) (hG n) (hP n)
    (by simpa only [one_mul] using hc)
  have hinit' := (Nat.pow_le_pow_left (hPi0 n) 4).trans hinit
  exact selected_chain K m n b hk hm hn hF hp9 (Pi n) (B n) (C n)
    (hstepPi n) (hstepB n) (hstepC n) (by simpa only [one_mul] using hinit') (hB0 n) (hC0 n) hnlarge hrate

/-- After the actual original-source cleanup, every wanted group has
constant physical support. This uses injectivity of BOTH surviving source
hash maps and the literal original integer minor score. -/
theorem surviving_groups_support {F W B C G D : Type*}
    [Field F] [Fintype F] [AddCommGroup W] [Module F W] [Fintype W]
    [Fintype B] [Fintype C] [Fintype G] [DecidableEq B] [DecidableEq C]
    [DecidableEq W] [DecidableEq D]
    (J K total : ℕ) (L : B→Fin J→ℤ) (R : C→Fin J→ℤ)
    (H : (Fin J→F)→ₗ[F] W)
    (P : G→Type*) [∀ g, Fintype (P g)]
    (left : ∀ g, P g→{b : B // b∉TernaryOriginalCollisions.deleted (fun b => H (fun j => (L b j : F)))})
    (right : ∀ g, P g→{c : C // c∉TernaryOriginalCollisions.deleted (fun c => H (fun j => (R c j : F)))})
    (root : G→W) (mode : ∀ g, P g→D)
    (hroot : ∀ g a, H ((fun j => (L (left g a).val j : F))+(fun j => (R (right g a).val j : F)))=root g)
    (hraw : ∀ g a b, (fun j => (L (left g a).val j : F))+(fun j => (R (right g a).val j : F))=
      (fun j => (L (left g b).val j : F))+(fun j => (R (right g b).val j : F))→mode g a=mode g b)
    (hsource : ∀ g a b, left g a=left g b → right g a=right g b → mode g a=mode g b)
    (hpotential : (∑ g : G, ∑ e : Fin K→P g,
      rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))≤total)
    (hzero : total=0) :
    ∀ g, (TernaryPairedSupport.physicalSupport (mode g)).card≤2*Fintype.card F^K := by
  classical
  intro g
  have hsum : (∑ e : Fin K→P g,
      rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))=0 := by
    have hh : (∑ e : Fin K→P g, rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))≤
        (∑ g : G, ∑ e : Fin K→P g, rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e)) :=
      Finset.single_le_sum (f := fun g : G => ∑ e : Fin K→P g,
        rowWeight (tupleMatrix (fun a => L (left g a).val) (fun a => R (right g a).val) e))
        (fun i hi => Nat.zero_le _) (Finset.mem_univ g)
    exact Nat.eq_zero_of_le_zero ((hh.trans hpotential).trans_eq hzero)
  apply physical_support_cap_of_zero_minors
    (fun a => L (left g a).val) (fun a => R (right g a).val) H (root g) (mode g) K
    (hroot g) (hraw g) ?_ hsum
  exact mode_eq_of_singleton_source_hashes (left g) (right g)
    (fun b j => (L b.val j : F)) (fun c j => (R c.val j : F)) H (root g) (mode g)
    (TernaryOriginalCollisions.surviving_hash_injective _) (TernaryOriginalCollisions.surviving_hash_injective _)
    (hroot g) (hsource g)

end ThreeSum.TernaryPairedSelectedChain
