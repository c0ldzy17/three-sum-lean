import Submission.ThreeSum.TernaryActualRuntimeParameters
import Submission.ThreeSum.LightTernaryColorPreparationProof
import Submission.ThreeSum.LightTernaryPreparedPostSelection
import Submission.ThreeSum.TernaryFastProgramBudget
import Submission.ThreeSum.TernaryActualCleanupRuntime

/-! A size-only time envelope for the complete executed per-color solver. -/
noncomputable section
namespace ThreeSum.TernaryActualColoredRuntime
open Light Real Filter StageBounds ArithmeticStageBounds
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryNativeCompleteFrontend
open TernaryActualPrefixRuntime TernaryActualSeedRuntime TernaryEntropyRates
open TernaryOversizePrime TernaryOversizeRates TernaryOversizeOverhead TernaryCoverScale
open scoped Topology BigOperators
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

def exponent : ℝ :=19209/10000
def J (m β κ n : ℕ) :=TernarySignedPadding.paddedLength β (n^κ) (radixLength m n)

/-- This function is independent of every source value, color, field
polynomial, selected seed and requester list. -/
def envelope (C : ℝ) (degree m β κ n : ℕ) : ℕ :=
  ⌈C*(J m β κ n+1:ℕ)^degree*(2:ℝ)^J m β κ n*
    (n:ℝ)^TernaryCountFrontendBudget.frontendExponent⌉₊

theorem ceil_powerBound {f : ℕ→ℝ} {a : ℝ} (ha : 0≤a) (hf : ∀n,0≤f n)
    (h : ∀ε:ℝ,0<ε→∀ᶠ n:ℕ in atTop,f n≤(n:ℝ)^(a+ε)) :
    PowerBound (fun n=>⌈f n⌉₊) a:=by
  intro ε hε
  filter_upwards [h (ε/2) (by linarith),(PowerBound.const 2) (ε/2) (by linarith),
    eventually_gt_atTop (1:ℕ)] with n hn htwo hlarge
  have hnR : (0:ℝ)<n:=by exact_mod_cast lt_trans Nat.zero_lt_one hlarge
  have hpow : (1:ℝ)≤(n:ℝ)^(a+ε/2):=Real.one_le_rpow
    (by exact_mod_cast hlarge.le) (by linarith)
  have hceil : (⌈f n⌉₊:ℝ)≤f n+1:=(Nat.ceil_lt_add_one (hf n)).le
  have hh : (⌈f n⌉₊:ℝ)≤2*(n:ℝ)^(a+ε/2):=by linarith
  have htwo' : (2:ℝ)≤(n:ℝ)^(ε/2):=by simpa only [zero_add,Nat.cast_ofNat] using htwo
  calc
    _≤2*(n:ℝ)^(a+ε/2):=hh
    _≤(n:ℝ)^(ε/2)*(n:ℝ)^(a+ε/2):=mul_le_mul_of_nonneg_right htwo' (by positivity)
    _=(n:ℝ)^(a+ε):=by rw [←Real.rpow_add hnR]; congr 1; ring

theorem envelope_powerBound {m β κ : ℕ} {δ : ℝ} (hm : 0<m) (hβ : 1<β)
    (hδ : 0≤δ) (hcarry : TernarySignedPadding.carryExponent m β (κ:ℝ)<δ)
    (C : ℝ) (hC : 0≤C) (degree : ℕ) :
    PowerBound (envelope C degree m β κ) (TernaryCountFrontendBudget.frontendExponent+δ):=by
  apply ceil_powerBound (by norm_num [TernaryCountFrontendBudget.frontendExponent]; linarith)
    (fun _=>by positivity)
  intro ε hε
  have hU : ∀n:ℕ,1<n→((n^κ:ℕ):ℝ)≤(n:ℝ)^(κ:ℝ):=by
    intro n hn
    simp only [Real.rpow_natCast,Nat.cast_pow]
    exact le_rfl
  have hp:=TernarySignedPreparationBudget.polynomial_digit_budget hm hβ (Nat.cast_nonneg κ)
    hε C hC degree (fun n=>n^κ) hU
  have hc:=TernarySignedPadding.padded_carry_eventually hm hβ (Nat.cast_nonneg κ)
    hcarry (fun n=>n^κ) hU
  filter_upwards [hp,hc,eventually_gt_atTop (1:ℕ)] with n hp hc hn
  have hbin : (1:ℝ)≤((Nat.log 2 (3*n^κ+1):ℝ)+2)^degree:=one_le_pow₀ (by
    have hh : (0:ℝ)≤Nat.log 2 (3*n^κ+1):=Nat.cast_nonneg _
    linarith)
  have hp' : C*(J m β κ n+1:ℕ)^degree≤(n:ℝ)^ε:=by
    have hh:=le_mul_of_one_le_right (show (0:ℝ)≤C*(J m β κ n+1:ℕ)^degree by positivity) hbin
    exact hh.trans (by simpa [J] using hp)
  have hc' : (2:ℝ)^J m β κ n≤(n:ℝ)^δ:=by simpa [J] using hc
  have hh:=mul_le_mul_of_nonneg_right
    (mul_le_mul hp' hc' (by positivity) (by positivity))
    (show (0:ℝ)≤(n:ℝ)^TernaryCountFrontendBudget.frontendExponent by positivity)
  have hnR : (0:ℝ)<n:=by exact_mod_cast lt_trans Nat.zero_lt_one hn
  calc
    _≤(n:ℝ)^ε*(n:ℝ)^δ*(n:ℝ)^TernaryCountFrontendBudget.frontendExponent:=hh
    _=(n:ℝ)^(TernaryCountFrontendBudget.frontendExponent+δ+ε):=by
      rw [←Real.rpow_add hnR,←Real.rpow_add hnR]; congr 1; ring

theorem preparation_build_bound {n : ℕ} (hn : 1≤n) (J U : ℕ) :
    LightTernaryColorPreparationProof.buildTime n n n J U≤
      100000*n*2^J*(J+1)^2*(Nat.log 2 (3*U+1)+2)^2:=by
  let B:=Nat.log 2 (3*U+1)+2
  let V:=n*2^J*(J+1)^2*B^2
  have hB : 2≤B:=by dsimp [B]; omega
  have hQ : 1≤2^J:=Nat.one_le_pow _ _ (by decide)
  have hJ : 1≤J+1:=by omega
  have hJ2 : J+1≤(J+1)^2:=Nat.le_self_pow (by decide) _
  have hB2 : B≤B^2:=Nat.le_self_pow (by decide) _
  have hN : n≤V:=by
    exact ((Nat.le_mul_of_pos_right n hQ).trans
      (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hJ))).trans
        (Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ (show 1≤B by omega)))
  have h1 : 1≤V:=hn.trans hN
  have hX : n*(J+1)*B≤V:=by
    have hh:=Nat.mul_le_mul (Nat.mul_le_mul_left n hJ2) hB2
    have hq:=Nat.mul_le_mul_left (n*(J+1)^2*B^2) hQ
    dsimp [V]
    nlinarith only [hh,hq]
  have hreq:=LightTernaryRequesterMatrix.time_bound n (2^J) J U
  have hcarry:=LightTernaryCarryCodes.time_bound J
  have hreq' : n*2^J*(J+1)*B≤V:=by
    have hh:=Nat.mul_le_mul (Nat.mul_le_mul_left (n*2^J) hJ2) hB2
    simpa [V,Nat.mul_assoc] using hh
  have hcar' : 2^J*(J+2)^2≤4*V:=by
    have hh : (J+2)^2≤4*(J+1)^2:=by nlinarith
    have hn' : 2^J*(J+1)^2≤V:=by
      have h0 : 2^J*(J+1)^2≤n*(2^J*(J+1)^2):=by simpa only [one_mul] using Nat.mul_le_mul_right (2^J*(J+1)^2) hn
      have h1:=Nat.le_mul_of_pos_right (n*(2^J*(J+1)^2)) (Nat.one_le_pow 2 B (show 1≤B by omega))
      have hh:=h0.trans h1
      simpa [V,Nat.mul_assoc] using hh
    nlinarith [Nat.mul_le_mul_left (2^J) hh]
  have hmatrix : LightTernarySignedMatrix.time n J U≤1000*V+20:=by
    have hh : LightTernarySignedMatrix.time n J U≤1000*n*(J+1)*B+20:=by
      unfold LightTernarySignedMatrix.time LightTernarySignedRow.time LightOutputDecodeDigits.time
        LightOutputDecodeDivide.budget
      dsimp [B]
      ring_nf
      omega
    nlinarith only [hh,hX]
  have hJ' : J≤V:=by
    have h0 : J+1≤n*(J+1):=by simpa only [one_mul] using Nat.mul_le_mul_right (J+1) hn
    have hh : J+1≤n*(J+1)*B:=h0.trans (Nat.le_mul_of_pos_right _ (show 1≤B by omega))
    omega
  unfold LightTernaryColorPreparationProof.buildTime LightNatPower.time
  dsimp [B] at hreq'
  dsimp [V] at hmatrix hcar' hreq' hN h1 hJ'
  dsimp [B] at *
  nlinarith only [hmatrix,hreq,hcarry,hreq',hcar',hN,h1,hJ']

theorem prelude_time_bound {n : ℕ} (hn : 1<n) :
    LightTernaryColorPrelude.time n≤20000*(n+1)*(LightColorParametersCosts.width n+1):=by
  have hs : BandPartition.size n n=1:=by
    unfold BandPartition.size
    rw [if_neg (by omega),Nat.div_eq_of_lt (by omega : n-1<n)]
  have hw : ColorBandBounds.width n n=2:=by
    norm_num [ColorBandBounds.width,LightBandEnumeration.width,hs]
  have hc : ColorBandBounds.count n n=3:=by norm_num [ColorBandBounds.count,hs]
  have hlog : Nat.clog 2 n≤LightColorParametersCosts.width n:=
    Nat.clog_le_of_le_pow (LightColorParametersCosts.width_sufficient n)
  have ht:=LightColorBands.time_bound (LightColorParametersCosts.width n) n n
  unfold LightTernaryColorPrelude.time
  have hh:=Nat.mul_le_mul_left (2100*(n+1)) (Nat.add_le_add_right hlog 1)
  have hW : 1≤LightColorParametersCosts.width n:=by unfold LightColorParametersCosts.width; omega
  unfold ColorBandBounds.time at ht
  rw [hc,hw] at ht
  nlinarith [Nat.mul_le_mul_left (n+1) hW]

theorem prelude_powerBound : PowerBound LightTernaryColorPrelude.time 1:=by
  have hn : PowerBound (fun n=>n+1) 1:=identity_powerBound.add_same ((PowerBound.const 1).mono_exponent (by norm_num))
  have hw : PowerBound (fun n=>LightColorParametersCosts.width n+1) 0:=
    LightColorParametersCosts.width_powerBound.add_same (PowerBound.const 1)
  have hh : PowerBound (fun n=>20000*(n+1)*(LightColorParametersCosts.width n+1)) 1:=by
    simpa only [zero_add,add_zero] using ((PowerBound.const 20000).mul hn).mul hw
  apply powerBound_mono hh
  filter_upwards [eventually_gt_atTop (1:ℕ)] with n hn
  exact prelude_time_bound hn

theorem preparation_powerBound {m β κ : ℕ} {δ : ℝ} (hm : 0<m) (hβ : 1<β)
    (hδ : 0≤δ) (hcarry : TernarySignedPadding.carryExponent m β (κ:ℝ)<δ) :
    PowerBound (fun n=>LightTernaryColorPreparationProof.time n (J m β κ n) (n^κ)) (1+δ):=by
  have hb : PowerBound (fun n=>LightTernaryColorPreparationProof.buildTime n n n (J m β κ n) (n^κ)) (1+δ):=by
    intro ε hε
    have hU : ∀n:ℕ,1<n→((n^κ:ℕ):ℝ)≤(n:ℝ)^(κ:ℝ):=by
      intro n hn
      simp only [Real.rpow_natCast,Nat.cast_pow]
      exact le_rfl
    have hh:=TernarySignedPreparationBudget.carry_preparation_budget hm hβ (Nat.cast_nonneg κ)
      hcarry hε 100000 (by norm_num) 2 (fun n=>n^κ) hU
    filter_upwards [hh,eventually_gt_atTop (1:ℕ)] with n hh hn
    have hb:=preparation_build_bound (show 1≤n by omega) (J m β κ n) (n^κ)
    have hbR : (LightTernaryColorPreparationProof.buildTime n n n (J m β κ n) (n^κ):ℝ)≤
      100000*(n:ℝ)*(2:ℝ)^J m β κ n*(J m β κ n+1:ℕ)^2*(Nat.log 2 (3*n^κ+1)+2:ℕ)^2:=by exact_mod_cast hb
    exact hbR.trans (by simpa [J,Nat.cast_add,Nat.cast_ofNat] using hh)
  have hp:=prelude_powerBound.mono_exponent (show (1:ℝ)≤1+δ by linarith)
  exact (hp.add_same hb).add_same ((PowerBound.const 5000).mono_exponent (by linarith))

/-- Only actual finite cardinalities, magnitudes and the typed query
maximum occur here. No execution or time conclusion is a field. -/
structure NativeBounds {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input)
    (n U κ carries D E j : ℕ) : Prop where
  left : I.nB≤n
  right : I.nC≤n
  requesters : I.requesterCount≤n*carries
  word : TernaryFrontendResources.eulerBound (N m j)
    (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I)≤D*(n+U+1)^E
  query : I.queryTime≤TernaryCountFrontendBudget.queryMax m j
    (nativeHost (K:=K) (k:=k) j maps Q I).front.f (nativeHost (K:=K) (k:=k) j maps Q I).front.g

structure State (K m : ℕ) where
  arena : Inputs
  phase : ℕ→Input
  seeds : (j seed : ℕ)→LightTernarySeedScoreFactory.Data
    (config (nativePrime K m) j (phase j) arena seed)
  post : Input
  cleanup : LightOriginalSurvivorPair.Layout
  keysB : ℕ→ℕ
  keysC : ℕ→ℕ

structure Fits {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : TernaryGoodOutputCatalog.Output m) (S : State K m)
    (β κ n D E B : ℕ) : Prop where
  dimension : S.arena.J=J m β κ n
  phases : ∀j≤radixLength m n,NativeBounds (k:=k) maps Q (S.phase j)
    n (n^κ) κ (2^S.arena.J) D E j
  post : NativeBounds (k:=k) maps Q S.post n (n^κ) κ (2^S.arena.J) D E (radixLength m n)
  seedB : ∀j≤radixLength m n,∀s,(S.seeds j s).bB≤B
  seedC : ∀j≤radixLength m n,∀s,(S.seeds j s).bC≤B
  seedO : ∀j≤radixLength m n,∀s,(S.seeds j s).bO≤B
  nA : S.cleanup.nA≤n
  nB : S.cleanup.nB≤n
  nC : S.cleanup.nC≤n
  modulus : S.cleanup.q=(nativePrime K m)^radixLength m n
  width : S.cleanup.L≤2*fixedLength m*S.arena.J
  collisionB : ((TernaryOriginalCollisions.collisionPairs
    (fun i : Fin S.cleanup.nB=>S.keysB i.val)).card:ℝ)≤(n:ℝ)^(7483/10000:ℝ)
  collisionC : ((TernaryOriginalCollisions.collisionPairs
    (fun i : Fin S.cleanup.nC=>S.keysC i.val)).card:ℝ)≤(n:ℝ)^(7483/10000:ℝ)

def hostInputs {K m : ℕ} (S : State K m) (n : ℕ) : ℕ→Input :=
  Function.update S.phase (radixLength m n) S.post

theorem Fits.host_bounds {K k m F β κ n D E B : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B) :
    ∀j≤radixLength m n,NativeBounds (k:=k) maps Q (hostInputs S n j)
      n (n^κ) κ (2^S.arena.J) D E j:=by
  intro j hj
  by_cases he : j=radixLength m n
  · subst j
    simpa only [hostInputs,Function.update_self] using H.post
  · simpa only [hostInputs,Function.update_of_ne he] using H.phases j hj

theorem Fits.prefix_bound {K k b m F β κ n D E B : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n:ℝ)≤
      prefixConstant K k c d m F D E κ B*(S.arena.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+6)*
        (2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:=by
  have hj : radixLength m n≤S.arena.J:=by
    rw [H.dimension]
    unfold J TernarySignedPadding.paddedLength
    omega
  have hh:=canonical_all_prefix_bound (U:=n^κ) (κ:=κ) (carries:=2^S.arena.J)
    maps Q S.phase S.arena S.seeds H.seedB H.seedC H.seedO hK hk hgood hn hj (le_refl _)
    hFpos hF hb (Nat.one_le_pow _ _ (by decide))
    (fun j hj=>(H.phases j hj).left) (fun j hj=>(H.phases j hj).right)
    (fun j hj=>(H.phases j hj).requesters) hposL hposR
    (fun j hj=>(H.phases j hj).word) (fun j hj=>(H.phases j hj).query) c d hpoly
  simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh

theorem Fits.host_bound {K k b m F β κ n D E B : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    ((nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post).runtime:ℝ)≤
      hostConstant K k c d m F D E κ*(S.arena.J+1:ℕ)^4*(2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:=by
  have hh:=all_host_prefix_bound (U:=n^κ) (κ:=κ) (carries:=2^S.arena.J)
    maps Q (hostInputs S n) hK hk hgood hn (le_refl _) hFpos hF hb
    (Nat.one_le_pow _ _ (by decide)) (fun j hj=>(H.host_bounds j hj).left)
    (fun j hj=>(H.host_bounds j hj).right) (fun j hj=>(H.host_bounds j hj).requesters)
    hposL hposR (fun j hj=>(H.host_bounds j hj).word) (fun j hj=>(H.host_bounds j hj).query) c d hpoly
  have hsingle : (nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post).runtime≤
      allHostTime (K:=K) (k:=k) maps Q (hostInputs S n) n:=by
    have hpost : hostInputs S n (radixLength m n)=S.post:=
      Function.update_self _ _ _
    rw [←hpost]
    change (nativeHost (K:=K) (k:=k) (radixLength m n) maps Q (hostInputs S n (radixLength m n))).runtime≤
      ∑j∈Finset.range (radixLength m n+1), (nativeHost (K:=K) (k:=k) j maps Q (hostInputs S n j)).runtime
    exact Finset.single_le_sum
      (f:=fun j=>(nativeHost (K:=K) (k:=k) j maps Q (hostInputs S n j)).runtime)
      (fun i _=>Nat.zero_le _)
      (show radixLength m n∈Finset.range (radixLength m n+1) by simp)
  have hJ : radixLength m n+1≤S.arena.J+1:=by
    rw [H.dimension]
    unfold J TernarySignedPadding.paddedLength
    omega
  have hp : ((radixLength m n+1:ℕ):ℝ)^4≤((S.arena.J+1:ℕ):ℝ)^4:=by exact_mod_cast Nat.pow_le_pow_left hJ 4
  have ht:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (hostConstant_nonneg K k c d m F D E κ))
      (show (0:ℝ)≤(2:ℝ)^S.arena.J by positivity)) (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
  have hh' : (allHostTime (K:=K) (k:=k) maps Q (hostInputs S n) n:ℝ)≤
      hostConstant K k c d m F D E κ*(radixLength m n+1:ℕ)^4*(2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:=by
    simpa only [Nat.cast_pow,Nat.cast_ofNat] using hh
  exact (show (_:ℝ)≤(allHostTime (K:=K) (k:=k) maps Q (hostInputs S n) n:ℝ) by exact_mod_cast hsingle).trans (hh'.trans ht)

theorem Fits.base_bound {K k b m F β κ n D E B : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) :
    let host:=nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post
    (TernaryMomentReporterBudget.base host:ℝ)≤
      4*(2:ℝ)^S.arena.J*volumeBundle K k b m n (radixLength m n)+(host.runtime:ℝ):=by
  let R:=radixLength m n
  let host:=nativeHost (K:=K) (k:=k) R maps Q S.post
  let V:=volumeBundle K k b m n R
  have hv:=bundle_components (k:=k) (b:=b) (j:=R) hK hn (native_factor_positive hFpos hF hb)
  have hc : (1:ℝ)≤(2:ℝ)^S.arena.J:=one_le_pow₀ (by norm_num)
  have hcarry : V≤(2:ℝ)^S.arena.J*V:=le_mul_of_one_le_left
    (show (0:ℝ)≤V by exact le_trans (by norm_num) hv.2.2.2) hc
  have hN : (n:ℝ)≤(2:ℝ)^S.arena.J*V:=hv.1.trans hcarry
  have hOne : (1:ℝ)≤(2:ℝ)^S.arena.J*V:=hv.2.2.2.trans hcarry
  have hl : (S.post.nB:ℝ)≤(2:ℝ)^S.arena.J*V:=
    (show (S.post.nB:ℝ)≤n by exact_mod_cast H.post.left).trans hN
  have hr : (S.post.nC:ℝ)≤(2:ℝ)^S.arena.J*V:=
    (show (S.post.nC:ℝ)≤n by exact_mod_cast H.post.right).trans hN
  have hcnt:=wanted_native_count (j:=R) maps S.post hK hgood hF hb H.post.requesters
  have hcount : (host.front.count:ℝ)≤(2:ℝ)^S.arena.J*V:=by
    have hh:=mul_le_mul_of_nonneg_left hv.2.2.1 (show (0:ℝ)≤(2:ℝ)^S.arena.J by positivity)
    change ((entries (r:=R) maps (threshold K k m) S.post).length:ℝ)≤_
    simp only [Nat.cast_pow,Nat.cast_ofNat] at hcnt
    nlinarith only [hcnt,hh]
  change ((S.post.nB+S.post.nC+host.front.count+host.runtime+1:ℕ):ℝ)≤_
  push_cast
  nlinarith only [hl,hr,hcount,hOne]

def reporterCoefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  (TernaryMomentReporterBudget.reporterConstant H:ℝ)*
    (hostConstant K k c d m F D E κ+4*volumeConstant K k c d m)

theorem reporterCoefficient_nonneg (K k c d m F D E κ B H : ℕ) :
    0≤reporterCoefficient K k c d m F D E κ B H:=
  mul_nonneg (Nat.cast_nonneg _) (add_nonneg (hostConstant_nonneg _ _ _ _ _ _ _ _ _)
    (mul_nonneg (by norm_num) (volumeConstant_nonneg _ _ _ _ _)))

theorem Fits.reporter_bound {K k b m F β κ n D E B Hdet : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    let host:=nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post
    (LightTernaryMomentReporter.time host Hdet:ℝ)≤
      reporterCoefficient K k c d m F D E κ B Hdet*(S.arena.J+1:ℕ)^4*(2:ℝ)^S.arena.J*
        (n:ℝ)^fullExponent K k c d m:=by
  let host:=nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post
  let T:=(n:ℝ)^fullExponent K k c d m
  have hb0:=H.base_bound hK hgood hn hFpos hF hb
  have ht:=H.host_bound hK hk hgood hn hFpos hF hb hposL hposR c d hpoly
  have hv:=volume_bundle_bound (j:=radixLength m n) hK hk hgood.1 hn (le_refl _) c d hpoly
  have hJ : (1:ℝ)≤((S.arena.J+1:ℕ):ℝ)^4:=one_le_pow₀ (by
    exact_mod_cast (show 1≤S.arena.J+1 by omega))
  have h1:=mul_le_mul_of_nonneg_left hv (show (0:ℝ)≤4*(2:ℝ)^S.arena.J by positivity)
  have h2:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hJ (show (0:ℝ)≤4*volumeConstant K k c d m by positivity [volumeConstant_nonneg K k c d m]))
      (show (0:ℝ)≤(2:ℝ)^S.arena.J by positivity)) (show (0:ℝ)≤T by positivity)
  have hbase : (TernaryMomentReporterBudget.base host:ℝ)≤
      (hostConstant K k c d m F D E κ+4*volumeConstant K k c d m)*
        (S.arena.J+1:ℕ)^4*(2:ℝ)^S.arena.J*T:=by
    dsimp only [T] at h2 ⊢
    nlinarith only [hb0,ht,h1,h2]
  have hr:=TernaryMomentReporterBudget.reporter_time_bound host Hdet
  have hrR : (LightTernaryMomentReporter.time host Hdet:ℝ)≤
      (TernaryMomentReporterBudget.reporterConstant Hdet:ℝ)*(TernaryMomentReporterBudget.base host:ℝ):=by exact_mod_cast hr
  unfold reporterCoefficient
  have hscale:=mul_le_mul_of_nonneg_left hbase
    (Nat.cast_nonneg (TernaryMomentReporterBudget.reporterConstant Hdet))
  exact hrR.trans (by simpa only [T,mul_assoc] using hscale)

def postCoefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  reporterCoefficient K k c d m F D E κ B H+
    1000000*(fixedLength m+1:ℕ)*(volumeConstant K k c d m+1)

def coefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  prefixConstant K k c d m F D E κ B+postCoefficient K k c d m F D E κ B H+1

theorem coefficient_nonneg (K k c d m F D E κ B H : ℕ) :
    0≤coefficient K k c d m F D E κ B H:=by
  unfold coefficient postCoefficient
  positivity [prefixConstant_nonneg K k c d m F D E κ B,
    reporterCoefficient_nonneg K k c d m F D E κ B H,volumeConstant_nonneg K k c d m]

/-- The delivered per-color running-time budget is size-only. Its fixed
parameters may depend on κ, and it contains no source data or run state. -/
def uniformTime (K k c d m F D E κ B H β n : ℕ) : ℕ :=
  LightTernaryColorPreparationProof.time n (J m β κ n) (n^κ)+
    LightTernaryArenaTemplate.time E+LightTernaryInitialBudgets.time K+
      envelope (coefficient K k c d m F D E κ B H)
        (seedPolynomialD K (nativePrime K m) B+6) m β κ n+10000

/-- The whole size-only per-color envelope has exponent strictly below
the final1.921 target, before the outer subpolynomial coloring scan. -/
theorem PB {K k c d m F D E κ B H β : ℕ} {δ : ℝ}
    (hm : 0<m) (hβ : 1<β) (hδ : 0≤δ)
    (hcarry : TernarySignedPadding.carryExponent m β (κ:ℝ)<δ)
    (hroom : TernaryCountFrontendBudget.frontendExponent+δ≤exponent) :
    PowerBound (uniformTime K k c d m F D E κ B H β) exponent:=by
  have he:=envelope_powerBound hm hβ hδ hcarry
    (coefficient K k c d m F D E κ B H) (coefficient_nonneg _ _ _ _ _ _ _ _ _ _ _)
    (seedPolynomialD K (nativePrime K m) B+6)
  have hp:=(preparation_powerBound hm hβ hδ hcarry).mono_exponent
    (show (1:ℝ)+δ≤exponent by
      have hh : (1:ℝ)≤TernaryCountFrontendBudget.frontendExponent:=by norm_num [TernaryCountFrontendBudget.frontendExponent]
      linarith)
  have hzero : (0:ℝ)≤exponent:=by norm_num [exponent]
  exact (((hp.add_same ((PowerBound.const (LightTernaryArenaTemplate.time E)).mono_exponent hzero)).add_same
    ((PowerBound.const (LightTernaryInitialBudgets.time K)).mono_exponent hzero)).add_same
      (he.mono_exponent hroom)).add_same ((PowerBound.const 10000).mono_exponent hzero)

theorem selected_room {K : ℕ} (hK : 100000000≤K) :
    TernaryCountFrontendBudget.frontendExponent+microAllowance K<exponent:=by
  have hk : (100000000:ℝ)≤K:=by exact_mod_cast hK
  have hp : (0:ℝ)<K:=by linarith
  have hμ : microAllowance K<(1/10000:ℝ):=by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  norm_num [TernaryCountFrontendBudget.frontendExponent,exponent]
  linarith

theorem exponent_lt_target : exponent<TernaryParameters.targetExponent:=by
  norm_num [exponent,TernaryParameters.targetExponent]

theorem Fits.post_bound {K k b m F β κ n D E B Hdet : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤TernaryCountFrontendBudget.frontendExponent) :
    let host:=nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post
    ((LightTernaryPreparedPostSelection.time host Hdet S.cleanup S.keysB S.keysC+673:ℕ):ℝ)≤
      postCoefficient K k c d m F D E κ B Hdet*(S.arena.J+1:ℕ)^4*(2:ℝ)^S.arena.J*
        (n:ℝ)^TernaryCountFrontendBudget.frontendExponent:=by
  let host:=nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post
  let Z:=(S.arena.J+1:ℕ)
  let P:=(n:ℝ)^TernaryCountFrontendBudget.frontendExponent
  have hpow:=Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤n by exact_mod_cast hn.le) hcharge
  have hv:=bundle_components (k:=k) (b:=b) (j:=radixLength m n) hK hn (native_factor_positive hFpos hF hb)
  have hvol:=volume_bundle_bound (j:=radixLength m n) hK hk hgood.1 hn (le_refl _) c d hpoly
  have hq : (S.cleanup.q:ℝ)≤volumeConstant K k c d m*P:=by
    rw [H.modulus]
    push_cast
    exact hv.2.1.trans (hvol.trans (mul_le_mul_of_nonneg_left hpow (volumeConstant_nonneg K k c d m)))
  have hp:=TernaryActualCleanupRuntime.prepared_post_bound host Hdet S.cleanup S.keysB S.keysC
    m S.arena.J n (volumeConstant K k c d m) hn (volumeConstant_nonneg K k c d m)
    H.nA H.nB H.nC hq H.width H.collisionB H.collisionC
  have hr:=H.reporter_bound (Hdet:=Hdet) hK hk hgood hn hFpos hF hb hposL hposR c d hpoly
  have hr' : (LightTernaryMomentReporter.time host Hdet:ℝ)≤
      reporterCoefficient K k c d m F D E κ B Hdet*(Z:ℝ)^4*(2:ℝ)^S.arena.J*P:=
    hr.trans (mul_le_mul_of_nonneg_left hpow (by positivity [reporterCoefficient_nonneg K k c d m F D E κ B Hdet]))
  have hZ : (Z:ℝ)≤(Z:ℝ)^4:=by
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤Z by dsimp [Z]; exact_mod_cast (show 1≤S.arena.J+1 by omega))
      (show 1≤(4:ℕ) by decide)
  have hZ' : (Z:ℝ)≤(Z:ℝ)^4*(2:ℝ)^S.arena.J:=hZ.trans
    (le_mul_of_one_le_right (by positivity) (one_le_pow₀ (by norm_num)))
  have hx:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZ'
    (show (0:ℝ)≤((1000000*(fixedLength m+1):ℕ):ℝ)*(volumeConstant K k c d m+1) by positivity [volumeConstant_nonneg K k c d m]))
      (show (0:ℝ)≤P by positivity)
  unfold postCoefficient
  dsimp [Z,P] at hp hr' hx ⊢
  push_cast at hp hr' hx ⊢
  nlinarith only [hp,hr',hx]

/-- Literal sum of the actual included child programs. The extra673 is
the proved final call-argument cost; the remaining10000 pays the driver. -/
def time {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : TernaryGoodOutputCatalog.Output m) (S : State K m) (E κ Hdet n : ℕ) : ℕ :=
  LightTernaryColorPreparationProof.time n S.arena.J (n^κ)+LightTernaryArenaTemplate.time E+
    LightTernaryInitialBudgets.time K+allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n+
      (LightTernaryPreparedPostSelection.time
        (nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post) Hdet S.cleanup S.keysB S.keysC+673)+10000

/-- Uniform pointwise domination: original data and selected hashes are
absent from the right-hand size-only time function. -/
theorem time_le_uniform {K k b m F β κ n D E B Hdet : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q S β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤TernaryCountFrontendBudget.frontendExponent) :
    time (k:=k) maps Q S E κ Hdet n≤uniformTime K k c d m F D E κ B Hdet β n:=by
  let host:=nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post
  let Z:=(S.arena.J+1:ℕ)
  let degree:=seedPolynomialD K (nativePrime K m) B+6
  let P:=(n:ℝ)^TernaryCountFrontendBudget.frontendExponent
  have hp:=H.prefix_bound hK hk hgood hn hFpos hF hb hposL hposR c d hpoly
  have ht:=H.post_bound (Hdet:=Hdet) hK hk hgood hn hFpos hF hb hposL hposR c d hpoly hcharge
  have hpow:=Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤n by exact_mod_cast hn.le) hcharge
  have hp' : (allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n:ℝ)≤
      prefixConstant K k c d m F D E κ B*(Z:ℝ)^degree*(2:ℝ)^S.arena.J*P:=
    hp.trans (mul_le_mul_of_nonneg_left hpow (by positivity [prefixConstant_nonneg K k c d m F D E κ B]))
  have hZd : (Z:ℝ)^4≤(Z:ℝ)^degree:=pow_le_pow_right₀
    (show (1:ℝ)≤Z by dsimp [Z]; exact_mod_cast (show 1≤S.arena.J+1 by omega)) (by dsimp [degree]; omega)
  have hpc : 0≤postCoefficient K k c d m F D E κ B Hdet:=by
    unfold postCoefficient
    positivity [reporterCoefficient_nonneg K k c d m F D E κ B Hdet,volumeConstant_nonneg K k c d m]
  have ht' : ((LightTernaryPreparedPostSelection.time host Hdet S.cleanup S.keysB S.keysC+673:ℕ):ℝ)≤
      postCoefficient K k c d m F D E κ B Hdet*(Z:ℝ)^degree*(2:ℝ)^S.arena.J*P:=by
    exact ht.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hZd hpc) (show (0:ℝ)≤(2:ℝ)^S.arena.J by positivity)) (show (0:ℝ)≤P by positivity))
  have hsum : ((allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n+
      (LightTernaryPreparedPostSelection.time host Hdet S.cleanup S.keysB S.keysC+673):ℕ):ℝ)≤
      coefficient K k c d m F D E κ B Hdet*(Z:ℝ)^degree*(2:ℝ)^S.arena.J*P:=by
    unfold coefficient
    push_cast at ht' ⊢
    have hnon : 0≤(Z:ℝ)^degree*(2:ℝ)^S.arena.J*P:=by positivity
    nlinarith only [hp',ht',hnon]
  have hceil : allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n+
      (LightTernaryPreparedPostSelection.time host Hdet S.cleanup S.keysB S.keysC+673)≤
        envelope (coefficient K k c d m F D E κ B Hdet) degree m β κ n:=by
    have hreal : ((allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n+
        (LightTernaryPreparedPostSelection.time host Hdet S.cleanup S.keysB S.keysC+673):ℕ):ℝ)≤
          (envelope (coefficient K k c d m F D E κ B Hdet) degree m β κ n:ℝ):=by
      apply hsum.trans
      dsimp [Z,P,envelope]
      rw [H.dimension]
      exact Nat.le_ceil _
    exact_mod_cast hreal
  unfold time uniformTime
  rw [H.dimension]
  dsimp only [degree,host] at hceil
  omega

end ThreeSum.TernaryActualColoredRuntime
