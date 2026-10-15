import Submission.ThreeSum.TernaryActualPrefixRuntime
import Submission.ThreeSum.TernaryArenaSeedCandidate
import Submission.ThreeSum.TernaryArenaControllerCore
import Submission.ThreeSum.TernarySeedCoefficientBudget
import Submission.ThreeSum.LightTernaryPrefixStep
import Submission.ThreeSum.LightTernaryPrefixInit

noncomputable section
namespace ThreeSum.TernaryActualSeedRuntime
open Real Light Filter
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryNativeCompleteFrontend
open TernaryActualPrefixRuntime TernaryEntropyRates TernaryOversizePrime
open TernaryOversizeRates TernaryOversizeOverhead TernaryCoverScale
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

abbrev threshold (K k m : ℕ) := TernaryCoverCapParameters.rawThreshold (nativePrime K m)
  (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k
abbrev outputCap (K k m F : ℕ) := F*TernaryGoodOutputCatalog.cap m (nativePrime K m) (threshold K k m)

theorem wanted_factor_bound {K k b m F : ℕ} (hK : 0<K)
    (hF : F≤(nativeFamily K m k).length) (hb : TernaryActualPrefixRuntime.localFactor m≤b) :
    (outputCap K k m F:ℝ)≤(nativeFactor K k b m:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ)):=by
  let P:=nativePrime K m
  let τ:=threshold K k m
  let loss:=TernaryPartitionCount.partitionLoss (7930175*m) (978249*m)
  have hcap:=TernaryGoodOutputCatalog.cap_real_le_native (m:=m) (p:=P) τ
    (TernaryCoverCapParameters.rawThreshold_pos _ _ _) (nativePrime_base_lower hK m)
  have hbase : 2*loss*F*τ≤nativeFactor K k b m:=by
    have hb' : 2*loss≤b:=by dsimp [TernaryActualPrefixRuntime.localFactor,loss] at hb ⊢; omega
    have hh:=Nat.mul_le_mul_right τ (Nat.mul_le_mul hb' hF)
    simpa only [nativeFactor,Nat.mul_assoc] using hh
  have hh:=mul_le_mul_of_nonneg_left hcap (show (0:ℝ)≤F by positivity)
  have hd:=mul_le_mul_of_nonneg_right (show ((2*loss*F*τ:ℕ):ℝ)≤nativeFactor K k b m by exact_mod_cast hbase)
    (show (0:ℝ)≤(P:ℝ)/(partitionCap m:ℝ) by positivity)
  calc
    (outputCap K k m F:ℝ)≤(F:ℝ)*(2*(((loss*P*τ:ℕ):ℝ)/(partitionCap m:ℝ))):=by
      simpa [outputCap,TernaryGoodOutputCatalog.Rbar,partitionCap,loss,Nat.cast_mul,τ] using hh
    _=((2*loss*F*τ:ℕ):ℝ)*((P:ℝ)/(partitionCap m:ℝ)):=by push_cast; ring
    _≤_:=hd

theorem wanted_work_bound {K k b m F n request carries j : ℕ} (hK : 0<K)
    (hF : F≤(nativeFamily K m k).length) (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hr : request≤n*carries) :
    ((request*(outputCap K k m F)^j:ℕ):ℝ)≤
      (carries:ℝ)*(nativeFactor K k b m:ℝ)^j*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j:=by
  have hpow:=pow_le_pow_left₀ (by positivity : (0:ℝ)≤outputCap K k m F) (wanted_factor_bound hK hF hb) j
  have hrR : (request:ℝ)≤(n:ℝ)*(carries:ℝ):=by exact_mod_cast hr
  have hh:=mul_le_mul hrR hpow (by positivity) (by positivity)
  simpa only [Nat.cast_mul,Nat.cast_pow,mul_pow,mul_assoc,mul_left_comm,mul_comm] using hh

/-- Individual volumes needed by scalar hash scans, the span catalog and
literal requester DFS are all present in the charged native bundle. -/
theorem bundle_components {K k b m n j : ℕ} (hK : 0<K) (hn : 1<n)
    (hfactor : 1≤nativeFactor K k b m) :
    (n:ℝ)≤volumeBundle K k b m n j ∧
    ((nativePrime K m)^j:ℝ)≤volumeBundle K k b m n j ∧
    (nativeFactor K k b m:ℝ)^j*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j≤volumeBundle K k b m n j ∧
    1≤volumeBundle K k b m n j :=by
  let D:=(nativeFactor K k b m:ℝ)^j
  let X:=(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j
  let E:=TernaryCountFrontendBudget.envelope m j
  let B:=volumeBundle K k b m n j
  have hD : 1≤D:=one_le_pow₀ (by exact_mod_cast hfactor)
  have hr : 1≤(nativePrime K m:ℝ)/(partitionCap m:ℝ):=
    (one_le_div (by unfold partitionCap; positivity)).mpr
      (by exact_mod_cast TernaryOversizeDimensions.partition_le_native hK m)
  have hX : (n:ℝ)≤X:=by
    have hh:=mul_le_mul_of_nonneg_left (one_le_pow₀ hr (n:=j)) (show (0:ℝ)≤n by positivity)
    simpa only [mul_one] using hh
  have hE : 1≤E:=TernaryCountFrontendBudget.envelope_ge_one m j
  have hnon : 0≤X:= (Nat.cast_nonneg n).trans hX
  have hq : D*X≤B:=by
    have h1:=mul_le_mul_of_nonneg_left hE (mul_nonneg (by linarith : (0:ℝ)≤D) hnon)
    have hp : 0≤D*((TernaryDimensionBounds.bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(nativePrime K m:ℝ)^j):=by positivity
    dsimp [B,volumeBundle,E,X,D] at h1 hp ⊢
    nlinarith only [h1,hp]
  have hp : (nativePrime K m:ℝ)^j≤B:=by
    have h1:=le_mul_of_one_le_left (show (0:ℝ)≤(nativePrime K m:ℝ)^j by positivity) hD
    have hnon' : 0≤D*((TernaryDimensionBounds.bankSize m j:ℝ)+(endpointSize m:ℝ)^j+X*E):=by positivity
    dsimp [B,volumeBundle,E,X,D] at h1 hnon' ⊢
    nlinarith only [h1,hnon']
  have hnB : (n:ℝ)≤B:=hX.trans ((le_mul_of_one_le_left hnon hD).trans hq)
  refine ⟨hnB,hp,?_,?_⟩
  · simpa only [D,X,mul_assoc,mul_left_comm,mul_comm] using hq
  · exact (show (1:ℝ)≤n by exact_mod_cast hn.le).trans hnB

theorem native_factor_positive {K k b m F : ℕ} (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) : 1≤nativeFactor K k b m:=by
  have hb' : 0<b:=by unfold TernaryActualPrefixRuntime.localFactor at hb; omega
  have hfamily : 0<(nativeFamily K m k).length:=lt_of_lt_of_le hFpos hF
  unfold nativeFactor
  exact Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.mul_pos hb' hfamily)
    (TernaryCoverCapParameters.rawThreshold_pos _ _ _))

/-- The literal seed score volume includes both source hash scans, the
complete requester DFS, the tensor output rows and the actual count host. -/
theorem canonical_seed_volume {K k b m n j F carries seed : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (hK : 0<K) (hn : 1<n) (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : I.nB≤n) (hC : I.nC≤n) (hrequest : I.requesterCount≤n*carries) :
    let host:=nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)
    (seedVolume D host (4^fixedLength m) F (outputCap K k m F)
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ)≤
      (2*nativePrime K m+6:ℕ)*(carries:ℝ)*volumeBundle K k b m n j+(host.runtime:ℝ):=by
  let host:=nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)
  let V:=volumeBundle K k b m n j
  have hv:=bundle_components (k:=k) (b:=b) (j:=j) hK hn (native_factor_positive hFpos hF hb)
  have hV : 0≤V:=(Nat.cast_nonneg n).trans hv.1
  have hc : (1:ℝ)≤carries:=by exact_mod_cast hcarries
  have hcarry : V≤(carries:ℝ)*V:=le_mul_of_one_le_left hV hc
  have hN : (n:ℝ)≤(carries:ℝ)*V:=hv.1.trans hcarry
  have hOne : (1:ℝ)≤(carries:ℝ)*V:=hv.2.2.2.trans hcarry
  have hreq : (I.requesterCount:ℝ)≤(carries:ℝ)*V:=by
    have hh : (I.requesterCount:ℝ)≤(n:ℝ)*(carries:ℝ):=by exact_mod_cast hrequest
    exact hh.trans (by nlinarith only [hv.1,show (0:ℝ)≤carries by positivity])
  have hwant:=wanted_work_bound (j:=j) hK hF hb hrequest
  have hwant' : ((I.requesterCount*(outputCap K k m F)^j:ℕ):ℝ)≤(carries:ℝ)*V:=by
    exact hwant.trans (by nlinarith only [hv.2.2.1,show (0:ℝ)≤carries by positivity])
  have hH : D.H (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m))≤I.requesterCount*(outputCap K k m F)^j:=by
    apply TernaryWantedBatchCount.count_le _ _ _ _ _ _ _ _ _ D.position
    intro x
    simpa [outputCap,config] using TernaryGoodOutputCatalog.localBucket_cap maps (threshold K k m) x
  have hpow : (nativePrime K m:ℝ)^(j-1)≤(nativePrime K m:ℝ)^j:=
    pow_le_pow_right₀ (by exact_mod_cast (nativePrime_prime K m).one_lt.le) (by omega)
  have hp : (nativePrime K m:ℝ)^(j-1)≤V:=hpow.trans hv.2.1
  have hpowp : (nativePrime K m:ℝ)^(j-1)*(nativePrime K m:ℝ)≤
      (nativePrime K m:ℝ)*(carries:ℝ)*V:=by
    have hh:=mul_le_mul_of_nonneg_left (hp.trans hcarry) (Nat.cast_nonneg (nativePrime K m))
    nlinarith only [hh]
  have hcat : (nativePrime K m:ℝ)^(j-1)≤(nativePrime K m:ℝ)*(carries:ℝ)*V:=by
    have hp1 : (1:ℝ)≤nativePrime K m:=by exact_mod_cast (nativePrime_prime K m).one_lt.le
    exact (hp.trans hcarry).trans (by nlinarith only [hp1,mul_nonneg (Nat.cast_nonneg carries) hV])
  have hBR : (I.nB:ℝ)≤(carries:ℝ)*V:=(show (I.nB:ℝ)≤n by exact_mod_cast hB).trans hN
  have hCR : (I.nC:ℝ)≤(carries:ℝ)*V:=(show (I.nC:ℝ)≤n by exact_mod_cast hC).trans hN
  have hHR : (D.H (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ)≤(carries:ℝ)*V:=
    (show (_:ℝ)≤((I.requesterCount*(outputCap K k m F)^j:ℕ):ℝ) by exact_mod_cast hH).trans hwant'
  dsimp only [seedVolume,config]
  push_cast
  simp only [Nat.cast_mul,Nat.cast_pow,outputCap] at hwant'
  change _≤(2*(nativePrime K m:ℝ)+6)*(carries:ℝ)*V+(host.runtime:ℝ)
  change _≤(2*(nativePrime K m:ℝ)+6)*(carries:ℝ)*V+
    ((nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)).runtime:ℝ)
  have hh:=add_le_add (add_le_add (add_le_add (add_le_add (add_le_add
    (add_le_add hcat hBR) hCR) hreq) hwant') hpowp) hHR
  have hh':=add_le_add (add_le_add hh (le_refl
    ((nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)).runtime:ℝ))) hOne
  convert hh' using 1 <;> first | rfl | ac_rfl | ring

def scoreConstant (K k c d m F D E κ : ℕ) : ℝ :=
  ((2*nativePrime K m+6+2*sourceCoefficient K m F+
    1000000*(widthCoefficient m D E κ)^3:ℕ):ℝ)*volumeConstant K k c d m

theorem volumeConstant_nonneg (K k c d m : ℕ) : 0≤volumeConstant K k c d m:=by
  unfold volumeConstant
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  exact add_nonneg (add_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le)
    (div_nonneg (Real.exp_pos _).le TernaryParameters.gibbs_parameters.2.2.1.le)

theorem scoreConstant_nonneg (K k c d m F D E κ : ℕ) : 0≤scoreConstant K k c d m F D E κ:=
  mul_nonneg (Nat.cast_nonneg _) (volumeConstant_nonneg _ _ _ _ _)

/-- A concrete physical seed evaluation, including its complete signed
fourth-tensor construction, fits the same native dimension rates. -/
theorem canonical_candidate_bound {K k b m n U κ j F carries seed D0 E : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (B V : ℕ) (hDB : D.bB≤B) (hDC : D.bC≤B) (hDO : D.bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hj : j≤radixLength m n) (hJ : radixLength m n≤A.J) (hU : U≤n^κ)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : I.nB≤n) (hC : I.nC≤n) (hrequest : I.requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : TernaryFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I)≤D0*(n+U+1)^E)
    (htime : I.queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q I).front.f (nativeHost (K:=K) (k:=k) j maps Q I).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    let host:=nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)
    (LightTernarySeedScoreFactory.runtime D host K (4^fixedLength m) F (outputCap K k m F) V
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ)≤
      (seedCoefficient K A.J (nativePrime K m) B V j:ℝ)*scoreConstant K k c d m F D0 E κ*
        (A.J+1:ℕ)^3*(carries:ℝ)*(n:ℝ)^fullExponent K k c d m:=by
  let I':=sourceInput I A seed D
  let host:=nativeHost (K:=K) (k:=k) j maps Q I'
  let W:=TernaryCountFrontendBudget.width (N m j) host.front.f host.front.g
  let H:=2*sourceCoefficient K m F+1000000*(widthCoefficient m D0 E κ)^3
  let L:=(A.J+1:ℕ)
  let T:=(n:ℝ)^fullExponent K k c d m
  have hvol:=volume_bundle_bound hK hk hgood.1 hn hj c d hpoly
  have hv:=canonical_seed_volume (j:=j) maps Q I A D hK hn hFpos hF hb hcarries hB hC hrequest
  have hh:=canonical_host_prefix_bound (j:=j) maps I' Q hK hk hgood hn hj hFpos hF hb hcarries
    hrequest hB hC hposL hposR htime c d hpoly
  have hw : W≤widthCoefficient m D0 E κ*L:=by
    have hh:=canonical_width_bound maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m))
      I' hgood.1 hn hj hU hword
    exact hh.trans (Nat.mul_le_mul_left _ (by dsimp [L]; omega))
  have hL : 1≤L:=by dsimp [L]; omega
  have hjL : j+1≤L^3:=(show j+1≤L by dsimp [L]; omega).trans
    (Nat.le_self_pow (by decide : 3≠0) _)
  have hco1 : 2*sourceCoefficient K m F*(j+1)≤2*sourceCoefficient K m F*L^3*carries:=
    (Nat.mul_le_mul_left _ hjL).trans (Nat.le_mul_of_pos_right _ hcarries)
  have hco2:=Nat.mul_le_mul_right carries (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hw 3))
  have hco : 2*sourceCoefficient K m F*(j+1)+1000000*W^3*carries≤H*L^3*carries:=by
    rw [mul_pow] at hco2
    dsimp [H]
    nlinarith only [hco1,hco2]
  have hcoR : 2*(sourceCoefficient K m F:ℝ)*(j+1:ℕ)+1000000*(W:ℝ)^3*(carries:ℝ)≤
      (H:ℝ)*(L:ℝ)^3*(carries:ℝ):=by exact_mod_cast hco
  have hh' : (host.runtime:ℝ)≤(H:ℝ)*(L:ℝ)^3*(carries:ℝ)*volumeConstant K k c d m*T:=
    hh.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoR (volumeConstant_nonneg _ _ _ _ _)) (by positivity))
  have hbase : (2*nativePrime K m+6:ℕ)≤(2*nativePrime K m+6)*L^3:=
    Nat.le_mul_of_pos_right _ (Nat.one_le_pow _ _ hL)
  have hbaseR : ((2*nativePrime K m+6:ℕ):ℝ)*(carries:ℝ)≤
      ((2*nativePrime K m+6:ℕ):ℝ)*(L:ℝ)^3*(carries:ℝ):=by
    exact_mod_cast Nat.mul_le_mul_right carries hbase
  have hv' : (seedVolume D host (4^fixedLength m) F (outputCap K k m F)
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ)≤
      scoreConstant K k c d m F D0 E κ*(L:ℝ)^3*(carries:ℝ)*T:=by
    have h1:=mul_le_mul_of_nonneg_left hvol
      (show (0:ℝ)≤((2*nativePrime K m+6:ℕ):ℝ)*(carries:ℝ) by positivity)
    have h2:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hbaseR (volumeConstant_nonneg K k c d m)) (show (0:ℝ)≤T by positivity)
    change (seedVolume D host _ _ _ _ _ _:ℝ)≤_ at hv
    unfold scoreConstant
    dsimp [H] at hh'
    dsimp only [T] at h2 hh' ⊢
    push_cast at h1 h2 hh' hv ⊢
    nlinarith only [hv,h1,h2,hh']
  have hs:=seed_runtime_shape D host K (4^fixedLength m) F (outputCap K k m F) V B
    (TernaryGoodOutputCatalog.raws maps (threshold K k m))
    (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
    (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)) hDB hDC hDO
  have hsR : (LightTernarySeedScoreFactory.runtime D host K (4^fixedLength m) F (outputCap K k m F) V
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ)≤
      (seedCoefficient K A.J (nativePrime K m) B V j:ℝ)*(seedVolume D host (4^fixedLength m) F (outputCap K k m F)
        (TernaryGoodOutputCatalog.raws maps (threshold K k m))
        (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
        (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)):ℝ):=by exact_mod_cast hs
  exact hsR.trans (by simpa only [L,T,mul_assoc] using
    mul_le_mul_of_nonneg_left hv' (Nat.cast_nonneg (seedCoefficient K A.J (nativePrime K m) B V j)))

def seedPolynomialC (K p B : ℕ) : ℕ :=
  Classical.choose (TernarySeedCoefficientBudget.seed_coefficient_polynomial K p B p)
def seedPolynomialD (K p B : ℕ) : ℕ :=
  Classical.choose (Classical.choose_spec (TernarySeedCoefficientBudget.seed_coefficient_polynomial K p B p))

theorem seed_polynomial_bound (K p B J j : ℕ) (hj : j≤J) :
    seedCoefficient K J p B (p*(p+1)^j) j≤seedPolynomialC K p B*(J+1)^seedPolynomialD K p B:=
  Classical.choose_spec (Classical.choose_spec
    (TernarySeedCoefficientBudget.seed_coefficient_polynomial K p B p)) J j hj

def menuSize (K m J : ℕ) : ℕ :=
  (nativePrime K m)^TernaryExtensionEncoding.menuDegree (nativePrime K m) (J+2) K

def prefixSeedTime {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed)) : ℕ :=
  (Finset.range (menuSize K m A.J*menuSize K m A.J)).sup fun seed=>
    LightTernarySeedScoreFactory.runtime (D seed)
      (nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed (D seed))) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m))

/-- The analysis maximum is exactly the uniform time used by the actual
canonical controller; it adds no input array or oracle to the program. -/
theorem prefixSeedTime_eq_core {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (U : ℕ) (L R : ℕ→ℕ→ℤ) :
    prefixSeedTime (K:=K) (k:=k) maps Q I A D=
      TernaryArenaControllerCore.seedTime
        (TernaryArenaControllerCore.family maps (threshold K k m)
          (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) U Q I A D L R)
        K (4^fixedLength m) F (menuSize K m A.J*menuSize K m A.J)
        (TernaryGoodOutputCatalog.raws maps (threshold K k m))
        (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
        (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m)):=rfl

private theorem cast_sup_le {s : Finset ℕ} {f : ℕ→ℕ} {V : ℝ} (hV : 0≤V)
    (h : ∀i∈s, (f i:ℝ)≤V) : ((s.sup f:ℕ):ℝ)≤V:=by
  induction s using Finset.induction_on with
  | empty => simpa using hV
  | @insert a s ha ih =>
    rw [Finset.sup_insert,Nat.cast_max]
    exact max_le (h a (Finset.mem_insert_self _ _))
      (ih (fun i hi=>h i (Finset.mem_insert_of_mem hi)))

theorem canonical_seed_max_bound {K k b m n U κ j F carries D0 E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (hDB : ∀s, (D s).bB≤B) (hDC : ∀s, (D s).bC≤B) (hDO : ∀s, (D s).bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hj : j≤radixLength m n) (hJ : radixLength m n≤A.J) (hU : U≤n^κ)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : I.nB≤n) (hC : I.nC≤n) (hrequest : I.requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : TernaryFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I)≤D0*(n+U+1)^E)
    (htime : I.queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q I).front.f (nativeHost (K:=K) (k:=k) j maps Q I).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (prefixSeedTime (K:=K) (k:=k) maps Q I A D:ℝ)≤
      (seedPolynomialC K (nativePrime K m) B:ℝ)*scoreConstant K k c d m F D0 E κ*
        (A.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+3)*(carries:ℝ)*
          (n:ℝ)^fullExponent K k c d m:=by
  unfold prefixSeedTime
  apply cast_sup_le (by positivity [scoreConstant_nonneg K k c d m F D0 E κ])
  intro seed _
  have hh:=canonical_candidate_bound (j:=j) maps Q I A (D seed) B
    ((nativePrime K m)*(nativePrime K m+1)^j) (hDB seed) (hDC seed) (hDO seed)
    hK hk hgood hn hj hJ hU hFpos hF hb hcarries hB hC hrequest hposL hposR hword htime c d hpoly
  have hp : (seedCoefficient K A.J (nativePrime K m) B ((nativePrime K m)*(nativePrime K m+1)^j) j:ℝ)≤
      (seedPolynomialC K (nativePrime K m) B:ℝ)*(A.J+1:ℕ)^seedPolynomialD K (nativePrime K m) B:=by
    exact_mod_cast seed_polynomial_bound K (nativePrime K m) B A.J j (hj.trans hJ)
  have hc:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hp (scoreConstant_nonneg K k c d m F D0 E κ))
      (show (0:ℝ)≤((A.J+1:ℕ):ℝ)^3 by positivity)) (Nat.cast_nonneg carries))
      (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
  exact hh.trans (by convert hc using 1 <;> rw [pow_add] <;> ring)

def menuCoefficient (K p : ℕ) : ℕ :=(48*p^(4*K+1)+3)^2+1
def spanCoefficient (p : ℕ) : ℕ :=(p+1)*(LightPrimeCoefficient.mulAddTime p+500)

theorem menu_square_bound (K m J : ℕ) :
    menuSize K m J*menuSize K m J+1≤menuCoefficient K (nativePrime K m)*(J+1)^2:=by
  have hp:=TernaryExtensionEncoding.menu_parameters_bound (p:=nativePrime K m) J K
  have hq : menuSize K m J≤(48*(nativePrime K m)^(4*K+1)+3)*(J+1):=by
    dsimp [menuSize]; omega
  have hh:=Nat.pow_le_pow_left hq 2
  have h1 : 1≤(J+1)^2:=Nat.one_le_pow _ _ (by omega)
  dsimp [menuCoefficient]
  rw [mul_pow] at hh
  nlinarith only [hh,h1]

theorem span_time_shape (J p rows : ℕ) :
    LightSpanCatalogStep.time J p rows≤spanCoefficient p*(J+1)*(rows+1):=by
  unfold LightSpanCatalogStep.time LightSpanCatalogBlock.time LightSpanAxpy.time spanCoefficient
  ring_nf
  omega

theorem bundle_bank_le {K k b m n j : ℕ} (hfactor : 1≤nativeFactor K k b m) :
    (TernaryDimensionBounds.bankSize m j:ℝ)≤volumeBundle K k b m n j:=by
  have hpow : (1:ℝ)≤(nativeFactor K k b m:ℝ)^j:=one_le_pow₀ (by exact_mod_cast hfactor)
  have hh:=le_mul_of_one_le_left (Nat.cast_nonneg (TernaryDimensionBounds.bankSize m j)) hpow
  unfold volumeBundle
  have hE:=TernaryCountFrontendBudget.envelope_ge_one m j
  have hnon : 0≤(nativeFactor K k b m:ℝ)^j*((endpointSize m:ℝ)^j+
      (nativePrime K m:ℝ)^j+(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*
        TernaryCountFrontendBudget.envelope m j):=by positivity
  nlinarith only [hh,hnon]

theorem prepare_time_shape (m j alpha2 : ℕ) :
    LightTernaryPrefixPrepare.time m j alpha2≤
      10000*(fixedLength m+alpha2+1)*(j+2)*(TernaryDimensionBounds.bankSize m (j+1)+1):=by
  have he:=LightTernaryEnumerationSetup.time_bound (LightTernaryPrefixSetup.N m (j+1))
    (LightTernaryPrefixSetup.T m (j+1))
  change _≤500*(LightTernaryPrefixSetup.N m (j+1)+1)*(LightTernaryPrefixSetup.nb m (j+1)+1) at he
  rw [LightTernaryPrefixSetup.nb_eq_bankSize] at he
  have hN : LightTernaryPrefixSetup.N m (j+1)=fixedLength m*(j+1):=by
    unfold LightTernaryPrefixSetup.N fixedLength; ring
  rw [hN] at he
  have hn : 1≤TernaryDimensionBounds.bankSize m (j+1)+1:=by omega
  have hh:=Nat.mul_le_mul_right (TernaryDimensionBounds.bankSize m (j+1)+1)
    (show 10000*(fixedLength m+alpha2+1)*(j+2)≥500*(fixedLength m*(j+1)+1)+
      20*(fixedLength m*(j+1))+20*(j+1)+20*(alpha2*(j+1))+30*(j+1)+8000 by nlinarith)
  have hc:=Nat.mul_le_mul_left (20*(fixedLength m*(j+1))+20*(j+1)+20*(alpha2*(j+1))+30*(j+1)+8000) hn
  unfold LightTernaryPrefixPrepare.time LightTernaryPrefixSetup.allocateTime LightTernaryPrefixSetup.time
    LightTernaryPrefixHeader.time LightNatPower.time LightTernaryRepeatWord.time
  rw [hN]
  nlinarith only [he,hh,hc]

def controllerConstant (K k c d m F D E κ B : ℕ) : ℝ :=
  (menuCoefficient K (nativePrime K m):ℝ)*
    ((seedPolynomialC K (nativePrime K m) B:ℝ)*scoreConstant K k c d m F D E κ+
      (2*spanCoefficient (nativePrime K m)+2000:ℕ)*volumeConstant K k c d m)

def prefixControllerTime {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed)) : ℕ :=
  LightTernarySeedController.time (menuSize K m A.J*menuSize K m A.J)
    (prefixSeedTime (K:=K) (k:=k) maps Q I A D)
    (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)))

theorem canonical_controller_bound {K k b m n U κ j F carries D0 E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (hDB : ∀s, (D s).bB≤B) (hDC : ∀s, (D s).bC≤B) (hDO : ∀s, (D s).bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hj : j≤radixLength m n) (hJ : radixLength m n≤A.J) (hU : U≤n^κ)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : I.nB≤n) (hC : I.nC≤n) (hrequest : I.requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : TernaryFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I)≤D0*(n+U+1)^E)
    (htime : I.queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q I).front.f (nativeHost (K:=K) (k:=k) j maps Q I).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (prefixControllerTime (K:=K) (k:=k) maps Q I A D:ℝ)≤
      controllerConstant K k c d m F D0 E κ B*
        (A.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+5)*(carries:ℝ)*
          (n:ℝ)^fullExponent K k c d m:=by
  let V:=volumeBundle K k b m n j
  let Z:=(A.J+1:ℕ)
  let e:=seedPolynomialD K (nativePrime K m) B+3
  let T:=(n:ℝ)^fullExponent K k c d m
  have hv:=bundle_components (k:=k) (b:=b) (j:=j) hK hn (native_factor_positive hFpos hF hb)
  have hvol:=volume_bundle_bound hK hk hgood.1 hn hj c d hpoly
  have hrows : ((nativePrime K m:ℝ)^(j-1)+1)≤2*V:=by
    have hp:=pow_le_pow_right₀ (show (1:ℝ)≤nativePrime K m by exact_mod_cast (nativePrime_prime K m).one_lt.le)
      (show j-1≤j by omega)
    nlinarith only [hp,hv.2.1,hv.2.2.2]
  have hspan0:=span_time_shape A.J (nativePrime K m) ((nativePrime K m)^(j-1))
  have hspan : (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)):ℝ)≤
      2*(spanCoefficient (nativePrime K m):ℝ)*(Z:ℝ)*V:=by
    have hh : (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)):ℝ)≤
      (spanCoefficient (nativePrime K m):ℝ)*(Z:ℝ)*((nativePrime K m:ℝ)^(j-1)+1):=by exact_mod_cast hspan0
    have hh':=mul_le_mul_of_nonneg_left hrows
      (show (0:ℝ)≤(spanCoefficient (nativePrime K m):ℝ)*(Z:ℝ) by positivity)
    exact hh.trans (by nlinarith only [hh'])
  have hZ : (1:ℝ)≤Z:=by dsimp [Z]; exact_mod_cast (show 1≤A.J+1 by omega)
  have he : (Z:ℝ)≤(Z:ℝ)^e:=by
    simpa only [pow_one] using pow_le_pow_right₀ hZ (show 1≤e by dsimp [e]; omega)
  have hZe : (Z:ℝ)≤(Z:ℝ)^e*(carries:ℝ):=
    he.trans (le_mul_of_one_le_right (by positivity) (by exact_mod_cast hcarries))
  have hconst : (2000:ℝ)≤2000*(Z:ℝ)*V:=by nlinarith only [hZ,hv.2.2.2]
  have haux0 : (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)):ℝ)+2000≤
      (2*spanCoefficient (nativePrime K m)+2000:ℕ)*(Z:ℝ)^e*(carries:ℝ)*V:=by
    have hh:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hZe
      (show (0:ℝ)≤(2*spanCoefficient (nativePrime K m)+2000:ℕ) by positivity))
      (show (0:ℝ)≤V by exact le_trans (by norm_num) hv.2.2.2)
    push_cast at hh ⊢
    nlinarith only [hspan,hconst,hh]
  have haux : (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)):ℝ)+2000≤
      (2*spanCoefficient (nativePrime K m)+2000:ℕ)*(Z:ℝ)^e*(carries:ℝ)*volumeConstant K k c d m*T:=by
    have hh:=mul_le_mul_of_nonneg_left hvol
      (show (0:ℝ)≤(2*spanCoefficient (nativePrime K m)+2000:ℕ)*(Z:ℝ)^e*(carries:ℝ) by positivity)
    simpa only [mul_assoc,T] using haux0.trans hh
  have hs:=canonical_seed_max_bound (j:=j) maps Q I A D hDB hDC hDO
    hK hk hgood hn hj hJ hU hFpos hF hb hcarries hB hC hrequest hposL hposR hword htime c d hpoly
  have hsum : (prefixSeedTime (K:=K) (k:=k) maps Q I A D:ℝ)+
      (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)):ℝ)+2000≤
      ((seedPolynomialC K (nativePrime K m) B:ℝ)*scoreConstant K k c d m F D0 E κ+
        (2*spanCoefficient (nativePrime K m)+2000:ℕ)*volumeConstant K k c d m)*
          (Z:ℝ)^e*(carries:ℝ)*T:=by
    dsimp [Z,e,T] at *
    nlinarith only [hs,haux]
  have hmenu : ((menuSize K m A.J*menuSize K m A.J+1:ℕ):ℝ)≤
      (menuCoefficient K (nativePrime K m):ℝ)*(Z:ℝ)^2:=by exact_mod_cast menu_square_bound K m A.J
  have ht:=all_seed_time_shape (menuSize K m A.J)
    (prefixSeedTime (K:=K) (k:=k) maps Q I A D)
    (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)))
  have htR : (prefixControllerTime (K:=K) (k:=k) maps Q I A D:ℝ)≤
      ((menuSize K m A.J*menuSize K m A.J+1:ℕ):ℝ)*
        ((prefixSeedTime (K:=K) (k:=k) maps Q I A D:ℝ)+
          (LightSpanCatalogStep.time A.J (nativePrime K m) ((nativePrime K m)^(j-1)):ℝ)+2000):=by exact_mod_cast ht
  have hh:=mul_le_mul hmenu hsum (by positivity) (by positivity)
  apply htR.trans
  convert hh using 1 <;> unfold controllerConstant <;> dsimp [Z,e,T] <;> rw [pow_add] <;> ring

def overheadCoefficient (m : ℕ) : ℕ :=40000*(fixedLength m+fixedAlpha m 2+1)+10000
def prefixOverhead (m j J p nB nC nO : ℕ) : ℕ :=
  LightTernaryPrefixPrepare.time m (j-1) (fixedAlpha m 2)+
    LightTernaryCommitKeys.time nB nC nO+copyTime (p^j*J)+5500

theorem prefix_overhead_bound {m j J p n nB nC nO carries : ℕ} {V : ℝ}
    (hj : 1≤j) (hJ : j≤J) (hcarries : 1≤carries)
    (hnB : nB≤n) (hnC : nC≤n) (hnO : nO≤n*carries)
    (h1 : 1≤V) (hn : (n:ℝ)≤V) (hp : (p:ℝ)^j≤V)
    (hbank : (TernaryDimensionBounds.bankSize m j:ℝ)≤V) :
    (prefixOverhead m j J p nB nC nO:ℝ)≤(overheadCoefficient m:ℝ)*(J+1:ℕ)*(carries:ℝ)*V:=by
  let Z:=(J+1:ℕ)
  let W:=(Z:ℝ)*(carries:ℝ)*V
  have hZ : (1:ℝ)≤Z:=by dsimp [Z]; exact_mod_cast (show 1≤J+1 by omega)
  have hc : (1:ℝ)≤carries:=by exact_mod_cast hcarries
  have hV : 0≤V:=le_trans (by norm_num) h1
  have hCV : V≤(carries:ℝ)*V:=le_mul_of_one_le_left hV hc
  have hVW : (carries:ℝ)*V≤W:=by
    have hh:=le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg carries) hV) hZ
    simpa only [W,mul_assoc] using hh
  have hVW' : V≤W:=hCV.trans hVW
  have hW : 1≤W:=h1.trans hVW'
  have hnB' : (nB:ℝ)≤W:=(show (nB:ℝ)≤n by exact_mod_cast hnB).trans (hn.trans hVW')
  have hnC' : (nC:ℝ)≤W:=(show (nC:ℝ)≤n by exact_mod_cast hnC).trans (hn.trans hVW')
  have hnO' : (nO:ℝ)≤W:=by
    have hh : (nO:ℝ)≤(n:ℝ)*(carries:ℝ):=by exact_mod_cast hnO
    have hh' : (n:ℝ)*(carries:ℝ)≤(carries:ℝ)*V:=by nlinarith only [hn,show (0:ℝ)≤carries by positivity]
    exact hh.trans (hh'.trans hVW)
  have hcopy : ((p^j*J:ℕ):ℝ)≤W:=by
    have hh:=mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤J by positivity)
    have hh' : (J:ℝ)*V≤(Z:ℝ)*V:=by dsimp [Z]; push_cast; nlinarith
    have hh'' : (Z:ℝ)*V≤W:=by dsimp [W]; nlinarith only [hCV,show (0:ℝ)≤Z by positivity]
    push_cast
    nlinarith only [hh,hh',hh'']
  have hp0:=prepare_time_shape m (j-1) (fixedAlpha m 2)
  rw [Nat.sub_add_cancel hj] at hp0
  have hpR : (LightTernaryPrefixPrepare.time m (j-1) (fixedAlpha m 2):ℝ)≤
      10000*(fixedLength m+fixedAlpha m 2+1:ℕ)*(j-1+2:ℕ)*
        (TernaryDimensionBounds.bankSize m j+1:ℕ):=by exact_mod_cast hp0
  have hjR : ((j-1+2:ℕ):ℝ)≤2*(Z:ℝ):=by exact_mod_cast (show j-1+2≤2*Z by dsimp [Z]; omega)
  have hbR : ((TernaryDimensionBounds.bankSize m j+1:ℕ):ℝ)≤2*V:=by push_cast; linarith
  have hpre : (LightTernaryPrefixPrepare.time m (j-1) (fixedAlpha m 2):ℝ)≤
      (40000*(fixedLength m+fixedAlpha m 2+1):ℕ)*W:=by
    have hh:=mul_le_mul hjR hbR (by positivity) (by positivity)
    have hh':=mul_le_mul_of_nonneg_left hh
      (show (0:ℝ)≤10000*(fixedLength m+fixedAlpha m 2+1:ℕ) by positivity)
    have hh'':=mul_le_mul_of_nonneg_left hCV
      (show (0:ℝ)≤40000*(fixedLength m+fixedAlpha m 2+1:ℕ)*(Z:ℝ) by positivity)
    push_cast at hpR hh' hh'' ⊢
    dsimp [W]
    nlinarith only [hpR,hh',hh'']
  unfold prefixOverhead overheadCoefficient LightTernaryCommitKeys.time copyTime
  dsimp [W,Z] at hW hnB' hnC' hnO' hcopy hpre
  push_cast at hW hnB' hnC' hnO' hcopy hpre ⊢
  nlinarith only [hpre,hnB',hnC',hnO',hcopy,hW]

def prefixStageTime {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed)) : ℕ :=
  prefixControllerTime (K:=K) (k:=k) maps Q I A D+
    prefixOverhead m j A.J (nativePrime K m) I.nB I.nC I.requesterCount

/-- Equality with the actual prepare/controller/commit machine timing at
the next prefix; every mutable key and span copy is included. -/
theorem prefixStageTime_eq_step {K k m F old : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) (old+1) I A seed))
    (X : LightTernaryPrefixStep.Inputs) (hm : X.m=m) (hj : X.j=old) (hp : X.p=nativePrime K m)
    (ha : X.alpha2=fixedAlpha m 2) (hpow : X.power=(nativePrime K m)^old) :
    prefixStageTime (K:=K) (k:=k) maps Q I A D=
      LightTernaryPrefixStep.time X (config (nativePrime K m) (old+1) I A 0)
        (menuSize K m A.J*menuSize K m A.J) (prefixSeedTime (K:=K) (k:=k) maps Q I A D):=by
  unfold prefixStageTime prefixControllerTime prefixOverhead LightTernaryPrefixStep.time
    LightTernaryPrefixFinish.time
  rw [hm,hj,ha,hpow,hp,←pow_succ]
  dsimp only [config]
  simp only [Nat.add_sub_cancel_right,Nat.add_sub_cancel_left]
  ring

def stageConstant (K k c d m F D E κ B : ℕ) : ℝ :=
  controllerConstant K k c d m F D E κ B+(overheadCoefficient m:ℝ)*volumeConstant K k c d m

theorem canonical_stage_bound {K k b m n U κ j F carries D0 E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : (seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed))
    (hDB : ∀s, (D s).bB≤B) (hDC : ∀s, (D s).bC≤B) (hDO : ∀s, (D s).bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hjpos : 1≤j) (hj : j≤radixLength m n) (hJ : radixLength m n≤A.J) (hU : U≤n^κ)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : I.nB≤n) (hC : I.nC≤n) (hrequest : I.requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : TernaryFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I)≤D0*(n+U+1)^E)
    (htime : I.queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q I).front.f (nativeHost (K:=K) (k:=k) j maps Q I).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (prefixStageTime (K:=K) (k:=k) maps Q I A D:ℝ)≤
      stageConstant K k c d m F D0 E κ B*
        (A.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+5)*(carries:ℝ)*
          (n:ℝ)^fullExponent K k c d m:=by
  have hs:=canonical_controller_bound (j:=j) maps Q I A D hDB hDC hDO
    hK hk hgood hn hj hJ hU hFpos hF hb hcarries hB hC hrequest hposL hposR hword htime c d hpoly
  have hv:=bundle_components (k:=k) (b:=b) (j:=j) hK hn (native_factor_positive hFpos hF hb)
  have hbv:=bundle_bank_le (j:=j) (n:=n) (native_factor_positive hFpos hF hb)
  have ha:=prefix_overhead_bound hjpos (hj.trans hJ) hcarries hB hC hrequest
    hv.2.2.2 hv.1 hv.2.1 hbv
  have hvol:=volume_bundle_bound hK hk hgood.1 hn hj c d hpoly
  have hpow : ((A.J+1:ℕ):ℝ)≤((A.J+1:ℕ):ℝ)^(seedPolynomialD K (nativePrime K m) B+5):=by
    simpa only [pow_one] using pow_le_pow_right₀ (show (1:ℝ)≤(A.J+1:ℕ) by exact_mod_cast (show 1≤A.J+1 by omega))
      (show 1≤seedPolynomialD K (nativePrime K m) B+5 by omega)
  have haux1:=mul_le_mul_of_nonneg_left hvol
    (show (0:ℝ)≤(overheadCoefficient m:ℝ)*(A.J+1:ℕ)*(carries:ℝ) by positivity)
  have haux2:=mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow (Nat.cast_nonneg (overheadCoefficient m))) (Nat.cast_nonneg carries))
        (volumeConstant_nonneg K k c d m)) (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
  unfold prefixStageTime stageConstant
  push_cast at hs ha haux1 haux2 ⊢
  nlinarith only [hs,ha,haux1,haux2]

theorem stageConstant_nonneg (K k c d m F D E κ B : ℕ) :
    0≤stageConstant K k c d m F D E κ B:=by
  unfold stageConstant controllerConstant
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _) (add_nonneg
      (mul_nonneg (Nat.cast_nonneg _) (scoreConstant_nonneg _ _ _ _ _ _ _ _ _))
      (mul_nonneg (Nat.cast_nonneg _) (volumeConstant_nonneg _ _ _ _ _))))
    (mul_nonneg (Nat.cast_nonneg _) (volumeConstant_nonneg _ _ _ _ _))

def allStageTime {K k m F : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : ℕ→Input) (A : Inputs)
    (D : (j seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j (I j) A seed))
    (n : ℕ) : ℕ :=
  (Finset.range (radixLength m n)).sup fun old=>
    prefixStageTime (K:=K) (k:=k) maps Q (I (old+1)) A (D (old+1))

def allPrefixTime {K k m F : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : ℕ→Input) (A : Inputs)
    (D : (j seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j (I j) A seed))
    (n : ℕ) : ℕ :=
  LightTernaryPrefixInit.time (config (nativePrime K m) 0 (I 0) A 0)
    (radixLength m n) (allStageTime (K:=K) (k:=k) maps Q I A D n)

theorem canonical_all_stage_bound {K k b m n U κ F carries D0 E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : ℕ→Input) (A : Inputs)
    (D : (j seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j (I j) A seed))
    (hDB : ∀j≤radixLength m n,∀s, (D j s).bB≤B)
    (hDC : ∀j≤radixLength m n,∀s, (D j s).bC≤B)
    (hDO : ∀j≤radixLength m n,∀s, (D j s).bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hJ : radixLength m n≤A.J) (hU : U≤n^κ)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : ∀j≤radixLength m n,(I j).nB≤n) (hC : ∀j≤radixLength m n,(I j).nC≤n)
    (hrequest : ∀j≤radixLength m n,(I j).requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀j≤radixLength m n,TernaryFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) (I j))≤D0*(n+U+1)^E)
    (htime : ∀j≤radixLength m n,(I j).queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (allStageTime (K:=K) (k:=k) maps Q I A D n:ℝ)≤
      stageConstant K k c d m F D0 E κ B*
        (A.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+5)*(carries:ℝ)*
          (n:ℝ)^fullExponent K k c d m:=by
  unfold allStageTime
  apply cast_sup_le (by positivity [stageConstant_nonneg K k c d m F D0 E κ B])
  intro old hold
  have hj : old+1≤radixLength m n:=Finset.mem_range.mp hold
  exact canonical_stage_bound (j:=old+1) maps Q (I (old+1)) A (D (old+1))
    (hDB _ hj) (hDC _ hj) (hDO _ hj) hK hk hgood hn (by omega) hj hJ hU hFpos hF hb hcarries
    (hB _ hj) (hC _ hj) (hrequest _ hj) hposL hposR (hword _ hj) (htime _ hj) c d hpoly

theorem prefix_init_shape (C : LightTernarySeedScoreFactory.Config) (rounds T : ℕ) :
    LightTernaryPrefixInit.time C rounds T≤
      (rounds+1)*(T+10000*(C.nB+C.nC+C.nO+C.J+1)):=by
  unfold LightTernaryPrefixInit.time LightTernaryInitialKeys.time LightTernaryPrefixLoop.time copyTime fillTime
  ring_nf
  omega

def prefixConstant (K k c d m F D E κ B : ℕ) : ℝ :=
  stageConstant K k c d m F D E κ B+50000*volumeConstant K k c d m

theorem prefixConstant_nonneg (K k c d m F D E κ B : ℕ) :
    0≤prefixConstant K k c d m F D E κ B:=
  add_nonneg (stageConstant_nonneg _ _ _ _ _ _ _ _ _ _) (by positivity [volumeConstant_nonneg K k c d m])

theorem canonical_all_prefix_bound {K k b m n U κ F carries D0 E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : ℕ→Input) (A : Inputs)
    (D : (j seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j (I j) A seed))
    (hDB : ∀j≤radixLength m n,∀s, (D j s).bB≤B)
    (hDC : ∀j≤radixLength m n,∀s, (D j s).bC≤B)
    (hDO : ∀j≤radixLength m n,∀s, (D j s).bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hJ : radixLength m n≤A.J) (hU : U≤n^κ)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b) (hcarries : 1≤carries)
    (hB : ∀j≤radixLength m n,(I j).nB≤n) (hC : ∀j≤radixLength m n,(I j).nC≤n)
    (hrequest : ∀j≤radixLength m n,(I j).requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀j≤radixLength m n,TernaryFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) (I j))≤D0*(n+U+1)^E)
    (htime : ∀j≤radixLength m n,(I j).queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (allPrefixTime (K:=K) (k:=k) maps Q I A D n:ℝ)≤
      prefixConstant K k c d m F D0 E κ B*
        (A.J+1:ℕ)^(seedPolynomialD K (nativePrime K m) B+6)*(carries:ℝ)*
          (n:ℝ)^fullExponent K k c d m:=by
  let Z:=(A.J+1:ℕ)
  let T:=(n:ℝ)^fullExponent K k c d m
  let e:=seedPolynomialD K (nativePrime K m) B+5
  let V:=volumeBundle K k b m n 0
  have hv:=bundle_components (k:=k) (b:=b) (j:=0) hK hn (native_factor_positive hFpos hF hb)
  have hvol:=volume_bundle_bound (j:=0) hK hk hgood.1 hn (by omega) c d hpoly
  have hs:=canonical_all_stage_bound maps Q I A D hDB hDC hDO hK hk hgood hn hJ hU
    hFpos hF hb hcarries hB hC hrequest hposL hposR hword htime c d hpoly
  have hZ : (1:ℝ)≤Z:=by dsimp [Z]; exact_mod_cast (show 1≤A.J+1 by omega)
  have hc : (1:ℝ)≤carries:=by exact_mod_cast hcarries
  have hCV : V≤(carries:ℝ)*V:=le_mul_of_one_le_left
    (show (0:ℝ)≤V by exact le_trans (by norm_num) hv.2.2.2) hc
  have hZCV : (carries:ℝ)*V≤(Z:ℝ)*(carries:ℝ)*V:=by
    have hh:=le_mul_of_one_le_left (mul_nonneg (Nat.cast_nonneg carries)
      (show (0:ℝ)≤V by exact le_trans (by norm_num) hv.2.2.2)) hZ
    simpa only [mul_assoc] using hh
  have hnZ : (n:ℝ)≤(Z:ℝ)*(carries:ℝ)*V:=hv.1.trans (hCV.trans hZCV)
  have hO : ((I 0).requesterCount:ℝ)≤(Z:ℝ)*(carries:ℝ)*V:=by
    have hh : ((I 0).requesterCount:ℝ)≤(n:ℝ)*(carries:ℝ):=by exact_mod_cast hrequest 0 (by omega)
    have hh' : (n:ℝ)*(carries:ℝ)≤(carries:ℝ)*V:=by
      nlinarith only [hv.1,show (0:ℝ)≤carries by positivity]
    exact hh.trans (hh'.trans hZCV)
  have hB0 : ((I 0).nB:ℝ)≤(Z:ℝ)*(carries:ℝ)*V:=
    (show ((I 0).nB:ℝ)≤n by exact_mod_cast hB 0 (by omega)).trans hnZ
  have hC0 : ((I 0).nC:ℝ)≤(Z:ℝ)*(carries:ℝ)*V:=
    (show ((I 0).nC:ℝ)≤n by exact_mod_cast hC 0 (by omega)).trans hnZ
  have hJ0 : (A.J:ℝ)+1≤(Z:ℝ)*(carries:ℝ)*V:=by
    have hh : (1:ℝ)≤(carries:ℝ)*V:=hv.2.2.2.trans hCV
    dsimp [Z]
    push_cast
    nlinarith only [hh,show (0:ℝ)≤A.J by positivity]
  have hcounts : ((I 0).nB+(I 0).nC+(I 0).requesterCount+A.J+1:ℕ)≤
      5*(Z:ℝ)*(carries:ℝ)*V:=by push_cast; nlinarith only [hB0,hC0,hO,hJ0]
  have hp : (Z:ℝ)≤(Z:ℝ)^e:=by
    simpa only [pow_one] using pow_le_pow_right₀ hZ (show 1≤e by dsimp [e]; omega)
  have hcounts' : ((I 0).nB+(I 0).nC+(I 0).requesterCount+A.J+1:ℕ)≤
      5*(Z:ℝ)^e*(carries:ℝ)*volumeConstant K k c d m*T:=by
    have h1:=mul_le_mul_of_nonneg_left hvol
      (show (0:ℝ)≤5*(Z:ℝ)*(carries:ℝ) by positivity)
    have h2:=mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (by norm_num : (0:ℝ)≤5))
        (Nat.cast_nonneg carries)) (volumeConstant_nonneg K k c d m)) (show (0:ℝ)≤T by positivity)
    dsimp [T] at h2 ⊢
    nlinarith only [hcounts,h1,h2]
  have hsum : (allStageTime (K:=K) (k:=k) maps Q I A D n:ℝ)+
      10000*((I 0).nB+(I 0).nC+(I 0).requesterCount+A.J+1:ℕ)≤
      prefixConstant K k c d m F D0 E κ B*(Z:ℝ)^e*(carries:ℝ)*T:=by
    unfold prefixConstant
    dsimp [Z,e,T] at *
    nlinarith only [hs,hcounts']
  have hinit:=prefix_init_shape (config (nativePrime K m) 0 (I 0) A 0)
    (radixLength m n) (allStageTime (K:=K) (k:=k) maps Q I A D n)
  have hinitR : (allPrefixTime (K:=K) (k:=k) maps Q I A D n:ℝ)≤
      (radixLength m n+1:ℕ)*((allStageTime (K:=K) (k:=k) maps Q I A D n:ℝ)+
        10000*((I 0).nB+(I 0).nC+(I 0).requesterCount+A.J+1:ℕ)):=by exact_mod_cast hinit
  have hR : ((radixLength m n+1:ℕ):ℝ)≤Z:=by exact_mod_cast Nat.add_le_add_right hJ 1
  have hh:=mul_le_mul hR hsum (by positivity) (by positivity)
  apply hinitR.trans
  convert hh using 1 <;> dsimp [Z,e,T] <;> rw [pow_add] <;> ring

/-- The executed seed scan, reconstruction, bank initialization, all
prefix commits and the physical loop have the claimed asymptotic rate.
Every hypothesis concerns fixed parameters or actual finite input data;
there is no supplied running-time or execution receipt. -/
theorem all_prefix_eventually {K k b m κ F D0 E B β : ℕ} {δ ε : ℝ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : ℕ→ℕ→Input) (A : ℕ→Inputs) (U : ℕ→ℕ)
    (D : (n j seed : ℕ)→LightTernarySeedScoreFactory.Data (config (nativePrime K m) j (I n j) (A n) seed))
    (hDB : ∀n,1<n→∀j≤radixLength m n,∀s,(D n j s).bB≤B)
    (hDC : ∀n,1<n→∀j≤radixLength m n,∀s,(D n j s).bC≤B)
    (hDO : ∀n,1<n→∀j≤radixLength m n,∀s,(D n j s).bO≤B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hβ : 1<β)
    (hJ : ∀n,(A n).J=TernarySignedPadding.paddedLength β (U n) (radixLength m n))
    (hU : ∀n,1<n→U n≤n^κ) (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hB : ∀n,1<n→∀j≤radixLength m n,(I n j).nB≤n)
    (hC : ∀n,1<n→∀j≤radixLength m n,(I n j).nC≤n)
    (hrequest : ∀n,1<n→∀j≤radixLength m n,(I n j).requesterCount≤n*2^(A n).J)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀n,1<n→∀j≤radixLength m n,TernaryFrontendResources.eulerBound (N m j)
      (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) (I n j))≤D0*(n+U n+1)^E)
    (htime : ∀n,1<n→∀j≤radixLength m n,(I n j).queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcarry : TernarySignedPadding.carryExponent m β (κ:ℝ)<δ) (hε : 0<ε)
    (hgap : fullExponent K k c d m+δ+ε<TernaryParameters.targetExponent) :
    ∀ᶠ n : ℕ in atTop,
      (allPrefixTime (K:=K) (k:=k) maps Q (I n) (A n) (D n) n:ℝ)≤
        (n:ℝ)^TernaryParameters.targetExponent:=by
  let C:=prefixConstant K k c d m F D0 E κ B
  let degree:=seedPolynomialD K (nativePrime K m) B+6
  have hC0 : 0≤C:=prefixConstant_nonneg _ _ _ _ _ _ _ _ _ _
  have hκ : (0:ℝ)≤κ:=Nat.cast_nonneg _
  have hUR : ∀n,1<n→(U n:ℝ)≤(n:ℝ)^(κ:ℝ):=by
    intro n hn
    simpa only [Real.rpow_natCast,Nat.cast_pow] using
      (show (U n:ℝ)≤(n^κ:ℕ) by exact_mod_cast hU n hn)
  have hcar:=TernarySignedPadding.padded_carry_eventually hgood.1 hβ hκ hcarry U hUR
  have hpol:=TernarySignedPreparationBudget.polynomial_digit_budget hgood.1 hβ hκ hε C hC0 degree U hUR
  filter_upwards [hcar,hpol,eventually_gt_atTop (1:ℕ)] with n hcarN hpolN hn
  have hJR : radixLength m n≤(A n).J:=by
    rw [hJ]
    unfold TernarySignedPadding.paddedLength
    omega
  have hbin : 1≤((Nat.log 2 (3*U n+1):ℝ)+2)^degree:=one_le_pow₀ (by
    have hh : (0:ℝ)≤Nat.log 2 (3*U n+1):=Nat.cast_nonneg _
    linarith)
  have hdrop : C*((A n).J+1:ℕ)^degree≤(n:ℝ)^ε:=by
    have hh:=le_mul_of_one_le_right (show (0:ℝ)≤C*((A n).J+1:ℕ)^degree by positivity) hbin
    exact hh.trans (by simpa [hJ] using hpolN)
  have hfinite:=canonical_all_prefix_bound (n:=n) (U:=U n) (κ:=κ) (carries:=2^(A n).J)
    (D0:=D0) (E:=E) (B:=B) maps Q (I n) (A n) (D n) (hDB n hn) (hDC n hn) (hDO n hn)
    hK hk hgood hn hJR (hU n hn) hFpos hF hb (Nat.one_le_pow _ _ (by decide))
    (hB n hn) (hC n hn) (hrequest n hn) hposL hposR (hword n hn) (htime n hn) c d hpoly
  have hfinite' : (allPrefixTime (K:=K) (k:=k) maps Q (I n) (A n) (D n) n:ℝ)≤
      C*((A n).J+1:ℕ)^degree*(2:ℝ)^(A n).J*(n:ℝ)^fullExponent K k c d m:=by
    simpa only [C,degree,Nat.cast_pow,Nat.cast_ofNat] using hfinite
  have hcarryN : (2:ℝ)^(A n).J≤(n:ℝ)^δ:=by simpa only [hJ] using hcarN
  have hsmall:=mul_le_mul hdrop hcarryN (by positivity) (show (0:ℝ)≤(n:ℝ)^ε by positivity)
  have hsmall':=mul_le_mul_of_nonneg_right hsmall (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
  have hnR : (0:ℝ)<n:=by exact_mod_cast lt_trans Nat.zero_lt_one hn
  calc
    _≤C*((A n).J+1:ℕ)^degree*(2:ℝ)^(A n).J*(n:ℝ)^fullExponent K k c d m:=hfinite'
    _≤(n:ℝ)^ε*(n:ℝ)^δ*(n:ℝ)^fullExponent K k c d m:=hsmall'
    _=(n:ℝ)^(fullExponent K k c d m+δ+ε):=by
      rw [←Real.rpow_add hnR,←Real.rpow_add hnR]; congr 1; ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hgap.le

end ThreeSum.TernaryActualSeedRuntime
