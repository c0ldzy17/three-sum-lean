import Submission.ThreeSum.LightTernarySourceHostBudget
import Submission.ThreeSum.TernaryWantedDictionaryFiber
import Submission.ThreeSum.TernaryArenaQueryTime
import Submission.ThreeSum.TernaryOversizeDimensions
import Submission.ThreeSum.TernaryMomentReporterBudget
import Submission.ThreeSum.LightTernarySeedControllerBudget
import Submission.ThreeSum.LightTernarySeedScoreFactory
import Submission.ThreeSum.TernarySignedPreparationBudget
import Submission.ThreeSum.TernaryExtensionBudget

/-! Concrete running times of the initialized source/count and scoring
programs. Dictionary generation, joins, signed histogram construction and
all seed evaluations are charged explicitly. -/
noncomputable section
namespace ThreeSum.TernaryActualPrefixRuntime
open Light Real Filter Asymptotics
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend
open TernaryEntropyRates TernaryDimensionBounds TernaryOversizePrime
open TernaryOversizeRates TernaryOversizeOverhead TernaryCoverScale
open scoped BigOperators Topology
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

/-- Every repeated key occurrence is counted. No injectivity of key values
is used to turn the physical histogram into a dictionary fiber. -/
theorem histogram_filter (xs : List ℤ) (f : ℤ→ℕ) (a : ℕ) :
    LightHistogram.count (fun j=>f (xs.getD j 0)) a xs.length=
      (xs.filter (fun z=>f z=a)).length :=by
  let q : ℕ→Bool:=fun j=>decide (f (xs.getD j 0)=a)
  have hn : ((List.range xs.length).filter q).Nodup:=List.nodup_range.filter _
  have hc:=List.toFinset_card_of_nodup hn
  have he : ((List.range xs.length).filter q).toFinset=
      (Finset.range xs.length).filter (fun j=>f (xs.getD j 0)=a) :=by
    ext j
    simp [q]
  rw [he] at hc
  unfold LightHistogram.count
  rw [hc]
  have hf : (xs.filter (fun z=>f z=a)).length=
      ((List.range xs.length).filter q).length :=by
    conv_lhs=>rw [←TernaryCanonicalFibers.map_range_getD xs 0]
    rw [List.filter_map,List.length_map]
    rfl
  exact hf.symm

/-- Actual per-original source join cap in the exact histogram API consumed
by SourceHostBudget. It includes all map-labelled duplicate key records. -/
theorem source_histogram_cap {p m F : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (cap r : ℕ) (right : Bool) (hp : 2<p) (x : ℤ) :
    let xs:=(localRecords maps cap right).map (TernaryCanonicalDictionaries.native right maps)
    LightHistogram.count
      (fun j=>WantedResidueKeys.code (p^r) 0 (LightTernarySourceHost.dictionary xs p r j))
      (WantedResidueKeys.code (p^r) 0 x) (LightTernarySourceHost.size xs r)≤(F*cap)^r :=by
  let xs:=(localRecords maps cap right).map (TernaryCanonicalDictionaries.native right maps)
  have hlen : (RadixKeyLists.values (p:ℤ) xs r).length=LightTernarySourceHost.size xs r :=by
    simp [RadixKeyLists.values_length,LightTernarySourceHost.size]
  have hpR : 0<p^r:=pow_pos (Fact.out : p.Prime).pos _
  have h:=histogram_filter (RadixKeyLists.values (p:ℤ) xs r)
    (WantedResidueKeys.code (p^r) 0) (WantedResidueKeys.code (p^r) 0 x)
  simp only [LightTernarySourceHost.dictionary] at ⊢
  rw [←hlen,h]
  have he : (fun z : ℤ=>decide (WantedResidueKeys.code (p^r) 0 z=
      WantedResidueKeys.code (p^r) 0 x))=(fun z=>decide ((p:ℤ)^r∣x-z)) :=by
    funext z
    apply decide_eq_decide.mpr
    simpa only [Int.natCast_pow,Int.add_zero] using WantedResidueKeys.code_eq_iff hpR x z 0
  rw [he]
  simpa [xs,localRecords] using
    TernaryWantedDictionaryFiber.source_values_fiber_cap (α:=fixedAlpha m) right maps cap hp r x


def sourceWidth (J L U M : ℕ) :=J+L+Nat.log 2 (U+1)+Nat.log 2 (M+1)+3

def sourceVolume (xs : List ℤ) (J M NL bank groups cap : ℕ) :=
  NL+LightTernarySourceHost.size xs J+xs.length+M+NL*cap+groups*bank+1

/-- Bound for the literal SourceHost time function, including all three
product dictionaries and the bucket setup even when it emits few matches. -/
theorem source_time_shape (xs ys zs : List ℤ) (hxy : ys.length=xs.length)
    (hxz : zs.length=xs.length) (hm : 1≤xs.length)
    (p J M NL U L bank groups cap : ℕ) (input : ℕ→ℤ)
    (hcap : ∀i<NL, LightHistogram.count
      (fun j=>WantedResidueKeys.code M 0 (LightTernarySourceHost.dictionary xs p J j))
      (WantedResidueKeys.code M 0 (input i)) (LightTernarySourceHost.size xs J)≤cap) :
    LightTernarySourceHost.time xs ys zs p J M NL U L bank groups input≤
      8000*sourceWidth J L U M*sourceVolume xs J M NL bank groups cap :=by
  let W:=sourceWidth J L U M
  let V:=sourceVolume xs J M NL bank groups cap
  have hW : 1≤W :=by dsimp [W,sourceWidth]; omega
  have hV : 1≤V :=by dsimp [V,sourceVolume]; omega
  have hwJ : J+1≤W :=by dsimp [W,sourceWidth]; omega
  have hwLog : Nat.log 2 (U+1)+Nat.log 2 (M+1)+1≤W :=by dsimp [W,sourceWidth]; omega
  have hwL : L+1≤W :=by dsimp [W,sourceWidth]; omega
  have hvDict : LightTernarySourceHost.size xs J+xs.length+1≤V :=by dsimp [V,sourceVolume]; omega
  have hvJoin : NL+LightTernarySourceHost.size xs J+M+NL*cap+1≤V :=by dsimp [V,sourceVolume]; omega
  have hvHist : NL*cap+groups*bank+1≤V :=by dsimp [V,sourceVolume]; omega
  have hDict:=Nat.mul_le_mul hwJ hvDict
  have hJoin:=Nat.mul_le_mul hvJoin hwLog
  have hHist:=Nat.mul_le_mul hwL hvHist
  have hUnit : 1≤W*V:=Nat.mul_le_mul hW hV
  have h:=LightTernarySourceHostBudget.time_bound xs ys zs hxy hxz hm
    p J M NL U L bank groups cap input hcap
  dsimp [W,V] at hDict hJoin hHist hUnit
  nlinarith only [h,hDict,hJoin,hHist,hUnit]

/-- The exact canonical source setup discharges the histogram cap, rather
than asking for a generic bound on its execution. -/
theorem canonical_source_time {p m F r : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (hp : 2<p) (hpos : 1≤(localRecords maps cap right).length) :
    (source (r:=r) maps cap I right).runtime≤
      8000*sourceWidth r (2*N m r) ((source (r:=r) maps cap I right).U) (p^r)*
        sourceVolume ((source (r:=r) maps cap I right).xs) r (p^r)
          (if right then I.nC else I.nB) (nb m r) (F^r) ((F*cap)^r) :=by
  apply source_time_shape
  · simp [source]
  · simp [source]
  · simpa [source] using hpos
  · intro i hi
    exact source_histogram_cap maps cap r right hp _


/-- The actual endpoint type is smaller than the output type on every good
block. This follows from the checked finite cardinality ledger. -/
theorem endpoint_le_output {K m : ℕ} (hK : 0<K) (hgood : GoodBlock K m) :
    endpointSize m≤outputSize m :=by
  have hm:=hgood.1
  have hMp : 0<(outputSize m:ℝ) :=by exact_mod_cast TernaryOversizePrime.outputSize_pos m
  have hEp : 0<(endpointSize m:ℝ) :=by
    have hh : 0<endpointSize m :=by rw [actual_endpoint_count]; exact typeCount_pos (by decide) m
    exact_mod_cast hh
  have hS : 0≤Real.log (inflation K m:ℝ) :=Real.log_nonneg (by exact_mod_cast inflation_pos hK m)
  have hc : TernaryOversizeRates.endpointCharge K m<2 :=by
    have hh:=hgood.2.2.2.1
    norm_num [softCertificate] at hh ⊢
    linarith
  rw [←TernaryOversizeDimensions.endpoint_charge_eq hm] at hc
  have hl:= (div_lt_iff₀ (TernaryPrincipalDimensions.output_log_pos hm)).mp hc
  unfold TernaryOversizeDimensions.tableSlope at hl
  have he : Real.log (endpointSize m:ℝ)≤Real.log (outputSize m:ℝ) :=by linarith
  exact_mod_cast (Real.log_le_log_iff hEp hMp).mp he

/-- The trimmed endpoint bucket cap is paid by the already charged p/Rbar
incidence volume; seventeen is a fixed local multiplicity. -/
theorem sourceCap_ratio {K m : ℕ} (hK : 0<K) (hgood : GoodBlock K m) :
    (TernaryCoverCapParameters.sourceCap m (nativePrime K m):ℝ)≤
      17*(nativePrime K m:ℝ)/(partitionCap m:ℝ) :=by
  let P:=nativePrime K m
  let V:=(TernaryCoverLocal.fieldVertices (fixedLength m) P (fixedAlpha m)).card
  have hpN : 0<P:=(nativePrime_prime K m).pos
  have hp : 0<(P:ℝ):=by exact_mod_cast hpN
  have hR : 0<(partitionCap m:ℝ) :=by unfold partitionCap; positivity
  have hRM : (partitionCap m:ℝ)≤P :=by exact_mod_cast TernaryOversizeDimensions.partition_le_native hK m
  have hV : V≤outputSize m :=by
    have hh : V≤endpointSize m:=Finset.card_image_le
    exact hh.trans (endpoint_le_output hK hgood)
  have hcap : TernaryCoverCapParameters.sourceCap m P*P≤8*(P+V)+P :=by
    unfold TernaryCoverCapParameters.sourceCap
    rw [Nat.ceilDiv_eq_add_pred_div]
    have hh:=Nat.div_mul_le_self (8*(P+V)+P-1) P
    change (8*(P+V)+P-1)/P*P≤_
    omega
  have hcapR : (TernaryCoverCapParameters.sourceCap m P:ℝ)*P≤9*(P:ℝ)+8*(outputSize m:ℝ) :=by
    have hc : (TernaryCoverCapParameters.sourceCap m P:ℝ)*P≤8*((P:ℝ)+V)+P :=by exact_mod_cast hcap
    have hv : (V:ℝ)≤outputSize m:=by exact_mod_cast hV
    linarith
  have hM : (outputSize m:ℝ)*(partitionCap m:ℝ)≤(P:ℝ)^2 :=by
    exact_mod_cast nativePrime_base_lower hK m
  have hprod:=mul_le_mul_of_nonneg_right hcapR hR.le
  have hpR:=mul_le_mul_of_nonneg_left hRM hp.le
  apply (le_div_iff₀ hR).mpr
  change (TernaryCoverCapParameters.sourceCap m P:ℝ)*(partitionCap m:ℝ)≤17*(P:ℝ)
  nlinarith only [hprod,hpR,hM,hp]

/-- Fixed source-word logarithms grow only linearly in prefix length. -/
theorem source_width_bound (p m r : ℕ) :
    sourceWidth r (2*N m r) (p*(p+1)^r) (p^r)≤
      (2*fixedLength m+3*p+6)*(r+1) :=by
  have hp : p≤2^p:=Nat.lt_two_pow_self.le
  have hps : p+1≤2^(p+1):=Nat.lt_two_pow_self.le
  have hu : p*(p+1)^r+1≤2^(p+(p+1)*r+1) :=by
    have hh:=Nat.mul_le_mul hp (Nat.pow_le_pow_left hps r)
    rw [←pow_mul,←pow_add] at hh
    have h1 : 1≤2^(p+(p+1)*r):=Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  have hm : p^r+1≤2^(p*r+1) :=by
    have hh:=Nat.pow_le_pow_left hp r
    rw [←pow_mul] at hh
    have h1 : 1≤2^(p*r):=Nat.one_le_pow _ _ (by decide)
    rw [pow_succ]
    omega
  have hlu:=Nat.log_mono_right (b:=2) hu
  have hlm:=Nat.log_mono_right (b:=2) hm
  rw [Nat.log_pow (by decide : 1<(2:ℕ))] at hlu hlm
  unfold sourceWidth N
  nlinarith only [hlu,hlm]

/-- Exact fourth-tensor execution is a polynomial in digit dimension times
one source/count call and the actual input/output lengths. -/
def tensorCoefficient (K J : ℕ) : ℕ :=
  powTableTime 5+(J+2)^4*(LightWeightRow.time 4 ((J+2)^4)+3000)+
    LightTernaryPairedPotential.time K (J+2)+6000

theorem tensor_time_shape (K J nL nR H hostTime : ℕ) :
    LightTernaryTensorDriver.time K J nL nR H hostTime≤
      tensorCoefficient K J*(nL+nR+H+hostTime+1) :=by
  let B:=nL+nR+H+hostTime+1
  have hB : 1≤B:=by dsimp [B]; omega
  have hnL : nL≤B:=by dsimp [B]; omega
  have hnR : nR≤B:=by dsimp [B]; omega
  have hH : H≤B:=by dsimp [B]; omega
  have ht : hostTime≤B:=by dsimp [B]; omega
  have hT : 1≤tensorCoefficient K J:=by unfold tensorCoefficient; omega
  have hsum : 40*nL+40*nR+60*H+hostTime+2266≤3000*B :=by dsimp [B]; omega
  have h1:=Nat.mul_le_mul_left ((J+2)^4) hsum
  have hp:=Nat.mul_le_mul_right (LightTernaryPairedPotential.time K (J+2)+100) hH
  have hu:=Nat.mul_le_mul_left
    (powTableTime 5+(J+2)^4*LightWeightRow.time 4 ((J+2)^4)+5000) hB
  unfold LightTernaryTensorDriver.time LightTernaryTaggedChannel.time
    LightTernaryProductChannel.time LightTernaryTensorScatter.time
    LightTernaryPairedPotentialBatch.time tensorCoefficient
  dsimp [B] at h1 hp hu
  nlinarith only [h1,hp,hu,hB]


def nativeFactor (K k b m : ℕ) : ℕ :=
  b*(nativeFamily K m k).length*
    TernaryCoverCapParameters.rawThreshold (nativePrime K m)
      (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k

def fullCharge (K m : ℕ) : ℝ :=
  max 1 (max (TernaryOversizeRates.bankCharge K m)
    (max (TernaryOversizeRates.queryCharge K m)
      (max (TernaryOversizeRates.endpointCharge K m)
        (max (TernaryOversizeRates.histogramCharge K m) (TernaryOversizeRates.incidenceCharge K m)))))

def fullExponent (K k c d m : ℕ) : ℝ :=fullCharge K m+overheadCharge k c d m

def volumeConstant (K k c d m : ℕ) : ℝ :=
  (baseFactor K k c d m:ℝ)*
    (Real.exp (TernaryOversizeDimensions.bankSlope K m)+
      Real.exp (TernaryOversizeDimensions.tableSlope K m (endpointSize m))+
      Real.exp (TernaryOversizeDimensions.tableSlope K m (nativePrime K m))+
      Real.exp (TernaryOversizeDimensions.querySlope K m)/TernaryParameters.z)

/-- The bundle pays source dictionaries, histogram domains, compact bank
cells, and all literal queries with the full prepared-query envelope. -/
def volumeBundle (K k b m n j : ℕ) : ℝ :=
  (nativeFactor K k b m:ℝ)^j*
    ((bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(nativePrime K m:ℝ)^j+
      (n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*
        TernaryCountFrontendBudget.envelope m j)

theorem volume_bundle_bound {K k b m n j : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (hn : 1<n)
    (hj : j≤radixLength m n) (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d) :
    volumeBundle K k b m n j≤volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m :=by
  let S:=(inflation K m:ℝ)^(4*j)
  let B:=(baseFactor K k c d m:ℝ)^j
  let E:=(n:ℝ)^fullCharge K m
  let CB:=Real.exp (TernaryOversizeDimensions.bankSlope K m)
  let CA:=Real.exp (TernaryOversizeDimensions.tableSlope K m (endpointSize m))
  let CP:=Real.exp (TernaryOversizeDimensions.tableSlope K m (nativePrime K m))
  let CQ:=Real.exp (TernaryOversizeDimensions.querySlope K m)/TernaryParameters.z
  have hnr : (1:ℝ)≤n:=by exact_mod_cast hn.le
  have hn0 : (0:ℝ)<n:=by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hcb : 0≤CB:=by dsimp [CB]; positivity
  have hca : 0≤CA:=by dsimp [CA]; positivity
  have hcp : 0≤CP:=by dsimp [CP]; positivity
  have hcq : 0≤CQ:=div_nonneg (Real.exp_pos _).le TernaryParameters.gibbs_parameters.2.2.1.le
  have hcharges : TernaryOversizeRates.bankCharge K m≤fullCharge K m ∧
      TernaryOversizeRates.queryCharge K m≤fullCharge K m ∧
      TernaryOversizeRates.endpointCharge K m≤fullCharge K m ∧
      TernaryOversizeRates.histogramCharge K m≤fullCharge K m :=by
    unfold fullCharge
    exact ⟨(le_max_left _ _).trans (le_max_right _ _),
      (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _)),
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))),
      (le_max_left _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))))⟩
  have hB0 : 0≤B:=by dsimp [B]; positivity
  have hfac : (nativeFactor K k b m:ℝ)^j≤S*B:=by
    dsimp [S,B,nativeFactor]
    exact_mod_cast repeated_native_family_factor_bound K k c d m b j hb
  have hbV:=TernaryOversizeDimensions.actual_bank_volume hK hm hn hj
  have haV:=TernaryOversizeDimensions.actual_endpoint_volume hK hm hn hj
  have hpV:=TernaryOversizeDimensions.actual_histogram_volume hK hm hn hj
  have hqV:=TernaryCountFrontendBudget.actual_query_envelope_volume hK hm hn hj
  have hb' : S*(bankSize m j:ℝ)≤CB*E :=hbV.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hnr hcharges.1) hcb)
  have ha' : S*(endpointSize m:ℝ)^j≤CA*E :=haV.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hnr hcharges.2.2.1) hca)
  have hp' : S*(nativePrime K m:ℝ)^j≤CP*E :=hpV.trans
    (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hnr hcharges.2.2.2) hcp)
  have hq' : S*((n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*
      TernaryCountFrontendBudget.envelope m j)≤CQ*E :=by
    have hh:=hqV.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hnr hcharges.2.1) hcq)
    simpa only [S,mul_assoc,mul_left_comm,mul_comm] using hh
  have hsum : S*((bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(nativePrime K m:ℝ)^j+
      (n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*TernaryCountFrontendBudget.envelope m j)
      ≤(CB+CA+CP+CQ)*E :=by nlinarith only [hb',ha',hp',hq']
  have hnon : 0≤(bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(nativePrime K m:ℝ)^j+
      (n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*TernaryCountFrontendBudget.envelope m j :=by
    have := TernaryCountFrontendBudget.envelope_pos m j
    positivity
  have hbase:=base_factor_prefix_bound hK hk hm hn hj c d
  change B≤(baseFactor K k c d m:ℝ)*(n:ℝ)^overheadCharge k c d m at hbase
  have hsum0 : 0≤(CB+CA+CP+CQ)*E:=by dsimp [E]; positivity
  calc
    volumeBundle K k b m n j≤B*(S*((bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(nativePrime K m:ℝ)^j+
      (n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*TernaryCountFrontendBudget.envelope m j)) :=by
      unfold volumeBundle
      simpa only [mul_assoc,mul_left_comm,mul_comm] using mul_le_mul_of_nonneg_right hfac hnon
    _≤B*((CB+CA+CP+CQ)*E):=mul_le_mul_of_nonneg_left hsum hB0
    _≤((baseFactor K k c d m:ℝ)*(n:ℝ)^overheadCharge k c d m)*((CB+CA+CP+CQ)*E):=
      mul_le_mul_of_nonneg_right hbase hsum0
    _=volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m :=by
      unfold volumeConstant fullExponent
      dsimp [CB,CA,CP,CQ,E]
      rw [Real.rpow_add hn0]
      ring

theorem full_exponent_lt {K m : ℕ} (hK : 100000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    fullExponent K (selectedMoment K) c d m<TernaryCountFrontendBudget.frontendExponent :=by
  have hmax : fullCharge K m<softCertificate:=by
    unfold fullCharge
    exact max_lt (by norm_num [softCertificate])
      (max_lt hgood.2.1 (max_lt hgood.2.2.1
        (max_lt hgood.2.2.2.1 (max_lt hgood.2.2.2.2.1 hgood.2.2.2.2.2))))
  have hkr : (100000000:ℝ)≤K:=by exact_mod_cast hK
  have hkp : (0:ℝ)<K:=by linarith
  have hmicro : microAllowance K<(1/10000:ℝ):=by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hbound : softCertificate+microAllowance K<TernaryCountFrontendBudget.frontendExponent :=by
    norm_num [softCertificate,TernaryCountFrontendBudget.frontendExponent]
    linarith
  exact (add_lt_add hmax hover).trans hbound


theorem actual_bank_size (m r : ℕ) : nb m r=bankSize m r :=by
  unfold nb bankCodes
  rw [TernaryBankEnumeration.codes_length_eq_bank_card]
  have hn : N m r=fixedLength (r*m):=by unfold N fixedLength; ring
  have ht : cut m r=bankCut m r:=by unfold cut bankCut LightTernaryPrefixSetup.T; ring
  rw [hn,ht]
  rfl

private theorem factor_ge {K k b m F : ℕ} (hb : 17≤b)
    (hF : F≤(nativeFamily K m k).length) : 17*F≤nativeFactor K k b m :=by
  have hτ : 1≤TernaryCoverCapParameters.rawThreshold (nativePrime K m)
      (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k :=
    TernaryCoverCapParameters.rawThreshold_pos _ _ _
  have h1:=Nat.mul_le_mul_left 17 hF
  have h2:=Nat.mul_le_mul_right (nativeFamily K m k).length hb
  have h3:=Nat.mul_le_mul_left (b*(nativeFamily K m k).length) hτ
  unfold nativeFactor
  nlinarith only [h1,h2,h3]

/-- All genuine canonical source dimensions fit the same four charged
volumes. In particular, source construction does not hide an N² join. -/
theorem canonical_source_volume {K k b m n j F : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input) (right : Bool)
    (hK : 0<K) (hgood : GoodBlock K m) (hn : 1<n) (hb : 17≤b) (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length)
    (hNL : (if right then I.nC else I.nB)≤n) :
    let cap:=TernaryCoverCapParameters.sourceCap m (nativePrime K m)
    let S:=source (r:=j) maps cap I right
    (sourceVolume S.xs j ((nativePrime K m)^j) S.NL (nb m j) (F^j) ((F*cap)^j):ℝ)≤
      (F*endpointSize m+3:ℕ)*volumeBundle K k b m n j :=by
  let P:=nativePrime K m
  let cap:=TernaryCoverCapParameters.sourceCap m P
  let S:=source (r:=j) maps cap I right
  let D:=(nativeFactor K k b m:ℝ)^j
  let X:=(n:ℝ)*((P:ℝ)/(partitionCap m:ℝ))^j*TernaryCountFrontendBudget.envelope m j
  let B:=volumeBundle K k b m n j
  have h17:=factor_ge hb hF
  have hFle : F≤nativeFactor K k b m:=by omega
  have hD1 : 1≤D:=by
    apply one_le_pow₀
    exact_mod_cast (show 1≤nativeFactor K k b m by omega)
  have hD0 : 0≤D:=by linarith
  have hr : 1≤(P:ℝ)/(partitionCap m:ℝ) :=
    (one_le_div (by unfold partitionCap; positivity)).mpr
      (by exact_mod_cast TernaryOversizeDimensions.partition_le_native hK m)
  have hE:=TernaryCountFrontendBudget.envelope_ge_one m j
  have hX : (n:ℝ)≤X:=by
    have hh:=mul_le_mul_of_nonneg_left (one_le_pow₀ hr (n:=j)) (show (0:ℝ)≤n by positivity)
    dsimp [X]
    nlinarith only [hh,hE,show (0:ℝ)≤n by positivity]
  have hX0 : 0≤X:=(Nat.cast_nonneg n).trans hX
  have hBexpand : B=D*((bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(P:ℝ)^j+X):=rfl
  have hB0 : 1≤B:=by
    have hn1 : (1:ℝ)≤n:=by exact_mod_cast hn.le
    have hpos : 0≤(bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(P:ℝ)^j:=by positivity
    rw [hBexpand]
    nlinarith only [hD1,hX,hn1,hpos]
  have hlen : S.xs.length≤F*endpointSize m:=by
    simpa [S,source,localRecords,endpointSize] using
      TernaryCanonicalDictionaries.records_length_le (α:=fixedAlpha m) right maps cap
  have hlenR : (S.xs.length:ℝ)≤F*endpointSize m:=by exact_mod_cast hlen
  have hDict : (LightTernarySourceHost.size S.xs j:ℝ)≤D*(endpointSize m:ℝ)^j:=by
    have hh:=Nat.pow_le_pow_left (hlen.trans (Nat.mul_le_mul_right _ hFle)) j
    simpa only [LightTernarySourceHost.size,Nat.cast_pow,Nat.cast_mul,mul_pow,D] using
      (show ((S.xs.length^j:ℕ):ℝ)≤((nativeFactor K k b m*endpointSize m)^j:ℕ) from by exact_mod_cast hh)
  have hPf : ((F^j:ℕ):ℝ)≤D:=by
    dsimp [D]
    exact_mod_cast Nat.pow_le_pow_left hFle j
  have hHist : ((F^j*nb m j:ℕ):ℝ)≤D*(bankSize m j:ℝ):=by
    rw [Nat.cast_mul,actual_bank_size]
    exact mul_le_mul_of_nonneg_right hPf (Nat.cast_nonneg _)
  have hP : (((P^j:ℕ):ℝ))≤D*(P:ℝ)^j:=by
    rw [Nat.cast_pow]
    exact le_mul_of_one_le_left (by positivity) hD1
  have hcap:=sourceCap_ratio hK hgood
  have hFc : (F*cap:ℝ)≤(nativeFactor K k b m:ℝ)*((P:ℝ)/(partitionCap m:ℝ)) :=by
    have hh:=mul_le_mul_of_nonneg_left hcap (show (0:ℝ)≤F by positivity)
    have h17R : (17*F:ℕ)≤nativeFactor K k b m:=h17
    have hd:=mul_le_mul_of_nonneg_right (show (17*(F:ℝ))≤nativeFactor K k b m by exact_mod_cast h17R)
      (show (0:ℝ)≤(P:ℝ)/(partitionCap m:ℝ) from hr.trans' (by norm_num))
    calc
      _≤(F:ℝ)*(17*(P:ℝ)/(partitionCap m:ℝ)):=hh
      _=(17*(F:ℝ))*((P:ℝ)/(partitionCap m:ℝ)):=by ring
      _≤_:=hd
  have hcpow:=pow_le_pow_left₀ (by positivity : (0:ℝ)≤(F*cap:ℝ)) hFc j
  simp only [mul_pow] at hcpow
  have hNL' : (S.NL:ℝ)≤n:=by exact_mod_cast hNL
  have hJoin : ((S.NL*(F*cap)^j:ℕ):ℝ)≤D*X:=by
    rw [Nat.cast_mul,Nat.cast_pow,Nat.cast_mul]
    have hh:=mul_le_mul hNL' hcpow (by positivity) (show (0:ℝ)≤n by positivity)
    have he:=mul_le_mul_of_nonneg_left hE (show (0:ℝ)≤(n:ℝ)*(D*((P:ℝ)/(partitionCap m:ℝ))^j) by positivity)
    simp only [D,X,mul_pow] at hh he ⊢
    nlinarith only [hh,he]
  have hN : (S.NL:ℝ)≤D*X:=by
    exact hNL'.trans (hX.trans (le_mul_of_one_le_left hX0 hD1))
  have hBparts : D*(bankSize m j:ℝ)+D*(endpointSize m:ℝ)^j+D*(P:ℝ)^j≤B:=by
    rw [hBexpand]
    nlinarith only [mul_nonneg hD0 hX0]
  have hx : D*X≤B:=by
    rw [hBexpand]
    have h0 : 0≤(bankSize m j:ℝ)+(endpointSize m:ℝ)^j+(P:ℝ)^j:=by positivity
    nlinarith only [mul_nonneg hD0 h0]
  have h0 : 0≤(F:ℝ)*(endpointSize m:ℝ):=by positivity
  change (sourceVolume S.xs j (P^j) S.NL (nb m j) (F^j) ((F*cap)^j):ℝ)≤((F*endpointSize m+3:ℕ):ℝ)*B
  unfold sourceVolume
  push_cast at hHist hP hJoin ⊢
  dsimp only [S,P,cap] at hDict hHist hP hJoin hN hlenR ⊢
  have hprod : 0≤((F:ℝ)*endpointSize m+1)*(B-1):=mul_nonneg (by positivity) (by linarith)
  dsimp only [P] at hBexpand
  nlinarith only [hDict,hHist,hP,hJoin,hN,hlenR,hBexpand,hx,hB0,hprod]

/-- Actual source execution under native dimensions, before the remaining
polylogarithmic tensor and menu loops are charged. -/
theorem canonical_source_prefix_bound {K k b m n j F : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input) (right : Bool)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hj : j≤radixLength m n) (hb17 : 17≤b) (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length) (hNL : (if right then I.nC else I.nB)≤n)
    (hpos : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) right).length)
    (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d) :
    ((source (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I right).runtime:ℝ)≤
      (8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3):ℕ)*
        volumeConstant K k c d m*(j+1:ℕ)*(n:ℝ)^fullExponent K k c d m :=by
  have ht:=canonical_source_time (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I right
    (by have:=nativePrime_gt_four hK hgood.1; omega) hpos
  have hv:=canonical_source_volume (j:=j) maps I right hK hgood hn hb17 hFpos hF hNL
  have hw:=source_width_bound (nativePrime K m) m j
  have htR : ((source (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I right).runtime:ℝ)≤
      8000*(sourceWidth j (2*N m j) (nativePrime K m*(nativePrime K m+1)^j) ((nativePrime K m)^j):ℝ)*
        (sourceVolume ((source (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I right).xs)
          j ((nativePrime K m)^j) (source (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I right).NL (nb m j) (F^j)
          ((F*TernaryCoverCapParameters.sourceCap m (nativePrime K m))^j):ℝ) :=by exact_mod_cast ht
  have hmul:=mul_le_mul (show (sourceWidth j (2*N m j) (nativePrime K m*(nativePrime K m+1)^j) ((nativePrime K m)^j):ℝ)≤
      ((2*fixedLength m+3*nativePrime K m+6)*(j+1):ℕ) by exact_mod_cast hw) hv (by positivity) (by positivity)
  have hbun:=volume_bundle_bound hK hk hgood.1 hn hj c d hb
  have hfactor : (0:ℝ)≤(8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3):ℕ)*(j+1:ℕ):=by positivity
  calc
    _≤(8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3):ℕ)*(j+1:ℕ)*volumeBundle K k b m n j :=by
      have hh:=mul_le_mul_of_nonneg_left hmul (by norm_num : (0:ℝ)≤8000)
      apply htR.trans
      convert hh using 1 <;> (try dsimp only [source]) <;> push_cast <;> ring
    _≤(8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3):ℕ)*(j+1:ℕ)*
      (volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m):=
      mul_le_mul_of_nonneg_left hbun hfactor
    _=_:=by ring


/-- Literal output rows are counted by the executed wanted DFS, including
all repeated map occurrence labels. -/
theorem wanted_entries_cap {p m F j : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (τ : ℕ) (I : Input) :
    (entries (r:=j) maps τ I).length≤I.requesterCount*(F*TernaryGoodOutputCatalog.cap m p τ)^j :=by
  unfold entries
  rw [TernaryWantedBatchIndex.entries_length_eq_count]
  apply TernaryWantedBatchCount.count_le _ _ _ _ _ _ _ _ _ I.positions
  intro x
  simpa using TernaryGoodOutputCatalog.localBucket_cap maps τ x

def localFactor (m : ℕ) : ℕ :=17+2*TernaryPartitionCount.partitionLoss (7930175*m) (978249*m)

theorem local_factor_polynomial (m : ℕ) : localFactor m≤19*(fixedLength m+1)^3 :=by
  have h1 : 2*(7930175*m)+1≤fixedLength m+1:=by unfold fixedLength; omega
  have h2 : 3*(978249*m)+1≤fixedLength m+1:=by unfold fixedLength; omega
  have h3 : 2*(978249*m)+1≤fixedLength m+1:=by unfold fixedLength; omega
  have hh:=Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have hpow : 1≤(fixedLength m+1)^3:=Nat.one_le_pow _ _ (by omega)
  unfold localFactor TernaryPartitionCount.partitionLoss
  nlinarith only [hh,hpow]

/-- The actual literal wanted count, with the complete physical requester
multiplicity (in particular 2^J) kept as an explicit factor. -/
theorem wanted_native_count {K k b m n j F carries : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (hK : 0<K) (hgood : GoodBlock K m)
    (hF : F≤(nativeFamily K m k).length) (hb : localFactor m≤b)
    (hrequest : I.requesterCount≤n*carries) :
    let τ:=TernaryCoverCapParameters.rawThreshold (nativePrime K m)
      (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k
    ((entries (r:=j) maps τ I).length:ℝ)≤
      (carries:ℝ)*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*(nativeFactor K k b m:ℝ)^j :=by
  let P:=nativePrime K m
  let τ:=TernaryCoverCapParameters.rawThreshold P (TernaryCoverCapParameters.sourceCap m P) k
  let loss:=TernaryPartitionCount.partitionLoss (7930175*m) (978249*m)
  have hτ : 0<τ:=TernaryCoverCapParameters.rawThreshold_pos _ _ _
  have hcap:=TernaryGoodOutputCatalog.cap_real_le_native (m:=m) (p:=P) τ hτ
    (nativePrime_base_lower hK m)
  have hbase : 2*loss*F*τ≤nativeFactor K k b m:=by
    have hb' : 2*loss≤b:=by dsimp [localFactor,loss] at hb ⊢; omega
    have hh:=Nat.mul_le_mul_right τ (Nat.mul_le_mul hb' hF)
    simpa only [nativeFactor,Nat.mul_assoc] using hh
  have hcap' : ((F*TernaryGoodOutputCatalog.cap m P τ:ℕ):ℝ)≤
      (nativeFactor K k b m:ℝ)*((P:ℝ)/(partitionCap m:ℝ)):=by
    have hh:=mul_le_mul_of_nonneg_left hcap (show (0:ℝ)≤F by positivity)
    have hd:=mul_le_mul_of_nonneg_right (show ((2*loss*F*τ:ℕ):ℝ)≤nativeFactor K k b m by exact_mod_cast hbase)
      (show (0:ℝ)≤(P:ℝ)/(partitionCap m:ℝ) by positivity)
    calc
      _≤(F:ℝ)*(2*(((loss*P*τ:ℕ):ℝ)/(partitionCap m:ℝ))):=by
        simpa [TernaryGoodOutputCatalog.Rbar,partitionCap,loss,Nat.cast_mul] using hh
      _=((2*loss*F*τ:ℕ):ℝ)*((P:ℝ)/(partitionCap m:ℝ)):=by push_cast; ring
      _≤_:=hd
  have hpow:=pow_le_pow_left₀ (by positivity : (0:ℝ)≤((F*TernaryGoodOutputCatalog.cap m P τ:ℕ):ℝ)) hcap' j
  have hcnt:=wanted_entries_cap (j:=j) maps τ I
  have hcntR : ((entries (r:=j) maps τ I).length:ℝ)≤
      (I.requesterCount:ℝ)*((F*TernaryGoodOutputCatalog.cap m P τ:ℕ):ℝ)^j:=by exact_mod_cast hcnt
  have hreqR : (I.requesterCount:ℝ)≤(n:ℝ)*(carries:ℝ):=by exact_mod_cast hrequest
  have hh:=mul_le_mul hreqR hpow (by positivity) (by positivity)
  dsimp [τ,P] at hcntR hh ⊢
  exact hcntR.trans (by simpa only [mul_pow,mul_assoc,mul_left_comm,mul_comm] using hh)


theorem frontend_time_mono (groups N L bank count s t : ℕ) (h : s≤t) :
    LightTernaryCountFrontend.time groups N L bank count s≤
      LightTernaryCountFrontend.time groups N L bank count t :=by
  unfold LightTernaryCountFrontend.time LightTernaryWantedRows.time LightTernaryWantedRowDispatch.time
  gcongr

/-- All complete carry rows are charged in the real frontend time function;
the extra factor is outside the native family exponent. -/
theorem frontend_bundle_shape {K k b m n j groups count carries : ℕ}
    (hK : 0<K) (hm : 0<m) (hn : 1<n) (hfactor : 1≤nativeFactor K k b m)
    (hcarries : 1≤carries) (f g : LightTernaryNearPair.Config)
    (hT : f.T=bankCut m j)
    (hgroups : groups≤nativeFactor K k b m^j)
    (hcount : (count:ℝ)≤(carries:ℝ)*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j*
      (nativeFactor K k b m:ℝ)^j) :
    ((LightTernaryCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count
      (TernaryCountFrontendBudget.queryMax m j f g)+1000:ℕ):ℝ)≤
      1000000*(TernaryCountFrontendBudget.width (fixedLength (j*m)) f g:ℝ)^3*
        (carries:ℝ)*volumeBundle K k b m n j :=by
  let D:=(nativeFactor K k b m:ℝ)^j
  let X:=(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^j
  have hD : 1≤D:=one_le_pow₀ (by exact_mod_cast hfactor)
  have hC : (1:ℝ)≤carries:=by exact_mod_cast hcarries
  have hr : 1≤(nativePrime K m:ℝ)/(partitionCap m:ℝ):=
    (one_le_div (by unfold partitionCap; positivity)).mpr
      (by exact_mod_cast TernaryOversizeDimensions.partition_le_native hK m)
  have hX : 1≤X:=by
    apply one_le_mul_of_one_le_of_one_le
    · exact_mod_cast hn.le
    · exact one_le_pow₀ hr
  have hCD : 1≤(carries:ℝ)*D:=one_le_mul_of_one_le_of_one_le hC hD
  have hg : (groups:ℝ)≤(carries:ℝ)*D:=by
    have hh : (groups:ℝ)≤D:=by dsimp [D]; exact_mod_cast hgroups
    exact hh.trans (le_mul_of_one_le_left (by linarith) hC)
  have hc : (count:ℝ)≤X*((carries:ℝ)*D):=by simpa only [X,D,mul_assoc,mul_left_comm,mul_comm] using hcount
  have ht:=TernaryCountFrontendBudget.frontend_shape_bound f g hT
    ((carries:ℝ)*D) X hCD hX hg hc
  have hvol : D*((bankSize m j:ℝ)+X*TernaryCountFrontendBudget.envelope m j)≤volumeBundle K k b m n j:=by
    unfold volumeBundle
    dsimp [D,X]
    have h0 : 0≤(nativeFactor K k b m:ℝ)^j*((endpointSize m:ℝ)^j+(nativePrime K m:ℝ)^j):=by positivity
    nlinarith only [h0]
  have hcoeff : 0≤1000000*(TernaryCountFrontendBudget.width (fixedLength (j*m)) f g:ℝ)^3*(carries:ℝ):=by positivity
  have hh:=mul_le_mul_of_nonneg_left hvol hcoeff
  exact ht.trans (by simpa only [mul_assoc,mul_left_comm,mul_comm] using hh)


theorem hash_time_mono (J p b B : ℕ) (h : b≤B) :
    LightSignedRowHash.time J p b≤LightSignedRowHash.time J p B :=by
  unfold LightSignedRowHash.time LightNaturalDot.reducedTime
  gcongr

def seedCoefficient (K J p B V prefixLen : ℕ) : ℕ :=
  60*J+200+(LightSignedRowHash.time (J+2) p B+120)+
    (LightTernaryWantedCanonical.overhead p V+LightTernaryWantedCanonical.stepCost V+40)*(prefixLen+1)+
    tensorCoefficient K J+10000

def seedVolume {C : LightTernarySeedScoreFactory.Config}
    (D : LightTernarySeedScoreFactory.Data C) {N : ℕ}
    (host : TernarySourceCountExecutionFactory.Setup N) (R S cap : ℕ)
    (raws : List ℤ) (words maps : List ℕ) : ℕ :=
  C.catalogRows+C.nB+C.nC+C.nO+C.nO*cap^C.prefixLength+C.power*C.p+
    D.H R S raws words maps+host.runtime+1

/-- Exact SeedScore runtime, with its four-way source/count loop and paired
potential work included. Only fixed-degree raw-coordinate magnitudes occur
in its coefficient. -/
theorem seed_runtime_shape {C : LightTernarySeedScoreFactory.Config}
    (D : LightTernarySeedScoreFactory.Data C) {N : ℕ}
    (host : TernarySourceCountExecutionFactory.Setup N) (K R S cap V B : ℕ)
    (raws : List ℤ) (words maps : List ℕ)
    (hB : D.bB≤B) (hC : D.bC≤B) (hO : D.bO≤B) :
    LightTernarySeedScoreFactory.runtime D host K R S cap V raws words maps≤
      seedCoefficient K C.J C.p B V C.prefixLength*seedVolume D host R S cap raws words maps :=by
  let H:=D.H R S raws words maps
  let W:=seedVolume D host R S cap raws words maps
  let A:=LightSignedRowHash.time (C.J+2) C.p B+120
  let T:=(LightTernaryWantedCanonical.overhead C.p V+LightTernaryWantedCanonical.stepCost V+40)*(C.prefixLength+1)
  have hW : 1≤W:=by dsimp [W,seedVolume]; omega
  have hInputs : C.nB+C.nC+C.nO≤W:=by dsimp [W,seedVolume]; omega
  have hSpan : C.catalogRows≤W:=by dsimp [W,seedVolume]; omega
  have hP : C.power*C.p≤W:=by dsimp [W,seedVolume]; omega
  have hWanted : C.nO*cap^C.prefixLength≤W:=by dsimp [W,seedVolume]; omega
  have hH : H≤W:=by dsimp [H,W,seedVolume]; omega
  have hHost : host.runtime≤W:=by dsimp [W,seedVolume]; omega
  have hl:=hash_time_mono (C.J+2) C.p D.bB B hB
  have hr:=hash_time_mono (C.J+2) C.p D.bC B hC
  have ho:=hash_time_mono (C.J+2) C.p D.bO B hO
  have hApp : LightTernaryAppendKeys.time C.nB (C.J+2) C.p D.bB+
      LightTernaryAppendKeys.time C.nC (C.J+2) C.p D.bC+
      LightTernaryAppendKeys.time C.nO (C.J+2) C.p D.bO≤A*W+90 :=by
    have h1:=Nat.mul_le_mul_left C.nB (Nat.add_le_add_right hl 120)
    have h2:=Nat.mul_le_mul_left C.nC (Nat.add_le_add_right hr 120)
    have h3:=Nat.mul_le_mul_left C.nO (Nat.add_le_add_right ho 120)
    have hh:=Nat.mul_le_mul_left A hInputs
    unfold LightTernaryAppendKeys.time
    dsimp [A] at hh ⊢
    nlinarith only [h1,h2,h3,hh]
  have hTensor:=tensor_time_shape K C.J C.nB C.nC H host.runtime
  have hTensor' : LightTernaryTensorDriver.time K C.J C.nB C.nC H host.runtime≤tensorCoefficient K C.J*W:=by
    apply hTensor.trans
    apply Nat.mul_le_mul_left
    dsimp [W,seedVolume,H]
    omega
  have hWant : LightTernaryWantedBatch.time C.p cap V C.prefixLength C.nO≤T*W+100*W+50:=by
    have h1:=Nat.mul_le_mul_left T hWanted
    have h2:=Nat.mul_le_mul_left 100 (show C.nO≤W by dsimp [W,seedVolume]; omega)
    unfold LightTernaryWantedBatch.time
    dsimp [T] at h1 ⊢
    nlinarith only [h1,h2]
  have hTest : LightSpanCatalogTest.time C.J C.catalogRows≤(60*C.J+200)*W+100:=by
    have hh:=Nat.mul_le_mul_left (60*C.J+200) hSpan
    unfold LightSpanCatalogTest.time LightSpanRowEqual.time
    nlinarith only [hh]
  have hDivide : LightSmallDivide.time (3*H) 3≤20*W+40:=by
    unfold LightSmallDivide.time
    rw [Nat.mul_div_right _ (by decide : 0<3)]
    omega
  have hCollision : LightOriginalCollisionScore.time C.nB (C.power*C.p)+
      LightOriginalCollisionScore.time C.nC (C.power*C.p)≤100*W+434:=by
    rw [LightOriginalCollisionScore.time_eq,LightOriginalCollisionScore.time_eq]
    have hh : C.nB+C.nC+C.power*C.p≤W:=by dsimp [W,seedVolume]; omega
    omega
  have hConst:=Nat.mul_le_mul_left 10000 hW
  unfold LightTernarySeedScoreFactory.runtime LightTernarySeedScore.time seedCoefficient
  dsimp [A,T,W,H] at hApp hTensor' hWant hTest hDivide hCollision hConst ⊢
  nlinarith only [hApp,hTensor',hWant,hTest,hDivide,hCollision,hConst]

/-- Every actual seed evaluation, the selected-seed reconstruction and the
physical span update are paid by the controller time function. -/
theorem all_seed_time_shape (q seedTime spanTime : ℕ) :
    LightTernarySeedController.time (q*q) seedTime spanTime≤
      (q*q+1)*(seedTime+spanTime+2000) :=
  LightTernarySeedControllerBudget.time_bound _ _ _


/-- Canonical CountFrontend runtime uses the actual proof-only typed query
maximum from CountReady. The wanted count is derived from literal entries. -/
theorem canonical_frontend_shape {K k b m n j F carries : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (Q : TernaryGoodOutputCatalog.Output m)
    (hK : 0<K) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : localFactor m≤b) (hcarries : 1≤carries)
    (hrequest : I.requesterCount≤n*carries)
    (htime : I.queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nearConfig (m:=m) (r:=j) I false
        (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I))
      (nearConfig (m:=m) (r:=j) I true
        (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I))) :
    let τ:=TernaryCoverCapParameters.rawThreshold (nativePrime K m)
      (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k
    let S:=front (r:=j) maps τ (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) Q I
    ((S.runtime+1000:ℕ):ℝ)≤
      1000000*(TernaryCountFrontendBudget.width (N m j) S.f S.g:ℝ)^3*
        (carries:ℝ)*volumeBundle K k b m n j :=by
  let τ:=TernaryCoverCapParameters.rawThreshold (nativePrime K m)
    (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k
  let S:=front (r:=j) maps τ (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) Q I
  have h17 : 17≤b:=by dsimp [localFactor] at hb; omega
  have hf:=factor_ge h17 hF
  have hFle : F≤nativeFactor K k b m:=by omega
  have hfac : 1≤nativeFactor K k b m:=by omega
  have hN : N m j=fixedLength (j*m):=by unfold N fixedLength; ring
  have hT : S.f.T=bankCut m j:=by
    change cut m j=bankCut m j
    unfold cut LightTernaryPrefixSetup.T bankCut
    ring
  have ht:=frontend_bundle_shape hK hgood.1 hn hfac hcarries S.f S.g hT
    (Nat.pow_le_pow_left hFle j) (wanted_native_count (j:=j) maps I hK hgood hF hb hrequest)
  have hmono:=frontend_time_mono (F^j) (fixedLength (j*m)) S.f.L (bankSize m j)
    S.count I.queryTime (TernaryCountFrontendBudget.queryMax m j S.f S.g) htime
  have hRuntime : S.runtime=LightTernaryCountFrontend.time (F^j) (fixedLength (j*m))
      S.f.L (bankSize m j) S.count I.queryTime:=by
    change LightTernaryCountFrontend.time (F^j) (N m j) S.f.L (nb m j) S.count I.queryTime=_
    exact congrArg₂ (fun a bank=>LightTernaryCountFrontend.time (F^j) a S.f.L bank S.count I.queryTime) hN (actual_bank_size m j)
  have hwidth:=congrArg (fun a=>TernaryCountFrontendBudget.width a S.f S.g) hN
  change ((S.runtime+1000:ℕ):ℝ)≤1000000*(TernaryCountFrontendBudget.width (N m j) S.f S.g:ℝ)^3*(carries:ℝ)*volumeBundle K k b m n j
  rw [hRuntime,hwidth]
  refine le_trans ?_ ht
  exact_mod_cast Nat.add_le_add_right hmono 1000

/-- Both actual source hosts and the actual count frontend are assembled
before the seed and moment drivers apply their fixed-dimensional loops. -/
theorem canonical_host_prefix_bound {K k b m n j F carries : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (Q : TernaryGoodOutputCatalog.Output m)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hj : j≤radixLength m n) (hFpos : 0<F)
    (hF : F≤(nativeFamily K m k).length) (hb : localFactor m≤b)
    (hcarries : 1≤carries) (hrequest : I.requesterCount≤n*carries)
    (hB : I.nB≤n) (hC : I.nC≤n)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (htime : I.queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nearConfig (m:=m) (r:=j) I false
        (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I))
      (nearConfig (m:=m) (r:=j) I true
        (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) I)))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    let τ:=TernaryCoverCapParameters.rawThreshold (nativePrime K m)
      (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k
    let S:=setup (r:=j) maps τ (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) Q I
    (S.runtime:ℝ)≤
      (2*(8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3):ℕ)*(j+1:ℕ)+
        1000000*(TernaryCountFrontendBudget.width (N m j) S.front.f S.front.g:ℝ)^3*(carries:ℝ))*
        volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m :=by
  let τ:=TernaryCoverCapParameters.rawThreshold (nativePrime K m)
    (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k
  let S:=setup (r:=j) maps τ (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) Q I
  have h17 : 17≤b:=by dsimp [localFactor] at hb; omega
  have hl:=canonical_source_prefix_bound (j:=j) maps I false hK hk hgood hn hj h17 hFpos hF hB hposL c d hpoly
  have hr:=canonical_source_prefix_bound (j:=j) maps I true hK hk hgood hn hj h17 hFpos hF hC hposR c d hpoly
  have hf:=canonical_frontend_shape (j:=j) maps I Q hK hgood hn hFpos hF hb hcarries hrequest htime
  have hv:=volume_bundle_bound hK hk hgood.1 hn hj c d hpoly
  have hcoeff : 0≤1000000*(TernaryCountFrontendBudget.width (N m j) S.front.f S.front.g:ℝ)^3*(carries:ℝ):=by positivity
  have hf': ((S.front.runtime+1000:ℕ):ℝ)≤
      (1000000*(TernaryCountFrontendBudget.width (N m j) S.front.f S.front.g:ℝ)^3*(carries:ℝ))*
        (volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m):=by
    exact hf.trans (mul_le_mul_of_nonneg_left hv hcoeff)
  have hrun : S.runtime≤S.left.runtime+S.right.runtime+(S.front.runtime+1000):=by
    unfold TernarySourceCountExecutionFactory.Setup.runtime LightTernarySourceCountHost.time
    omega
  have hrunR : (S.runtime:ℝ)≤(S.left.runtime:ℝ)+(S.right.runtime:ℝ)+((S.front.runtime+1000:ℕ):ℝ):=by exact_mod_cast hrun
  change (S.runtime:ℝ)≤_
  change (S.left.runtime:ℝ)≤_ at hl
  change (S.right.runtime:ℝ)≤_ at hr
  nlinarith only [hl,hr,hf',hrunR]


def potentialCoefficient (K : ℕ) : ℕ :=
  powTableTime (TernaryPairedColumnEnumeration.width K+1)+
    280*TernaryPairedColumnEnumeration.width K+LightTernaryPairedPolynomial.time K+700

theorem potential_time_polynomial (K Λ : ℕ) (hΛ : 1≤Λ) :
    LightTernaryPairedPotential.time K Λ≤
      potentialCoefficient K*Λ^(2*TernaryPairedColumnEnumeration.width K) :=by
  let w:=TernaryPairedColumnEnumeration.width K
  have hpow : Λ^w≤Λ^(2*w):=Nat.pow_le_pow_right hΛ (by omega)
  have h1 : 1≤Λ^(2*w):=Nat.one_le_pow _ _ hΛ
  have hlinear:=Nat.mul_le_mul_left (240*w+LightTernaryPairedPolynomial.time K+306) hpow
  have hconst:=Nat.mul_le_mul_left (powTableTime (w+1)+300) h1
  unfold LightTernaryPairedPotential.time LightWeightRow.time LightRadixDigit.time potentialCoefficient
  change _≤(powTableTime (w+1)+280*w+LightTernaryPairedPolynomial.time K+700)*Λ^(2*w)
  rw [show Λ^(2*w)=(Λ^w)^2 by rw [Nat.mul_comm 2 w,pow_mul]] at hlinear hconst ⊢
  nlinarith only [hlinear,hconst]

/-- The degree depends on the fixed moment order K, while the digit-length
argument remains a variable. The actual unary digit kernels are included. -/
theorem tensor_coefficient_polynomial (K : ℕ) :
    ∃ A d : ℕ, ∀J, tensorCoefficient K J≤A*(J+1)^d :=by
  let d:=max 8 (2*TernaryPairedColumnEnumeration.width K)
  let C:=powTableTime 5+160+3966+potentialCoefficient K+6000
  refine ⟨C*2^d,d,fun J=>?_⟩
  let Λ:=J+2
  have hΛ : 1≤Λ:=by dsimp [Λ]; omega
  have h8 : Λ^8≤Λ^d:=Nat.pow_le_pow_right hΛ (le_max_left _ _)
  have h4 : Λ^4≤Λ^d:=Nat.pow_le_pow_right hΛ (by dsimp [d]; omega)
  have hw : Λ^(2*TernaryPairedColumnEnumeration.width K)≤Λ^d:=
    Nat.pow_le_pow_right hΛ (le_max_right _ _)
  have h1 : 1≤Λ^d:=Nat.one_le_pow _ _ hΛ
  have hpot:=(potential_time_polynomial K Λ hΛ).trans (Nat.mul_le_mul_left _ hw)
  have hconst:=Nat.mul_le_mul_left (powTableTime 5+6000) h1
  have hpoly : tensorCoefficient K J≤C*Λ^d:=by
    have he : Λ^4*Λ^4=Λ^8:=by rw [←pow_add]
    have h8':=Nat.mul_le_mul_left 160 h8
    have h4':=Nat.mul_le_mul_left 3966 h4
    unfold tensorCoefficient LightWeightRow.time LightRadixDigit.time
    dsimp [C,Λ] at hpot hconst h8' h4' he ⊢
    nlinarith only [hpot,hconst,h8',h4',he]
  have hJ : Λ≤2*(J+1):=by dsimp [Λ]; omega
  have hh:=Nat.mul_le_mul_left C (Nat.pow_le_pow_left hJ d)
  rw [mul_pow] at hh
  exact hpoly.trans (by simpa only [Nat.mul_assoc] using hh)


def capacityBits (M D E κ : ℕ) : ℕ :=D+2*E+M*(κ+1)*E+1

/-- Only the logarithm of the polynomial word envelope enters near-query
cost. No polynomial-size arena scan is inserted into the runtime bound. -/
theorem capacity_power_bound {M n U κ D E : ℕ} (hM : 1<M) (hn : 1<n)
    (hU : U≤n^κ) :
    D*(n+U+1)^E+1≤2^(capacityBits M D E κ*(Nat.clog M (n^2)+1)) :=by
  let R:=Nat.clog M (n^2)
  have hnM : n≤M^R:=by
    have hh:=Nat.le_pow_clog hM (n^2)
    have hn2 : n≤n^2:=by nlinarith
    exact hn2.trans hh
  have hbM : 1≤M^R:=Nat.one_le_pow _ _ (by omega)
  have hPow : M^R≤(M^R)^(κ+1):=Nat.le_self_pow (by omega) _
  have hUPow : U≤(M^R)^(κ+1):=hU.trans ((Nat.pow_le_pow_left hnM κ).trans
    (Nat.pow_le_pow_right hbM (by omega)))
  have hN : n+U+1≤3*(M^R)^(κ+1):=by
    have h1 : 1≤(M^R)^(κ+1):=Nat.one_le_pow _ _ hbM
    omega
  have hM2 : M≤2^M:=Nat.lt_two_pow_self.le
  have hBase : 3*(M^R)^(κ+1)≤2^(2+M*R*(κ+1)):=by
    have hh:=Nat.mul_le_mul_left 3 (Nat.pow_le_pow_left hM2 (R*(κ+1)))
    calc
      _=3*M^(R*(κ+1)):=by rw [pow_mul]
      _≤3*(2^M)^(R*(κ+1)):=hh
      _=3*2^(M*(R*(κ+1))):=by rw [←pow_mul]
      _≤4*2^(M*(R*(κ+1))):=Nat.mul_le_mul_right _ (by decide : 3≤4)
      _=_:=by rw [pow_add]; norm_num; simp only [Nat.mul_assoc]
  have hD2 : D≤2^D:=Nat.lt_two_pow_self.le
  have hCap : D*(n+U+1)^E≤2^(D+(2+M*R*(κ+1))*E):=by
    have hh:=Nat.mul_le_mul hD2 (Nat.pow_le_pow_left (hN.trans hBase) E)
    simpa only [←pow_mul,←pow_add] using hh
  have h1 : 1≤2^(D+(2+M*R*(κ+1))*E):=Nat.one_le_pow _ _ (by decide)
  have hPlus : D*(n+U+1)^E+1≤2^(D+(2+M*R*(κ+1))*E+1):=by rw [pow_succ]; omega
  apply hPlus.trans
  apply Nat.pow_le_pow_right (by decide : 1≤(2:ℕ))
  dsimp [capacityBits,R]
  ring_nf
  omega

theorem log_from_capacity {M n U κ D E V : ℕ} (hM : 1<M) (hn : 1<n)
    (hU : U≤n^κ) (hV : V≤D*(n+U+1)^E) :
    Nat.log 2 (V+1)≤capacityBits M D E κ*(Nat.clog M (n^2)+1) :=by
  have hh:=Nat.log_mono_right (b:=2) ((Nat.add_le_add_right hV 1).trans (capacity_power_bound hM hn hU))
  simpa only [Nat.log_pow (by decide : 1<(2:ℕ))] using hh

/-- Tight query width for the actual canonical configs, obtained from the
same fixed polynomial word envelope already needed by the executable. -/
theorem canonical_width_bound {p m F n j U κ D E : ℕ} [Fact p.Prime]
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input)
    (hm : 0<m) (hn : 1<n) (hj : j≤radixLength m n) (hU : U≤n^κ)
    (hV : TernaryFrontendResources.eulerBound (N m j) (valueCap (r:=j) maps cap I)≤D*(n+U+1)^E) :
    TernaryCountFrontendBudget.width (N m j)
      (nearConfig (m:=m) (r:=j) I false (valueCap (r:=j) maps cap I))
      (nearConfig (m:=m) (r:=j) I true (valueCap (r:=j) maps cap I))≤
      (5*fixedLength m+2*capacityBits (outputSize m) D E κ+3)*(radixLength m n+1) :=by
  have hM : 1<outputSize m:=by have:=outputSize_ge_sixteen hm; omega
  have hh:=log_from_capacity hM hn hU hV
  have hN : N m j=fixedLength (j*m):=by unfold N fixedLength; ring
  let f:=nearConfig (m:=m) (r:=j) I false (valueCap (r:=j) maps cap I)
  let g:=nearConfig (m:=m) (r:=j) I true (valueCap (r:=j) maps cap I)
  have hf : f.L≤2*fixedLength (j*m):=by change 2*N m j≤_; rw [hN]
  have hg : g.L≤2*fixedLength (j*m):=by change 2*N m j≤_; rw [hN]
  have hlogs : Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)≤
      (2*capacityBits (outputSize m) D E κ)*(radixLength m n+1):=by
    change Nat.log 2 (TernaryFrontendResources.eulerBound (N m j) (valueCap (r:=j) maps cap I)+1)+
      Nat.log 2 (TernaryFrontendResources.eulerBound (N m j) (valueCap (r:=j) maps cap I)+1)≤_
    dsimp [radixLength] at ⊢
    nlinarith only [hh]
  rw [hN]
  exact TernaryCountFrontendBudget.width_bound_from_logs hj f g hf hg hlogs


def nativeHost {K k m F : ℕ} (j : ℕ) (maps : Fin F→Weight m (nativePrime K m))
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) :=
  setup (r:=j) maps (TernaryCoverCapParameters.rawThreshold (nativePrime K m)
    (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) k)
    (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) Q I

def allHostTime {K k m F : ℕ} (maps : Fin F→Weight m (nativePrime K m))
    (Q : TernaryGoodOutputCatalog.Output m) (I : ℕ→Input) (n : ℕ) : ℕ :=
  ∑j∈Finset.range (radixLength m n+1), (nativeHost (K:=K) (k:=k) j maps Q (I j)).runtime

def sourceCoefficient (K m F : ℕ) : ℕ :=
  8000*(2*fixedLength m+3*nativePrime K m+6)*(F*endpointSize m+3)
def widthCoefficient (m D E κ : ℕ) : ℕ :=5*fixedLength m+2*capacityBits (outputSize m) D E κ+3

def hostConstant (K k c d m F D E κ : ℕ) : ℝ :=
  ((2*sourceCoefficient K m F+1000000*(widthCoefficient m D E κ)^3:ℕ):ℝ)*volumeConstant K k c d m

theorem hostConstant_nonneg (K k c d m F D E κ : ℕ) : 0≤hostConstant K k c d m F D E κ:=by
  unfold hostConstant
  apply mul_nonneg (Nat.cast_nonneg _)
  unfold volumeConstant
  refine mul_nonneg (Nat.cast_nonneg _) ?_
  exact add_nonneg (add_nonneg (add_nonneg (Real.exp_pos _).le (Real.exp_pos _).le) (Real.exp_pos _).le)
    (div_nonneg (Real.exp_pos _).le TernaryParameters.gibbs_parameters.2.2.1.le)

/-- Sum of the concrete source/count runtimes at every prefix. All bounds
are on original lengths, actual word magnitudes, and the literal typed
query maximum. The physical carry count is an explicit multiplier. -/
theorem all_host_prefix_bound {K k b m n U κ F carries D E : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : ℕ→Input) (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m)
    (hn : 1<n) (hU : U≤n^κ) (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : localFactor m≤b) (hcarries : 1≤carries)
    (hB : ∀j≤radixLength m n, (I j).nB≤n) (hC : ∀j≤radixLength m n, (I j).nC≤n)
    (hrequest : ∀j≤radixLength m n, (I j).requesterCount≤n*carries)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀j≤radixLength m n,
      TernaryFrontendResources.eulerBound (N m j)
        (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) (I j))≤D*(n+U+1)^E)
    (htime : ∀j≤radixLength m n, (I j).queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    (allHostTime (K:=K) (k:=k) maps Q I n:ℝ)≤
      hostConstant K k c d m F D E κ*(radixLength m n+1:ℕ)^4*(carries:ℝ)*
        (n:ℝ)^fullExponent K k c d m :=by
  let R:=radixLength m n
  let A:=2*sourceCoefficient K m F+1000000*(widthCoefficient m D E κ)^3
  have hvol : 0≤volumeConstant K k c d m:=by
    have hz:=TernaryParameters.gibbs_parameters.2.2.1
    unfold volumeConstant
    positivity
  have hper : ∀j∈Finset.range (R+1),
      ((nativeHost (K:=K) (k:=k) j maps Q (I j)).runtime:ℝ)≤
        (A:ℝ)*(R+1:ℕ)^3*(carries:ℝ)*volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m :=by
    intro j hj
    have hj' : j≤radixLength m n:=by have:=Finset.mem_range.mp hj; dsimp [R] at this; omega
    let S:=nativeHost (K:=K) (k:=k) j maps Q (I j)
    let W:=TernaryCountFrontendBudget.width (N m j) S.front.f S.front.g
    have ht:=canonical_host_prefix_bound (j:=j) maps (I j) Q hK hk hgood hn hj' hFpos hF hb hcarries
      (hrequest j hj') (hB j hj') (hC j hj') hposL hposR (htime j hj') c d hpoly
    have hw : W≤widthCoefficient m D E κ*(R+1):=
      canonical_width_bound maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m))
        (I j) hgood.1 hn hj' hU (hword j hj')
    have hJ : j+1≤(R+1)^3:=by
      have hh : j+1≤R+1:=by dsimp [R]; omega
      exact hh.trans (Nat.le_self_pow (by decide : 3≠0) _)
    have h1:=Nat.mul_le_mul_left (2*sourceCoefficient K m F) hJ
    have h1': 2*sourceCoefficient K m F*(j+1)≤2*sourceCoefficient K m F*(R+1)^3*carries:=
      h1.trans (Nat.le_mul_of_pos_right _ hcarries)
    have h2:=Nat.mul_le_mul_right carries (Nat.mul_le_mul_left 1000000 (Nat.pow_le_pow_left hw 3))
    have hcoeff : 2*sourceCoefficient K m F*(j+1)+1000000*W^3*carries≤A*(R+1)^3*carries:=by
      rw [mul_pow] at h2
      dsimp [A]
      nlinarith only [h1',h2]
    have hcoeffR : (2:ℝ)*(sourceCoefficient K m F:ℝ)*(j+1:ℕ)+1000000*(W:ℝ)^3*(carries:ℝ)≤
      (A:ℝ)*(R+1:ℕ)^3*(carries:ℝ):=by exact_mod_cast hcoeff
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeffR hvol) (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
    exact ht.trans hh
  unfold allHostTime
  rw [Nat.cast_sum]
  have hh:=Finset.sum_le_sum hper
  have he : (∑_j∈Finset.range (R+1),
      (A:ℝ)*(R+1:ℕ)^3*(carries:ℝ)*volumeConstant K k c d m*(n:ℝ)^fullExponent K k c d m)=
      hostConstant K k c d m F D E κ*(radixLength m n+1:ℕ)^4*(carries:ℝ)*
        (n:ℝ)^fullExponent K k c d m:=by
    simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
    unfold hostConstant
    dsimp [A,R]
    push_cast
    ring
  exact hh.trans_eq he


/-- Complete all-prefix source/count cost, including the physical 2^J carry
factor, is below the requested exponent whenever the common fixed block
and radix leave the stated positive margin. No running-time premise occurs. -/
theorem all_host_eventually {K k b m κ F D E β : ℕ} {δ ε : ℝ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : ℕ→ℕ→Input) (U : ℕ→ℕ)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hβ : 1<β)
    (hU : ∀n, 1<n → U n≤n^κ) (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : localFactor m≤b)
    (hB : ∀n, 1<n → ∀j≤radixLength m n, (I n j).nB≤n)
    (hC : ∀n, 1<n → ∀j≤radixLength m n, (I n j).nC≤n)
    (hrequest : ∀n, 1<n → ∀j≤radixLength m n,
      (I n j).requesterCount≤n*2^TernarySignedPadding.paddedLength β (U n) (radixLength m n))
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hword : ∀n, 1<n → ∀j≤radixLength m n,
      TernaryFrontendResources.eulerBound (N m j)
        (valueCap (r:=j) maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) (I n j))≤D*(n+U n+1)^E)
    (htime : ∀n, 1<n → ∀j≤radixLength m n, (I n j).queryTime≤TernaryCountFrontendBudget.queryMax m j
      (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.f (nativeHost (K:=K) (k:=k) j maps Q (I n j)).front.g)
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcarry : TernarySignedPadding.carryExponent m β (κ:ℝ)<δ) (hε : 0<ε)
    (hgap : fullExponent K k c d m+δ+ε<TernaryParameters.targetExponent) :
    ∀ᶠ n : ℕ in atTop,
      (allHostTime (K:=K) (k:=k) maps Q (I n) n:ℝ)≤(n:ℝ)^TernaryParameters.targetExponent :=by
  let A:=hostConstant K k c d m F D E κ
  have hA : 0≤A:=hostConstant_nonneg _ _ _ _ _ _ _ _ _
  have hκ : (0:ℝ)≤κ:=Nat.cast_nonneg _
  have hUR : ∀n, 1<n → (U n:ℝ)≤(n:ℝ)^(κ:ℝ):=by
    intro n hn
    simpa only [Real.rpow_natCast,Nat.cast_pow] using (show (U n:ℝ)≤(n^κ:ℕ) by exact_mod_cast hU n hn)
  have hc:=TernarySignedPadding.padded_carry_eventually hgood.1 hβ hκ hcarry U hUR
  have hp:=TernarySignedPreparationBudget.polynomial_digit_budget hgood.1 hβ hκ hε A hA 4 U hUR
  filter_upwards [hc,hp,eventually_gt_atTop (1:ℕ)] with n hcarryN hpolyN hn
  let J:=TernarySignedPadding.paddedLength β (U n) (radixLength m n)
  have hJ : radixLength m n+1≤J+1:=by
    dsimp [J,TernarySignedPadding.paddedLength]
    omega
  have hbinary : 1≤((Nat.log 2 (3*U n+1):ℝ)+2)^4:=one_le_pow₀ (by
    have hh : (0:ℝ)≤Nat.log 2 (3*U n+1):=Nat.cast_nonneg _
    linarith)
  have hdrop : A*(J+1:ℕ)^4≤(n:ℝ)^ε:=by
    have hh:=le_mul_of_one_le_right (show (0:ℝ)≤A*(J+1:ℕ)^4 by positivity) hbinary
    exact hh.trans (by simpa [J] using hpolyN)
  have htimeN:=all_host_prefix_bound (n:=n) (U:=U n) (κ:=κ)
    (carries:=2^J) (D:=D) (E:=E) maps Q (I n) hK hk hgood hn (hU n hn) hFpos hF hb
    (Nat.one_le_pow _ _ (by decide)) (hB n hn) (hC n hn) (hrequest n hn)
    hposL hposR (hword n hn) (htime n hn) c d hpoly
  have hRpow : ((radixLength m n+1:ℕ):ℝ)^4≤((J+1:ℕ):ℝ)^4:=by exact_mod_cast Nat.pow_le_pow_left hJ 4
  have hfinite : (allHostTime (K:=K) (k:=k) maps Q (I n) n:ℝ)≤
      A*(J+1:ℕ)^4*(2:ℝ)^J*(n:ℝ)^fullExponent K k c d m:=by
    have hh:=mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hRpow hA)
        (show (0:ℝ)≤(2:ℝ)^J by positivity)) (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
    have hh0 : (allHostTime (K:=K) (k:=k) maps Q (I n) n:ℝ)≤
        A*(radixLength m n+1:ℕ)^4*(2:ℝ)^J*(n:ℝ)^fullExponent K k c d m:=by
      simpa only [A,Nat.cast_pow,Nat.cast_ofNat] using htimeN
    exact hh0.trans hh
  have hCarry : (2:ℝ)^J≤(n:ℝ)^δ:=by simpa only [J] using hcarryN
  have hsmall:=mul_le_mul hdrop hCarry (by positivity) (show (0:ℝ)≤(n:ℝ)^ε by positivity)
  have hsmall':=mul_le_mul_of_nonneg_right hsmall (show (0:ℝ)≤(n:ℝ)^fullExponent K k c d m by positivity)
  have hnR : (0:ℝ)<n:=by exact_mod_cast lt_trans Nat.zero_lt_one hn
  calc
    _≤A*(J+1:ℕ)^4*(2:ℝ)^J*(n:ℝ)^fullExponent K k c d m:=hfinite
    _≤(n:ℝ)^ε*(n:ℝ)^δ*(n:ℝ)^fullExponent K k c d m:=hsmall'
    _=(n:ℝ)^(fullExponent K k c d m+δ+ε):=by rw [←Real.rpow_add hnR,←Real.rpow_add hnR]; congr 1; ring
    _≤_:=Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn.le) hgap.le

end ThreeSum.TernaryActualPrefixRuntime
