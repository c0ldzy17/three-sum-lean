import Submission.ThreeSum.TernaryActualColoredRuntime
import Submission.ThreeSum.TernaryUniformQueryTime

/-! Exact additive pricing for a single global query-time maximum. The
operational setup and every memory header remain the actual ones. -/
noncomputable section
namespace ThreeSum.TernaryActualGlobalQueryRuntime
open Light Real Filter StageBounds
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryArenaSeedCandidate TernaryNativeCompleteFrontend
open TernaryActualPrefixRuntime TernaryActualSeedRuntime TernaryActualColoredRuntime
open TernaryOversizePrime TernaryOversizeRates TernaryOversizeOverhead TernaryCoverScale TernaryEntropyRates
open scoped Topology BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000
attribute [local instance] Classical.propDecidable

def zeroInput (I : Input) : Input :={I with queryTime:=0}

def zeroState {K m : ℕ} (S : State K m) : State K m where
  arena:=S.arena
  phase:=fun j=>zeroInput (S.phase j)
  seeds:=S.seeds
  post:=zeroInput S.post
  cleanup:=S.cleanup
  keysB:=S.keysB
  keysC:=S.keysC

def queryCap {K m : ℕ} (S : State K m) (n : ℕ) : ℕ :=
  max ((Finset.range (radixLength m n+1)).sup (fun j=>(S.phase j).queryTime)) S.post.queryTime

def wantedCap (K k m F n digitLength : ℕ) : ℕ :=
  n*2^digitLength*(outputCap K k m F)^radixLength m n

def extraCoefficient (K k c d m F D E κ B H : ℕ) : ℝ :=
  ((16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*H+1)).length:ℕ):ℝ)*
    (TernaryUniformQueryTime.coefficient m D E κ:ℝ)*volumeConstant K k c d m

/-- The stable size-only whole-child budget with one global query maximum. -/
def uniformTime (K k c d m F D E κ B H β n : ℕ) : ℕ :=
  TernaryActualColoredRuntime.uniformTime K k c d m F D E κ B H β n+
    TernaryActualColoredRuntime.envelope (extraCoefficient K k c d m F D E κ B H) 10 m β κ n

theorem query_le_cap {K m : ℕ} (S : State K m) (n j : ℕ) (hj : j≤radixLength m n) :
    (S.phase j).queryTime≤queryCap S n:=by
  exact (Finset.le_sup (f:=fun j=>(S.phase j).queryTime) (Finset.mem_range.mpr (by omega))).trans (Nat.le_max_left _ _)

theorem queryCap_le {K m n q : ℕ} (S : State K m)
    (hphase : ∀j≤radixLength m n,(S.phase j).queryTime≤q) (hpost : S.post.queryTime≤q) :
    queryCap S n≤q:=by
  apply max_le _ hpost
  exact Finset.sup_le (fun j hj=>hphase j (by have := Finset.mem_range.mp hj; omega))

theorem host_query_split {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m) (I : Input) :
    (nativeHost (K:=K) (k:=k) j maps Q I).runtime=
      (nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)).runtime+
        (nativeHost (K:=K) (k:=k) j maps Q I).front.count*I.queryTime:=by
  let H:=nativeHost (K:=K) (k:=k) j maps Q I
  let Z:=nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)
  have hL : H.left=Z.left:=rfl
  have hR : H.right=Z.right:=rfl
  have hfront : H.front.runtime=Z.front.runtime+H.front.count*I.queryTime:=by
    change LightTernaryCountFrontend.time H.front.groups (N m j) H.front.f.L H.front.f.nb H.front.count I.queryTime=
      LightTernaryCountFrontend.time H.front.groups (N m j) H.front.f.L H.front.f.nb H.front.count 0+H.front.count*I.queryTime
    unfold LightTernaryCountFrontend.time LightTernaryWantedRows.time LightTernaryWantedRowDispatch.time
    ring
  change H.runtime=Z.runtime+H.front.count*I.queryTime
  unfold TernarySourceCountExecutionFactory.Setup.runtime LightTernarySourceCountHost.time
  rw [hL,hR,hfront]
  ring

theorem seed_query_split {K k m F j seed : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs)
    (D : LightTernarySeedScoreFactory.Data (config (nativePrime K m) j I A seed)) :
    LightTernarySeedScoreFactory.runtime D
      (nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m))=
    LightTernarySeedScoreFactory.runtime D
      (nativeHost (K:=K) (k:=k) j maps Q (sourceInput (zeroInput I) A seed D)) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m))+
      (A.J+2)^4*(nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)).front.count*I.queryTime:=by
  have hh:=host_query_split (k:=k) (j:=j) maps Q (sourceInput I A seed D)
  change (nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)).runtime=
    (nativeHost (K:=K) (k:=k) j maps Q (sourceInput (zeroInput I) A seed D)).runtime+
      (nativeHost (K:=K) (k:=k) j maps Q (sourceInput I A seed D)).front.count*I.queryTime at hh
  unfold LightTernarySeedScoreFactory.runtime LightTernarySeedScore.time LightTernaryTensorDriver.time
  rw [hh]
  dsimp only [config]
  ring

theorem wanted_count_le_cap {K k m F n digitLength j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (I : Input)
    (hF : 0<F) (hj : j≤radixLength m n) (hrequest : I.requesterCount≤n*2^digitLength) :
    (entries (r:=j) maps (threshold K k m) I).length≤wantedCap K k m F n digitLength:=by
  have hpos : 1≤outputCap K k m F:=by
    unfold outputCap
    exact Nat.succ_le_iff.mpr (Nat.mul_pos hF (TernaryGoodOutputCatalog.cap_pos (TernaryCoverCapParameters.rawThreshold_pos _ _ _)))
  have hc:=wanted_entries_cap (j:=j) maps (threshold K k m) I
  exact hc.trans (Nat.mul_le_mul hrequest (Nat.pow_le_pow_right hpos hj))

def prefixCorrection {K m : ℕ} (k F : ℕ) (S : State K m) (n : ℕ) : ℕ :=
  radixLength m n*(menuSize K m S.arena.J*menuSize K m S.arena.J+1)*(S.arena.J+2)^4*
    wantedCap K k m F n S.arena.J*queryCap S n

theorem seed_max_query_bound {K k m F n j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F) (hj : j≤radixLength m n)
    (hrequest : (S.phase j).requesterCount≤n*2^S.arena.J) :
    prefixSeedTime (K:=K) (k:=k) maps Q (S.phase j) S.arena (S.seeds j)≤
      prefixSeedTime (K:=K) (k:=k) maps Q ((zeroState S).phase j) S.arena ((zeroState S).seeds j)+
        (S.arena.J+2)^4*wantedCap K k m F n S.arena.J*queryCap S n:=by
  unfold prefixSeedTime
  apply Finset.sup_le
  intro seed hseed
  have hs:=seed_query_split (k:=k) (j:=j) maps Q (S.phase j) S.arena (S.seeds j seed)
  have hc:=wanted_count_le_cap (k:=k) (j:=j) maps (sourceInput (S.phase j) S.arena seed (S.seeds j seed)) hF hj hrequest
  have ht:=query_le_cap S n j hj
  have hmul:=Nat.mul_le_mul (Nat.mul_le_mul_left ((S.arena.J+2)^4) hc) ht
  have hzero:=Finset.le_sup (f:=fun seed=>LightTernarySeedScoreFactory.runtime (S.seeds j seed)
    (nativeHost (K:=K) (k:=k) j maps Q (sourceInput (zeroInput (S.phase j)) S.arena seed (S.seeds j seed))) K
      (4^fixedLength m) F (outputCap K k m F) ((nativePrime K m)*(nativePrime K m+1)^j)
      (TernaryGoodOutputCatalog.raws maps (threshold K k m))
      (TernaryGoodOutputCatalog.wordCodes maps (threshold K k m))
      (TernaryGoodOutputCatalog.mapCodes maps (threshold K k m))) hseed
  change _≤_ at hc
  rw [hs]
  exact Nat.add_le_add hzero hmul

theorem controller_time_add (q s t span : ℕ) :
    LightTernarySeedController.time (q*q) (s+t) span=
      LightTernarySeedController.time (q*q) s span+(q*q+1)*t:=by
  unfold LightTernarySeedController.time
  ring

theorem stage_query_bound {K k m F n j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F) (hj : j≤radixLength m n)
    (hrequest : (S.phase j).requesterCount≤n*2^S.arena.J) :
    prefixStageTime (K:=K) (k:=k) maps Q (S.phase j) S.arena (S.seeds j)≤
      prefixStageTime (K:=K) (k:=k) maps Q ((zeroState S).phase j) S.arena ((zeroState S).seeds j)+
        (menuSize K m S.arena.J*menuSize K m S.arena.J+1)*(S.arena.J+2)^4*
          wantedCap K k m F n S.arena.J*queryCap S n:=by
  have hs:=seed_max_query_bound (k:=k) (j:=j) maps Q S hF hj hrequest
  have hm:=Nat.mul_le_mul_left (menuSize K m S.arena.J*menuSize K m S.arena.J+1) hs
  unfold prefixStageTime prefixControllerTime LightTernarySeedController.time
  change _≤_ at hm
  dsimp only [zeroState,zeroInput,prefixOverhead] at hm ⊢
  nlinarith only [hm]

theorem all_prefix_query_bound {K k m F n : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F)
    (hrequest : ∀j≤radixLength m n,(S.phase j).requesterCount≤n*2^S.arena.J) :
    allPrefixTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n≤
      allPrefixTime (K:=K) (k:=k) maps Q (zeroState S).phase S.arena (zeroState S).seeds n+
        prefixCorrection k F S n:=by
  let extra:=(menuSize K m S.arena.J*menuSize K m S.arena.J+1)*(S.arena.J+2)^4*
    wantedCap K k m F n S.arena.J*queryCap S n
  have hmax : allStageTime (K:=K) (k:=k) maps Q S.phase S.arena S.seeds n≤
      allStageTime (K:=K) (k:=k) maps Q (zeroState S).phase S.arena (zeroState S).seeds n+extra:=by
    unfold allStageTime
    apply Finset.sup_le
    intro old hold
    have hj : old+1≤radixLength m n:=Finset.mem_range.mp hold
    have hh:=stage_query_bound (k:=k) (j:=old+1) maps Q S hF hj (hrequest _ hj)
    have hz:=Finset.le_sup (f:=fun old=>prefixStageTime (K:=K) (k:=k) maps Q
      ((zeroState S).phase (old+1)) S.arena ((zeroState S).seeds (old+1))) hold
    exact hh.trans (Nat.add_le_add_right hz extra)
  have hh:=Nat.mul_le_mul_left (radixLength m n) hmax
  unfold allPrefixTime LightTernaryPrefixInit.time LightTernaryPrefixLoop.time prefixCorrection
  dsimp only [zeroState,zeroInput,config] at *
  dsimp [extra] at hh
  nlinarith only [hh]

private theorem channel_time_add (steps : List LightTernaryFixedChannelLoop.Channel)
    (cost : LightTernaryFixedChannelLoop.Channel→ℕ)
    (arity delta : ℕ) :
    LightTernaryFixedChannelLoop.time steps (fun c=>cost c+delta) arity=
      LightTernaryFixedChannelLoop.time steps cost arity+steps.length*delta:=by
  induction steps with
  | nil => simp [LightTernaryFixedChannelLoop.time]
  | cons c cs ih => simp only [LightTernaryFixedChannelLoop.time,List.length_cons,ih]; ring

theorem reporter_query_split {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (Hdet : ℕ) :
    let H:=nativeHost (K:=K) (k:=k) j maps Q I
    let Z:=nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)
    LightTernaryMomentReporter.time H Hdet=LightTernaryMomentReporter.time Z Hdet+
      (TernaryMomentSchedule.channels (2*Hdet+1)).length*H.front.count*I.queryTime:=by
  let H:=nativeHost (K:=K) (k:=k) j maps Q I
  let Z:=nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)
  have hcount : H.front.count=Z.front.count:=rfl
  have hargv : H.argv=Z.argv:=rfl
  have hleft : H.left.NL=Z.left.NL:=rfl
  have hright : H.right.NL=Z.right.NL:=rfl
  have hh:=host_query_split (k:=k) (j:=j) maps Q I
  have hcost : LightTernaryCertifiedMomentDriver.cost H=
      fun c=>LightTernaryCertifiedMomentDriver.cost Z c+H.front.count*I.queryTime:=by
    funext c
    unfold LightTernaryCertifiedMomentDriver.cost LightTernaryMomentChannelStep.time
    rw [hh,hleft,hright,hcount]
    ring
  change LightTernaryMomentReporter.time H Hdet=_
  unfold LightTernaryMomentReporter.time LightTernaryCertifiedMomentDriver.time LightTernaryMomentDriver.time
  rw [hargv,hcount,hcost]
  rw [hcount]
  rw [channel_time_add]
  simp only [LightTernaryMomentDriver.labels,List.length_map,List.length_range]
  ring

theorem prepared_post_query_split {K k m F j : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (Hdet : ℕ) (L : LightOriginalSurvivorPair.Layout) (keysB keysC : ℕ→ℕ) :
    let H:=nativeHost (K:=K) (k:=k) j maps Q I
    let Z:=nativeHost (K:=K) (k:=k) j maps Q (zeroInput I)
    LightTernaryPreparedPostSelection.time H Hdet L keysB keysC=
      LightTernaryPreparedPostSelection.time Z Hdet L keysB keysC+
        (TernaryMomentSchedule.channels (2*Hdet+1)).length*H.front.count*I.queryTime:=by
  have hh:=reporter_query_split (k:=k) (j:=j) maps Q I Hdet
  dsimp only at hh ⊢
  unfold LightTernaryPreparedPostSelection.time LightTernaryPostSelection.time LightTernaryCompactReporter.time
  rw [hh]
  ring

def totalCorrection {K m : ℕ} (k F Hdet : ℕ) (S : State K m) (n : ℕ) : ℕ :=
  prefixCorrection k F S n+(TernaryMomentSchedule.channels (2*Hdet+1)).length*
    wantedCap K k m F n S.arena.J*queryCap S n

theorem time_query_bound {K k m F β κ n D E B Hdet : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (S : State K m) (hF : 0<F)
    (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B) :
    TernaryActualColoredRuntime.time (k:=k) maps Q S E κ Hdet n≤
      TernaryActualColoredRuntime.time (k:=k) maps Q (zeroState S) E κ Hdet n+
        totalCorrection k F Hdet S n:=by
  have hp:=all_prefix_query_bound (k:=k) maps Q S hF (fun j hj=>(H.phases j hj).requesters)
  have hpost:=prepared_post_query_split (k:=k) (j:=radixLength m n) maps Q S.post Hdet S.cleanup S.keysB S.keysC
  have hc:=wanted_count_le_cap (k:=k) (j:=radixLength m n) maps S.post hF (le_refl _) H.post.requesters
  have ht : S.post.queryTime≤queryCap S n:=Nat.le_max_right _ _
  have hcorr:=Nat.mul_le_mul
    (Nat.mul_le_mul_left (TernaryMomentSchedule.channels (2*Hdet+1)).length hc) ht
  unfold TernaryActualColoredRuntime.time totalCorrection
  dsimp only [zeroState] at *
  rw [hpost]
  change (TernaryMomentSchedule.channels (2*Hdet+1)).length*
    (nativeHost (K:=K) (k:=k) (radixLength m n) maps Q S.post).front.count*S.post.queryTime≤_ at hcorr
  nlinarith only [hp,hcorr]

theorem charged_query_product {K k b m F β κ n D E B : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (S : State K m) (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hF : F≤(nativeFamily K m k).length) (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hquery : (queryCap S n:ℝ)≤(TernaryUniformQueryTime.coefficient m D E κ:ℝ)*
      (S.arena.J+1:ℕ)^3*TernaryCountFrontendBudget.envelope m (radixLength m n))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d) :
    ((wantedCap K k m F n S.arena.J*queryCap S n:ℕ):ℝ)≤
      (TernaryUniformQueryTime.coefficient m D E κ:ℝ)*volumeConstant K k c d m*
        (S.arena.J+1:ℕ)^3*(2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:=by
  let R:=radixLength m n
  let X:=(nativeFactor K k b m:ℝ)^R*(n:ℝ)*((nativePrime K m:ℝ)/(partitionCap m:ℝ))^R
  have hw:=wanted_work_bound (j:=R) hK hF hb (le_refl (n*2^S.arena.J))
  have hw' : (wantedCap K k m F n S.arena.J:ℝ)≤(2:ℝ)^S.arena.J*X:=by
    simpa only [wantedCap,R,Nat.cast_pow,Nat.cast_ofNat,X,mul_assoc,mul_left_comm,mul_comm] using hw
  have hv : X*TernaryCountFrontendBudget.envelope m R≤volumeBundle K k b m n R:=by
    unfold volumeBundle
    dsimp [X]
    have hnon : 0≤(nativeFactor K k b m:ℝ)^R*((TernaryDimensionBounds.bankSize m R:ℝ)+
      (endpointSize m:ℝ)^R+(nativePrime K m:ℝ)^R):=by positivity
    nlinarith only [hnon]
  have hvol:=volume_bundle_bound (j:=R) hK hk hgood.1 hn (le_refl _) c d hpoly
  have hm:=mul_le_mul hw' hquery (Nat.cast_nonneg _) (by positivity)
  have hh:=mul_le_mul_of_nonneg_left (hv.trans hvol)
    (show (0:ℝ)≤(TernaryUniformQueryTime.coefficient m D E κ:ℝ)*(S.arena.J+1:ℕ)^3*(2:ℝ)^S.arena.J by positivity)
  dsimp only [R] at hh
  push_cast at hm hh ⊢
  nlinarith only [hm,hh]

theorem correction_polynomial {K k m F n Hdet : ℕ} (S : State K m)
    (hJ : radixLength m n≤S.arena.J) :
    totalCorrection k F Hdet S n≤
      (16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*Hdet+1)).length)*
        (S.arena.J+1)^7*(wantedCap K k m F n S.arena.J*queryCap S n):=by
  have hmenu:=menu_square_bound K m S.arena.J
  have hcoord : (S.arena.J+2)^4≤16*(S.arena.J+1)^4:=by nlinarith only [Nat.pow_le_pow_left (show S.arena.J+2≤2*(S.arena.J+1) by omega) 4]
  have hmult:=Nat.mul_le_mul (Nat.mul_le_mul hJ hmenu) hcoord
  have hmain : radixLength m n*(menuSize K m S.arena.J*menuSize K m S.arena.J+1)*(S.arena.J+2)^4≤
      16*menuCoefficient K (nativePrime K m)*(S.arena.J+1)^7:=by
    have hh : S.arena.J≤S.arena.J+1:=by omega
    have hh':=Nat.mul_le_mul_right (menuCoefficient K (nativePrime K m)*(S.arena.J+1)^2*(16*(S.arena.J+1)^4)) hh
    nlinarith only [hmult,hh']
  have hm:=Nat.mul_le_mul_right (wantedCap K k m F n S.arena.J*queryCap S n) hmain
  have hpow : 1≤(S.arena.J+1)^7:=Nat.one_le_pow _ _ (by omega)
  have ha:=Nat.mul_le_mul_right
    ((TernaryMomentSchedule.channels (2*Hdet+1)).length*(wantedCap K k m F n S.arena.J*queryCap S n)) hpow
  unfold totalCorrection prefixCorrection
  nlinarith only [hm,ha]

theorem extraCoefficient_nonneg (K k c d m F D E κ B H : ℕ) :
    0≤extraCoefficient K k c d m F D E κ B H:=by
  unfold extraCoefficient
  positivity [volumeConstant_nonneg K k c d m]

theorem correction_bound {K k b m F β κ n D E B Hdet : ℕ}
    (maps : Fin F→Weight m (nativePrime K m)) (Q : TernaryGoodOutputCatalog.Output m)
    (S : State K m) (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hF : F≤(nativeFamily K m k).length) (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hquery : (queryCap S n:ℝ)≤(TernaryUniformQueryTime.coefficient m D E κ:ℝ)*
      (S.arena.J+1:ℕ)^3*TernaryCountFrontendBudget.envelope m (radixLength m n))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤TernaryCountFrontendBudget.frontendExponent) :
    (totalCorrection k F Hdet S n:ℝ)≤
      extraCoefficient K k c d m F D E κ B Hdet*(J m β κ n+1:ℕ)^10*
        (2:ℝ)^J m β κ n*(n:ℝ)^TernaryCountFrontendBudget.frontendExponent:=by
  have hd : S.arena.J=J m β κ n:=H.dimension
  have hJ : radixLength m n≤S.arena.J:=by
    rw [hd]
    exact (TernarySignedPadding.padded_length_proper β (n^κ) (radixLength m n)).le
  have hc:=correction_polynomial (k:=k) (F:=F) (Hdet:=Hdet) S hJ
  have hc' : (totalCorrection k F Hdet S n:ℝ)≤
      ((16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*Hdet+1)).length:ℕ):ℝ)*
        (S.arena.J+1:ℕ)^7*(wantedCap K k m F n S.arena.J*queryCap S n:ℕ):=by exact_mod_cast hc
  have hp:=charged_query_product maps Q S H hK hk hgood hn hF hb hquery c d hpoly
  have hs:=mul_le_mul_of_nonneg_left hp (show (0:ℝ)≤
      ((16*menuCoefficient K (nativePrime K m)+(TernaryMomentSchedule.channels (2*Hdet+1)).length:ℕ):ℝ)*
        (S.arena.J+1:ℕ)^7 by positivity)
  have hmain : (totalCorrection k F Hdet S n:ℝ)≤
      extraCoefficient K k c d m F D E κ B Hdet*(S.arena.J+1:ℕ)^10*
        (2:ℝ)^S.arena.J*(n:ℝ)^fullExponent K k c d m:=by
    apply (hc'.trans hs).trans_eq
    unfold extraCoefficient
    ring
  have hpow:=Real.rpow_le_rpow_of_exponent_le (show (1:ℝ)≤n by exact_mod_cast hn.le) hcharge
  have hx:=mul_le_mul_of_nonneg_left hpow (show (0:ℝ)≤
    extraCoefficient K k c d m F D E κ B Hdet*(S.arena.J+1:ℕ)^10*(2:ℝ)^S.arena.J by
      positivity [extraCoefficient_nonneg K k c d m F D E κ B Hdet])
  rw [←hd]
  exact hmain.trans hx

theorem time_le_uniform {K k b m F β κ n D E B Hdet : ℕ}
    {maps : Fin F→Weight m (nativePrime K m)} {Q : TernaryGoodOutputCatalog.Output m}
    {S : State K m} (H : Fits (k:=k) maps Q (zeroState S) β κ n D E B)
    (hK : 0<K) (hk : 0<k) (hgood : GoodBlock K m) (hn : 1<n)
    (hFpos : 0<F) (hF : F≤(nativeFamily K m k).length)
    (hb : TernaryActualPrefixRuntime.localFactor m≤b)
    (hposL : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) false).length)
    (hposR : 1≤(localRecords maps (TernaryCoverCapParameters.sourceCap m (nativePrime K m)) true).length)
    (hquery : (queryCap S n:ℝ)≤(TernaryUniformQueryTime.coefficient m D E κ:ℝ)*
      (S.arena.J+1:ℕ)^3*TernaryCountFrontendBudget.envelope m (radixLength m n))
    (c d : ℕ) (hpoly : b≤c*(fixedLength m+1)^d)
    (hcharge : fullExponent K k c d m≤TernaryCountFrontendBudget.frontendExponent) :
    TernaryActualColoredRuntime.time (k:=k) maps Q S E κ Hdet n≤
      uniformTime K k c d m F D E κ B Hdet β n:=by
  have ht:=time_query_bound (Hdet:=Hdet) maps Q S hFpos H
  have hz:=TernaryActualColoredRuntime.time_le_uniform (Hdet:=Hdet) H hK hk hgood hn hFpos hF hb hposL hposR c d hpoly hcharge
  have hc:=correction_bound (Hdet:=Hdet) maps Q S H hK hk hgood hn hF hb hquery c d hpoly hcharge
  have hceil : totalCorrection k F Hdet S n≤
      TernaryActualColoredRuntime.envelope (extraCoefficient K k c d m F D E κ B Hdet) 10 m β κ n:=by
    have hh : (totalCorrection k F Hdet S n:ℝ)≤
        (TernaryActualColoredRuntime.envelope (extraCoefficient K k c d m F D E κ B Hdet) 10 m β κ n:ℝ):=by
      exact hc.trans (Nat.le_ceil _)
    exact_mod_cast hh
  exact ht.trans (Nat.add_le_add hz hceil)

theorem PB {K k c d m F D E κ B H β : ℕ} {δ : ℝ}
    (hm : 0<m) (hβ : 1<β) (hδ : 0≤δ)
    (hcarry : TernarySignedPadding.carryExponent m β (κ:ℝ)<δ)
    (hroom : TernaryCountFrontendBudget.frontendExponent+δ≤TernaryActualColoredRuntime.exponent) :
    PowerBound (uniformTime K k c d m F D E κ B H β) TernaryActualColoredRuntime.exponent:=by
  have he:=TernaryActualColoredRuntime.envelope_powerBound hm hβ hδ hcarry
    (extraCoefficient K k c d m F D E κ B H)
    (extraCoefficient_nonneg K k c d m F D E κ B H) 10
  exact (TernaryActualColoredRuntime.PB hm hβ hδ hcarry hroom).add_same (he.mono_exponent hroom)

end ThreeSum.TernaryActualGlobalQueryRuntime
