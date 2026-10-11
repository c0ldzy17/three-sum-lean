import Submission.ThreeSum.SharedTraversalPrefixCosts
import Submission.ThreeSum.ReportingHostSuffixCosts
import Submission.ThreeSum.LocalParameterBounds

/-!
# Polynomial overhead of the actual traversal operations

All logarithmic residue costs are bounded before the binomial work terms
are charged. This prevents an endpoint magnitude from being used as a
running-time bound. The final scalar overhead is polynomial in the block
dimensions and will therefore have exponent zero at the prescribed scales.
-/

namespace ThreeSum.SharedTraversalCosts

open Finset Light LocalCoverBounds LightBlockQuery ReportingHostLevelData
open SubsetAddress
open scoped BigOperators

set_option maxHeartbeats 2400000
set_option maxRecDepth 12000

def size (h J : ℕ) : ℕ := (J+1)*(2048*h+20)
def overhead (h J : ℕ) : ℕ := 200000*(size h J)^4

theorem size_bounds (h J : ℕ) :
    1 ≤ size h J ∧ J+1 ≤ size h J ∧ 512*h+1 ≤ size h J ∧
      width h J+1 ≤ size h J ∧
      1026*h+4 ≤ size h J ∧
      J*(512*h)+(514*h+2)*(J+1)+2 ≤ size h J := by
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> simp only [size,width] <;> nlinarith

theorem log_local_le (h : ℕ) : Nat.log 2 (512*h*localPrime h+1)+1 ≤ 1026*h+4 := by
  have hp := LocalParameterBounds.prime_bound h
  have hw : 512*h ≤ 2^(512*h) := (Nat.lt_two_pow_self (n := 512*h)).le
  have hh : 512*h*localPrime h ≤ 2^(1026*h+2) := by
    calc
      _ ≤ 2^(512*h)*2^(514*h+2) := Nat.mul_le_mul hw hp
      _ = _ := by rw [← pow_add]; congr 1; omega
  have hh' : 512*h*localPrime h+1 ≤ 2^(1026*h+3) := by
    have hz := Nat.two_pow_pos (1026*h+2)
    rw [show 1026*h+3=(1026*h+2)+1 by omega,pow_succ]
    omega
  have hl := Nat.log_mono_right (b := 2) hh'
  rw [Nat.log_pow (by decide)] at hl
  omega

theorem log_endpoint_le (h J : ℕ) :
    Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1)+1 ≤
      J*(512*h)+(514*h+2)*(J+1)+2 := by
  let W := J*(512*h)
  let E := W+(514*h+2)*(J+1)
  have hpow : localPrime h^J*localPrime h ≤ 2^((514*h+2)*(J+1)) := by
    rw [← pow_succ]
    exact (Nat.pow_le_pow_left (LocalParameterBounds.prime_bound h) _).trans_eq
      (pow_mul _ _ _).symm
  have hw : W ≤ 2^W := (Nat.lt_two_pow_self (n := W)).le
  have he : LightBlockSourceBuild.endpointBound h J ≤ 2^E := by
    unfold LightBlockSourceBuild.endpointBound
    change W*(localPrime h^J*localPrime h) ≤ 2^E
    exact (Nat.mul_le_mul hw hpow).trans_eq (pow_add 2 W ((514*h+2)*(J+1))).symm
  have he' : LightBlockSourceBuild.endpointBound h J+1 ≤ 2^(E+1) := by
    have hz := Nat.two_pow_pos E
    rw [pow_succ]
    omega
  have hl := Nat.log_mono_right (b := 2) he'
  rw [Nat.log_pow (by decide)] at hl
  dsimp [E,W] at hl
  omega

theorem residue_le_size (h J : ℕ) :
    LightResidues.residueBudget (LightBlockSourceBuild.endpointBound h J) ≤ 77*size h J := by
  have hb := size_bounds h J
  have hl := log_endpoint_le h J
  unfold LightResidues.residueBudget
  omega

theorem preparation_time_le (h J n : ℕ) :
    LightSourcePreparation.time n J (512*h) (localPrime h) ≤
      4000*(size h J)^2*(n+1) := by
  let B := size h J
  have hb := size_bounds h J
  have hlog := (log_local_le h).trans hb.2.2.2.2.1
  have hJ : J+1 ≤ B := hb.2.1
  have hL : 512*h+1 ≤ B := hb.2.2.1
  have hW : J*(512*h)+1 ≤ B := hb.2.2.2.1
  have hp : 1 ≤ B := hb.1
  have hB : B ≤ B^2 := Nat.le_self_pow (by decide) _
  have hbase := Nat.mul_le_mul hJ hL
  have hrow : J*(150*(512*h)+464*(Nat.log 2 (512*h*localPrime h+1)+1)+250) ≤
      864*B^2 := by
    calc
      _ ≤ B*(864*B) := Nat.mul_le_mul (by omega : J ≤ B) (by omega)
      _ = _ := by ring
  have hmain : 300*(J*(512*h)+1)^2+
      J*(150*(512*h)+464*(Nat.log 2 (512*h*localPrime h+1)+1)+250)+400 ≤ 1564*B^2 := by
    have hs := Nat.pow_le_pow_left hW 2
    nlinarith
  have htime := LightSourcePreparation.time_bound n J (512*h) (localPrime h)
  have hfirst : 300*(J+1)*(512*h+1) ≤ 300*B^2 := by nlinarith [hbase]
  have hsecond := Nat.mul_le_mul_right (n+1) (show 600*(J*(512*h)+1) ≤ 600*B^2 by omega)
  have hthird := Nat.mul_le_mul_left n hmain
  change LightSourcePreparation.time n J (512*h) (localPrime h) ≤ 4000*B^2*(n+1)
  nlinarith

theorem terminal_charge_le (h J K : ℕ) :
    ReportingHostTerminalFrontier.charge h J K+240 ≤
      31000*(size h J)^2*2^((J-K)*(2*h)) := by
  let B := size h J
  let T := 2^((J-K)*(2*h))
  have hb := size_bounds h J
  have hp : 1 ≤ B := hb.1
  have ht : 1 ≤ T := Nat.two_pow_pos _
  have hB : B ≤ B^2 := Nat.le_self_pow (by decide) _
  have hc : LightReportingTerminalMasks.count h J K ≤ T := Nat.choose_le_two_pow _ _
  have hr : (J-K)*(2*h)+1 ≤ B := by
    have hs := Nat.mul_le_mul (Nat.sub_le J K) (by omega : 2*h ≤ 512*h)
    have hw := hb.2.2.2.1
    change J*(512*h)+1 ≤ B at hw
    omega
  have hbin := (LightReportingBinomial.time_bound ((J-K)*(2*h))).trans
    (Nat.mul_le_mul_left 1100 (Nat.pow_le_pow_left hr 2))
  have hbinT := hbin.trans (Nat.le_mul_of_pos_right _ ht)
  have hmask := LightReportingTerminalMasks.time_bound h J K
  have hmaskT : LightReportingTerminalMasks.time h J K ≤ 3200*B^2*T := by
    calc
      _ ≤ 1600*B^2*(2*T) := hmask.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left 1600 (Nat.pow_le_pow_left hb.2.2.2.1 2)) (by change T+1 ≤ 2*T; omega))
      _ = _ := by ring
  have hprep := preparation_time_le h J (LightReportingTerminalMasks.count h J K)
  have hprepT : LightReportingTerminalPreparation.time h J (LightReportingTerminalMasks.count h J K) ≤
      16800*B^2*T := by
    have hm := hprep.trans (Nat.mul_le_mul_left (4000*B^2) (show
      LightReportingTerminalMasks.count h J K+1 ≤ 2*T by omega))
    unfold LightReportingTerminalPreparation.time
    nlinarith [Nat.mul_le_mul (Nat.one_le_pow 2 B hp) ht]
  have hres := residue_le_size h J
  have hresT : (2*LightResidues.residueBudget (LightBlockSourceBuild.endpointBound h J)+1300)*T ≤
      1454*B^2*T := Nat.mul_le_mul_right T (by nlinarith)
  have hconstant : 2070 ≤ 2070*B^2*T := by
    have hh := Nat.mul_le_mul (Nat.one_le_pow 2 B hp) ht
    nlinarith
  unfold ReportingHostTerminalFrontier.charge
  change LightReportingBinomial.time ((J-K)*(2*h))+LightReportingTerminalMasks.time h J K+
    LightReportingTerminalPreparation.time h J (LightReportingTerminalMasks.count h J K)+
    (2*LightResidues.residueBudget (LightBlockSourceBuild.endpointBound h J)+1300)*T+1830+240 ≤
      31000*B^2*T
  nlinarith only [hbinT,hmaskT,hprepT,hresT,hconstant]

theorem query_items_le_layer {c t : ℕ} (ht : t ≤ c/2) :
    LightSparseQuery.queryItems c t+1 ≤ (c+2)*c.choose t := by
  have htc : t ≤ c := ht.trans (Nat.div_le_self _ _)
  simpa only [LightSparseQuery.queryItems,downsetCap,Nat.min_eq_left htc,layerOffset_succ]
    using ReportingHostSuffixCosts.downsetCap_add_one_le_layer ht

theorem residual_le_size (h J k : ℕ) : residualSize h J k+2 ≤ 2*size h J := by
  have hb := (size_bounds h J).2.2.2.1
  have hr : residualSize h J k ≤ width h J :=
    Nat.mul_le_mul (Nat.sub_le _ _) (by omega)
  omega

theorem expansion_le_layer {h J k t : ℕ} (hk : k < J)
    (ht : t ≤ residualSize h J (k+1)/2) :
    LightReportingPositiveExpand.time h J k t+200 ≤
      overhead h J*groupSize h*(residualSize h J (k+1)).choose t := by
  let B := size h J
  let Q := (residualSize h J (k+1)).choose t
  have hb := size_bounds h J
  have hB : 1 ≤ B^4 := Nat.one_le_pow _ _ hb.1
  have hq : 1 ≤ Q := Nat.choose_pos (ht.trans (Nat.div_le_self _ _))
  have hg : 1 ≤ groupSize h := Nat.choose_pos (by omega)
  have hqitems := query_items_le_layer ht
  have hqB := hqitems.trans (Nat.mul_le_mul_right Q (residual_le_size h J (k+1)))
  have he := LightReportingPositiveExpand.time_bound hk (by omega : t ≤ residualSize h J (k+1)+1)
  have he' : LightReportingPositiveExpand.time h J k t ≤ 104000*B^4*groupSize h*Q := by
    calc
      _ ≤ 26000*B^3*(2*B*Q)*(2*groupSize h) := he.trans
        (Nat.mul_le_mul (Nat.mul_le_mul
          (Nat.mul_le_mul_left 26000 (Nat.pow_le_pow_left hb.2.2.2.1 3)) hqB) (by omega))
      _ = _ := by ring
  have h1 := Nat.mul_le_mul (Nat.mul_le_mul hB hg) hq
  unfold overhead
  change _ ≤ 200000*B^4*groupSize h*Q
  nlinarith

theorem initial_le_layer {h J K : ℕ} (D : ℕ → Catalog) (hK : K ≤ J)
    (ht : (D 0).t ≤ residualSize h J 0/2) :
    initialUnit h J D K ≤ overhead h J*(residualSize h J 0).choose (D 0).t := by
  let B := size h J
  let Q := (residualSize h J 0).choose (D 0).t
  have hb := size_bounds h J
  have hB : B ≤ B^4 := Nat.le_self_pow (by decide) _
  have hq : 1 ≤ Q := Nat.choose_pos (ht.trans (Nat.div_le_self _ _))
  have hqitems := query_items_le_layer ht
  have hqB := hqitems.trans (Nat.mul_le_mul_right Q (residual_le_size h J 0))
  have hquery := LightReportingCatalogQuery.time_bound (Nat.zero_le J)
    (by omega : (D 0).t ≤ residualSize h J 0+1)
  have hquery' : LightReportingCatalogQuery.time h J 0 (D 0).t ≤ 40000*B^4*Q := by
    calc
      _ ≤ 20000*B^3*(2*B*Q) := hquery.trans (Nat.mul_le_mul
        (Nat.mul_le_mul_left 20000 (Nat.pow_le_pow_left hb.2.2.2.1 3)) hqB)
      _ = _ := by ring
  have hscalar : LightBlockMasks.time J (512*h)+1300*K+3420 ≤ 5000*B := by
    unfold LightBlockMasks.time powTableTime
    have hh := hb.2.2.1
    have hj := hb.2.1
    omega
  have hs := hscalar.trans ((Nat.mul_le_mul_left 5000 hB).trans (Nat.le_mul_of_pos_right _ hq))
  unfold initialUnit LightReportingWantedInitialize.time LightReportingInitializeStored.time
    LightReportingInitialize.time LightDenseGuard.time overhead
  change _ ≤ 200000*B^4*Q
  nlinarith only [hquery',hs]

end ThreeSum.SharedTraversalCosts
