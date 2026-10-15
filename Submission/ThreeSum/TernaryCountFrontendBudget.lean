import Submission.ThreeSum.LightTernaryCountFrontend
import Submission.ThreeSum.TernaryOversizeDimensions

/-! Budgets for the actual natural running-time functions of the physical
count frontend, including real near setup and frozen-query execution. -/
noncomputable section
namespace ThreeSum.TernaryCountFrontendBudget
open Filter Real Asymptotics
open TernaryJointType TernaryBank TernaryParameters TernaryDimensionBounds
open TernaryEntropyRates TernaryLocalParameters TernaryCoverScale TernaryOversizePrime TernaryOversizeRates
open TernaryCoverCapParameters
open TernaryOversizeOverhead TernaryOversizeDimensions TernaryPrincipalDimensions
open LightTernaryNearPair
open scoped Topology
set_option maxHeartbeats 5000000
set_option maxRecDepth 16000

def envelope (m j : ℕ) : ℝ :=
  Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy)/z

theorem envelope_pos (m j : ℕ) : 0<envelope m j :=
  div_pos (Real.exp_pos _) gibbs_parameters.2.2.1

theorem gibbs_expression {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (1+z)^digitCount Q 1*(1+z+z^2)^digitCount Q 2 / z^(queryDeficit m j)=envelope m j := by
  have hz := gibbs_parameters.2.2.1
  have h1 : 0<1+z := by linarith
  have h2 : 0<1+z+z^2 := by nlinarith [sq_nonneg z]
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-Real.log z=
      (fixedPi (j*m) 1 : ℝ)*Real.log queryArg1+(fixedPi (j*m) 2 : ℝ)*Real.log queryArg2-
        (queryDeficit m j : ℝ)*Real.log z := by
    unfold queryEntropy pi1 pi2 TernaryParameters.deficit queryDeficit fixedLength fixedPi
    norm_num
    push_cast
    field_simp
    ring
  have hpos : 0<(1+z)^digitCount Q 1*(1+z+z^2)^digitCount Q 2 / z^(queryDeficit m j) := by positivity
  have hlog : Real.log ((1+z)^digitCount Q 1*(1+z+z^2)^digitCount Q 2 / z^(queryDeficit m j))=
      (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy-Real.log z := by
    rw [Real.log_div (mul_pos (pow_pos h1 _) (pow_pos h2 _)).ne' (pow_pos hz _).ne',
      Real.log_mul (pow_pos h1 _).ne' (pow_pos h2 _).ne',Real.log_pow,Real.log_pow,Real.log_pow,
      hQ 1,hQ 2,←generating_polynomials.2.2,←generating_polynomials.2.1]
    exact he.symm
  calc
    _=Real.exp (Real.log ((1+z)^digitCount Q 1*(1+z+z^2)^digitCount Q 2 / z^(queryDeficit m j))) := (Real.exp_log hpos).symm
    _=envelope m j := by rw [hlog,Real.exp_sub,Real.exp_log hz]; rfl

theorem near_card_bound {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    ((nearWords Q (queryDeficit m j)).card : ℝ)≤envelope m j := by
  have hg := nearWords_card_gibbs_counts Q (queryDeficit m j) z
    gibbs_parameters.2.2.1.le gibbs_parameters.2.2.2.le
  rw [←gibbs_expression Q hQ]
  exact (le_div_iff₀ (pow_pos gibbs_parameters.2.2.1 _)).mpr hg

theorem envelope_one {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) : 1≤envelope m j := by
  have hcard : (1 : ℝ)≤(nearWords Q (queryDeficit m j)).card := by
    exact_mod_cast near_pos Q (queryDeficit m j)
  exact hcard.trans (near_card_bound Q hQ)

theorem prepared_rows_bound {m j : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (LightTernaryPreparedWanted.rows Q (bankCut m j) : ℝ)≤envelope m j := by
  have hD : LightTernaryPreparedWanted.D Q (bankCut m j)≤queryDeficit m j := by
    have := query_boundary hQ
    unfold LightTernaryPreparedWanted.D
    omega
  have hsub : nearWords Q (LightTernaryPreparedWanted.D Q (bankCut m j))⊆nearWords Q (queryDeficit m j) := by
    intro R hR
    rw [mem_nearWords] at hR ⊢
    exact ⟨hR.1,hR.2.trans hD⟩
  have hc := Finset.card_le_card hsub
  unfold LightTernaryPreparedWanted.rows
  rw [TernaryNearBankEnumeration.codes_length_eq_nearWords_card]
  have hcR : ((nearWords Q (LightTernaryPreparedWanted.D Q (bankCut m j))).card : ℝ)≤
      ((nearWords Q (queryDeficit m j)).card : ℝ) := by exact_mod_cast hc
  exact hcR.trans (near_card_bound Q hQ)

theorem actual_query_time_bound {m j L : ℕ} (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) :
    (LightTernaryFrozenQuery.queryTime L (bankCut m j) (fixedLength (j*m)) Q : ℝ)≤
      10000*((fixedLength (j*m) : ℝ)+L+1)*((fixedLength (j*m) : ℝ)+1)*envelope m j := by
  have hg := LightTernaryFrozenQuery.queryTime_gibbs L (bankCut m j) Q z
    gibbs_parameters.2.2.1.le gibbs_parameters.2.2.2.le
  rw [query_boundary hQ] at hg
  have h := (le_div_iff₀ (pow_pos gibbs_parameters.2.2.1 (queryDeficit m j))).mpr hg
  calc
    _≤_ := h
    _=10000*((fixedLength (j*m) : ℝ)+L+1)*((fixedLength (j*m) : ℝ)+1)*envelope m j := by
      rw [←gibbs_expression Q hQ]
      ring

def width (N : ℕ) (f g : Config) : ℕ :=
  N+f.L+g.L+Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)+3

theorem rank_time_bound (N : ℕ) : LightTernaryRank.time N≤2000*(N+1)^2 := by
  unfold LightTernaryRank.time LightTernaryCodes.digitTime LightMaskErase.time
  nlinarith

theorem actual_prepared_time_bound {m j : ℕ} (f g : Config)
    (hT : f.T=bankCut m j) (Q : TritWord (fixedLength (j*m))) (hQ : HasType Q (fixedPi (j*m))) :
    (LightTernaryPreparedWanted.time f g Q : ℝ)≤
      100000*(width (fixedLength (j*m)) f g : ℝ)^3*envelope m j := by
  let N := fixedLength (j*m)
  let r := LightTernaryPreparedWanted.rows Q f.T
  let W := width N f g
  have hW : N+1≤W := by dsimp [W,width]; omega
  have hWpos : 1≤W := by omega
  have hsq : (N+1)^2≤W^3 := by
    calc
      _≤W^2 := Nat.pow_le_pow_left hW 2
      _≤W^3 := Nat.pow_le_pow_right hWpos (by decide)
  have hs := LightTernaryNearSetup.time_bound Q (LightTernaryPreparedWanted.D Q f.T)
  have hp := LightTernaryNearPair.pairTime_bound N r f g
  have hr := rank_time_bound N
  have htime : LightTernaryPreparedWanted.time f g Q≤
      30000*W^3*(r+1)+LightTernaryFrozenQuery.queryTime f.L f.T N Q := by
    have hs' : LightTernaryNearSetup.time Q (LightTernaryPreparedWanted.D Q f.T)≤3000*W^3*(r+1) := by
      exact hs.trans (by change 3000*(N+1)^2*(r+1)≤_; gcongr)
    have hr' : LightTernaryRank.time N≤2000*W^3*(r+1) := by
      apply hr.trans
      have h0 := Nat.mul_le_mul_left 2000 hsq
      have h1 := Nat.le_mul_of_pos_right (2000*W^3) (by omega : 0<r+1)
      exact h0.trans h1
    have hbase : 1≤W^3*(r+1) := Nat.succ_le_of_lt (by positivity)
    unfold LightTernaryPreparedWanted.time LightTernaryWantedQuery.time
    change _≤30000*W^3*(r+1)+_
    change LightTernaryNearPair.pairTime N r f g≤23000*W^3*(r+1) at hp
    nlinarith only [hs',hp,hr',hbase]
  have hrows : (r : ℝ)+1≤2*envelope m j := by
    have h1 := envelope_one Q hQ
    have h2 := prepared_rows_bound Q hQ
    dsimp [r]
    rw [hT]
    linarith
  have hpoly : ((N : ℝ)+f.L+1)*((N : ℝ)+1)≤(W : ℝ)^3 := by
    have hF : N+f.L+1≤W := by dsimp [W,width]; omega
    have hn : (N+f.L+1)*(N+1)≤W^3 :=
      (Nat.mul_le_mul hF hW).trans (by nlinarith [Nat.one_le_pow 3 W hWpos])
    exact_mod_cast hn
  have hq := actual_query_time_bound (L := f.L) Q hQ
  rw [←hT] at hq
  have htR : (LightTernaryPreparedWanted.time f g Q : ℝ)≤
      30000*(W : ℝ)^3*((r : ℝ)+1)+(LightTernaryFrozenQuery.queryTime f.L f.T N Q : ℝ) := by exact_mod_cast htime
  have hq' : (LightTernaryFrozenQuery.queryTime f.L f.T N Q : ℝ)≤10000*(W : ℝ)^3*envelope m j := by
    calc
      _≤10000*((N : ℝ)+f.L+1)*((N : ℝ)+1)*envelope m j := hq
      _≤_ := by
        have hm : 10000*((N : ℝ)+f.L+1)*((N : ℝ)+1)≤10000*(W : ℝ)^3 := by nlinarith only [hpoly]
        exact mul_le_mul_of_nonneg_right hm (envelope_pos m j).le
  have hrow' := mul_le_mul_of_nonneg_left hrows (by positivity : (0 : ℝ)≤30000*(W : ℝ)^3)
  change _≤100000*(W : ℝ)^3*envelope m j
  nlinarith only [htR,hq',hrow',mul_nonneg (by positivity : (0 : ℝ)≤(W : ℝ)^3) (envelope_pos m j).le]


theorem envelope_ge_one (m j : ℕ) : 1≤envelope m j := by
  have hent : 0≤queryEntropy := analytic_admissibility.2.1.le
  have hlog : 0≤Real.log 2 := log_two_pos.le
  have hz := gibbs_parameters.2.2.1
  have hExp : 1≤Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy) :=
    Real.one_le_exp_iff.mpr (by positivity : 0≤(fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy)
  unfold envelope
  apply (le_div_iff₀ hz).mpr
  norm_num
  exact gibbs_parameters.2.2.2.le.trans hExp

/-- This prices the actual full inverse-query envelope, not just near leaves. -/
theorem actual_query_envelope_volume {K m n j : ℕ} (hK : 0<K) (hm : 0<m) (hn : 1<n)
    (hj : j≤radixLength m n) :
    (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*envelope m j≤
      (Real.exp (TernaryOversizeDimensions.querySlope K m)/z)*(n : ℝ)^TernaryOversizeRates.queryCharge K m := by
  have hM : 1<outputSize m := by have := outputSize_ge_sixteen hm; omega
  have hp : 0<(nativePrime K m : ℝ) := by exact_mod_cast (nativePrime_prime K m).pos
  have hR : 0<(partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hS : 0<(inflation K m : ℝ) := by exact_mod_cast inflation_pos hK m
  have hnR : 0<(n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have hz := gibbs_parameters.2.2.1
  have hratio := div_pos hp hR
  have he : (fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy=
      (j : ℝ)*((fixedLength m : ℝ)*Real.log 2*queryEntropy) := by unfold fixedLength; push_cast; ring
  have hX : 0≤((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy) := by positivity
  have hlog : Real.log (((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy))≤
      (j : ℝ)*TernaryOversizeDimensions.querySlope K m := by
    rw [Real.log_mul (mul_pos (pow_pos hratio _) (pow_pos hS _)).ne' (Real.exp_pos _).ne',
      Real.log_mul (pow_pos hratio _).ne' (pow_pos hS _).ne',Real.log_pow,Real.log_pow,
      Real.log_exp,Real.log_div hp.ne' hR.ne',he]
    unfold TernaryOversizeDimensions.querySlope
    push_cast
    nlinarith
  have hb := prefix_dimension_bound hM hn hj (query_slope_nonneg hK hm) hX hlog
  calc
    _=((n : ℝ)/z)*(((nativePrime K m : ℝ)/partitionCap m)^j*(inflation K m : ℝ)^(4*j)*
      Real.exp ((fixedLength (j*m) : ℝ)*Real.log 2*queryEntropy)) := by unfold envelope; ring
    _≤((n : ℝ)/z)*(Real.exp (TernaryOversizeDimensions.querySlope K m)*
      (n : ℝ)^(2*TernaryOversizeDimensions.querySlope K m/Real.log (outputSize m : ℝ))) :=
      mul_le_mul_of_nonneg_left hb (div_pos hnR hz).le
    _=_ := by rw [←TernaryOversizeDimensions.query_charge_eq hm,Real.rpow_add hnR,Real.rpow_one]; ring

private theorem nat_sup_cast_le {α : Type*} (s : Finset α) (f : α→ℕ) (C : ℝ)
    (hC : 0≤C) (h : ∀ a∈s, (f a : ℝ)≤C) : ((s.sup f : ℕ) : ℝ)≤C := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using hC
  | @insert a s ha ih =>
    rw [Finset.sup_insert,Nat.cast_max]
    exact max_le (h a (Finset.mem_insert_self _ _))
      (ih (fun b hb => h b (Finset.mem_insert_of_mem hb)))

/-- Maximum of the actual natural prepared-query time functions. This is an
analysis bound; the machine never reads or computes this maximum. -/
def queryMax (m j : ℕ) (f g : Config) : ℕ :=
  (TernaryCoverLocal.vertices (fixedLength (j*m)) (fixedPi (j*m))).sup
    (fun Q => LightTernaryPreparedWanted.time f g Q)

theorem query_time_le_max {m j : ℕ} (f g : Config) (Q : TritWord (fixedLength (j*m)))
    (hQ : HasType Q (fixedPi (j*m))) : LightTernaryPreparedWanted.time f g Q≤queryMax m j f g := by
  apply Finset.le_sup
  simpa [TernaryCoverLocal.vertices] using hQ

theorem query_max_bound {m j : ℕ} (f g : Config) (hT : f.T=bankCut m j) :
    (queryMax m j f g : ℝ)≤100000*(width (fixedLength (j*m)) f g : ℝ)^3*envelope m j := by
  apply nat_sup_cast_le
  · exact mul_nonneg (by positivity) (envelope_pos m j).le
  · intro Q hQ
    exact actual_prepared_time_bound f g hT Q (by simpa [TernaryCoverLocal.vertices] using hQ)


private theorem one_le_mul_real {a b : ℝ} (ha : 1≤a) (hb : 1≤b) : 1≤a*b := by
  nlinarith [mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr hb)]

/-- Direct bound for the actual frontend natural time, before substituting
native-family dimensions. The added 1000 pays ordinary loop/call overhead. -/
theorem frontend_shape_bound {m j groups count : ℕ} (f g : Config) (hT : f.T=bankCut m j)
    (D X : ℝ) (hD : 1≤D) (hX : 1≤X) (hgroups : (groups : ℝ)≤D) (hcount : (count : ℝ)≤X*D) :
    (LightTernaryCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count (queryMax m j f g)+1000 : ℕ)≤
      1000000*(width (fixedLength (j*m)) f g : ℝ)^3*D*((bankSize m j : ℝ)+X*envelope m j) := by
  let N := fixedLength (j*m)
  let W := (width N f g : ℝ)
  let B := (bankSize m j : ℝ)
  let E := envelope m j
  have hW : 1≤W := by
    have hn : 1≤width N f g := by unfold width; omega
    dsimp [W]
    exact_mod_cast hn
  have hW3 : 1≤W^3 := one_le_pow₀ hW
  have hB : 1≤B := by
    have hn : 1≤bankSize m j := bank_pos N (bankCut m j)
    dsimp [B]
    exact_mod_cast hn
  have hE : 1≤E := envelope_ge_one m j
  have hD0 : 0≤D := by linarith
  have hX0 : 0≤X := by linarith
  have hE0 : 0≤E := by linarith
  have hB0 : 0≤B := by linarith
  have hW0 : 0≤W^3 := by positivity
  have hbase : ((N : ℝ)+1)*((N : ℝ)+f.L+1)≤W^3 := by
    have hN : (N : ℝ)+1≤W := by dsimp [W,width]; push_cast; linarith
    have hL : (N : ℝ)+f.L+1≤W := by dsimp [W,width]; push_cast; linarith
    calc
      _≤W*W := mul_le_mul hN hL (by positivity) (by linarith)
      _=W^2 := by ring
      _≤W^3 := pow_le_pow_right₀ hW (by decide)
  have hgplus : (groups : ℝ)+1≤2*D := by linarith
  have hbplus : B+1≤2*B := by linarith
  have hxd : 1≤X*D := one_le_mul_real hX hD
  have hcplus : (count : ℝ)+1≤2*(X*D) := by linarith
  have ht := query_max_bound f g hT
  change (queryMax m j f g : ℝ)≤100000*W^3*E at ht
  have heunit : 1≤W^3*E := one_le_mul_real hW3 hE
  have htplus : (queryMax m j f g : ℝ)+1000≤101000*W^3*E := by nlinarith only [ht,heunit]
  have hbank : 40000*((groups : ℝ)+1)*((N : ℝ)+1)*((N : ℝ)+f.L+1)*(B+1)≤160000*W^3*D*B := by
    have hprod := mul_le_mul hgplus hbplus (by linarith) (by linarith : 0≤2*D)
    have hprod' : ((groups : ℝ)+1)*(B+1)≤4*D*B := by nlinarith only [hprod]
    have hm := mul_le_mul hbase hprod' (by positivity : 0≤((groups : ℝ)+1)*(B+1)) hW0
    nlinarith only [hm]
  have hquery : ((count : ℝ)+1)*((queryMax m j f g : ℝ)+1000)≤202000*W^3*D*(X*E) := by
    have hm := mul_le_mul hcplus htplus (by positivity) (by positivity : 0≤2*(X*D))
    nlinarith only [hm]
  have htimeN := LightTernaryCountFrontend.time_bound groups N f.L (bankSize m j) count (queryMax m j f g)
  have htime : (LightTernaryCountFrontend.time groups N f.L (bankSize m j) count (queryMax m j f g) : ℝ)≤
      40000*((groups : ℝ)+1)*((N : ℝ)+1)*((N : ℝ)+f.L+1)*(B+1)+
        ((count : ℝ)+1)*((queryMax m j f g : ℝ)+1000) := by dsimp [B]; exact_mod_cast htimeN
  have hunit : 1≤W^3*D*B := one_le_mul_real (one_le_mul_real hW3 hD) hB
  have hqnonneg : 0≤W^3*D*(X*E) := by positivity
  change _≤1000000*W^3*D*(B+X*E)
  push_cast
  nlinarith only [htime,hbank,hquery,hunit,hqnonneg]

def principalExponent (K k c d m : ℕ) : ℝ :=
  max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m)+overheadCharge k c d m

def dimensionConstant (K k c d m : ℕ) : ℝ :=
  1000000*(baseFactor K k c d m : ℝ)*
    (Real.exp (TernaryOversizeDimensions.bankSlope K m)+Real.exp (TernaryOversizeDimensions.querySlope K m)/z)

theorem dimensionConstant_nonneg (K k c d m : ℕ) : 0≤dimensionConstant K k c d m := by
  have hz := gibbs_parameters.2.2.1
  unfold dimensionConstant
  positivity

/-- The literal repeated family/carry/raw-cap factor is inserted into the
actual frontend natural time. This includes the larger field's p/Rbar volume. -/
theorem physical_prefix_bound {K k m n j groups count b : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (hn : 1<n) (hj : j≤radixLength m n)
    (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (f g : Config) (hT : f.T=bankCut m j)
    (hgroups : groups≤(b*(nativeFamily K m k).length*
      TernaryCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^j)
    (hcount : (count : ℝ)≤(n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
      ((b*(nativeFamily K m k).length*
        TernaryCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j) :
    (LightTernaryCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count (queryMax m j f g)+1000 : ℕ)≤
      dimensionConstant K k c d m*(width (fixedLength (j*m)) f g : ℝ)^3*
        (n : ℝ)^principalExponent K k c d m := by
  let S := (inflation K m : ℝ)^(4*j)
  let B := (baseFactor K k c d m : ℝ)^j
  let X := (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j
  have hs : (1 : ℝ)≤ inflation K m := by exact_mod_cast inflation_pos hK m
  have hbpos : (1 : ℝ)≤baseFactor K k c d m := by exact_mod_cast baseFactor_pos K k c d m
  have hS : 1≤S := one_le_pow₀ hs
  have hB : 1≤B := one_le_pow₀ hbpos
  have hR : 0<(partitionCap m : ℝ) := by unfold partitionCap; positivity
  have hpR : (partitionCap m : ℝ)≤nativePrime K m := by exact_mod_cast partition_le_native hK m
  have hratio : 1≤(nativePrime K m : ℝ)/partitionCap m := (one_le_div hR).mpr hpR
  have hX : 1≤X := one_le_mul_real (by exact_mod_cast hn.le) (one_le_pow₀ hratio)
  have hfacN := repeated_native_family_factor_bound K k c d m b j hb
  have hfac : (((b*(nativeFamily K m k).length*
      TernaryCoverCapParameters.rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j)≤S*B := by
    dsimp [S,B]
    exact_mod_cast hfacN
  have hgR : (groups : ℝ)≤S*B := (by exact_mod_cast hgroups : (groups : ℝ)≤_).trans hfac
  have hcR : (count : ℝ)≤X*(S*B) := hcount.trans (mul_le_mul_of_nonneg_left hfac (show 0≤X from by linarith))
  have ht := frontend_shape_bound f g hT (S*B) X (one_le_mul_real hS hB) hX hgR hcR
  have hbVol := TernaryOversizeDimensions.actual_bank_volume hK hm hn hj
  have hqVol := actual_query_envelope_volume hK hm hn hj
  have hvol : S*((bankSize m j : ℝ)+X*envelope m j)≤
      (Real.exp (TernaryOversizeDimensions.bankSlope K m)+Real.exp (TernaryOversizeDimensions.querySlope K m)/z)*
        (n : ℝ)^max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m) := by
    have hnr : (1 : ℝ)≤n := by exact_mod_cast hn.le
    have h1 := Real.rpow_le_rpow_of_exponent_le hnr (le_max_left (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m))
    have h2 := Real.rpow_le_rpow_of_exponent_le hnr (le_max_right (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m))
    have hB' := hbVol.trans (mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le)
    have hQ' := hqVol.trans (mul_le_mul_of_nonneg_left h2 (div_pos (Real.exp_pos _) gibbs_parameters.2.2.1).le)
    dsimp [S,X] at *
    nlinarith only [hB',hQ']
  have hbase := base_factor_prefix_bound hK hk hm hn hj c d
  change B≤(baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m at hbase
  have hmain := mul_le_mul_of_nonneg_left hvol (by positivity : 0≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*B)
  have hbase' := mul_le_mul_of_nonneg_right hbase
    (by have hz := gibbs_parameters.2.2.1; positivity : 0≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*
      (Real.exp (TernaryOversizeDimensions.bankSlope K m)+Real.exp (TernaryOversizeDimensions.querySlope K m)/z)*
      (n : ℝ)^max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m))
  have hnR : 0<(n : ℝ) := by exact_mod_cast lt_trans Nat.zero_lt_one hn
  have heq : (n : ℝ)^overheadCharge k c d m*(n : ℝ)^max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m)=
      (n : ℝ)^principalExponent K k c d m := by rw [←Real.rpow_add hnR]; congr 1; unfold principalExponent; ring
  calc
    _≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*(S*B)*
      ((bankSize m j : ℝ)+X*envelope m j) := ht
    _=1000000*(width (fixedLength (j*m)) f g : ℝ)^3*B*
      (S*((bankSize m j : ℝ)+X*envelope m j)) := by ring
    _≤1000000*(width (fixedLength (j*m)) f g : ℝ)^3*B*
      ((Real.exp (TernaryOversizeDimensions.bankSlope K m)+Real.exp (TernaryOversizeDimensions.querySlope K m)/z)*
        (n : ℝ)^max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m)) := hmain
    _=B*(1000000*(width (fixedLength (j*m)) f g : ℝ)^3*
      (Real.exp (TernaryOversizeDimensions.bankSlope K m)+Real.exp (TernaryOversizeDimensions.querySlope K m)/z)*
        (n : ℝ)^max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m)) := by ring
    _≤_ := hbase'
    _=dimensionConstant K k c d m*(width (fixedLength (j*m)) f g : ℝ)^3*
      (n : ℝ)^principalExponent K k c d m := by
      unfold dimensionConstant
      rw [show (baseFactor K k c d m : ℝ)*(n : ℝ)^overheadCharge k c d m*
        (1000000*(width (fixedLength (j*m)) f g : ℝ)^3*
          (Real.exp (TernaryOversizeDimensions.bankSlope K m)+Real.exp (TernaryOversizeDimensions.querySlope K m)/z)*
          (n : ℝ)^max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m))=
        (1000000*(baseFactor K k c d m : ℝ)*
          (Real.exp (TernaryOversizeDimensions.bankSlope K m)+Real.exp (TernaryOversizeDimensions.querySlope K m)/z)*
          (width (fixedLength (j*m)) f g : ℝ)^3)*
          ((n : ℝ)^overheadCharge k c d m*(n : ℝ)^max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m)) by ring,
        heq]



def prefixTime (m n j : ℕ) (f g : Config) (groups count : ℕ) : ℕ :=
  LightTernaryCountFrontend.time groups (fixedLength (j*m)) f.L (bankSize m j) count (queryMax m j f g)+1000

def allPrefixTime (m : ℕ) (f g : ℕ→ℕ→Config) (groups wanted : ℕ→ℕ→ℕ)
    (channels : ℕ→ℕ) (n : ℕ) : ℕ :=
  channels n*∑ j ∈ Finset.range (radixLength m n+1), prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j)

/-- Word-value logarithms may depend on the original input size, so they are
bounded by the full radix length, uniformly over every prefix. -/
theorem width_bound_from_logs {m n j v : ℕ} (hj : j≤radixLength m n) (f g : Config)
    (hf : f.L≤2*fixedLength (j*m)) (hg : g.L≤2*fixedLength (j*m))
    (hv : Nat.log 2 (f.V+1)+Nat.log 2 (g.V+1)≤v*(radixLength m n+1)) :
    width (fixedLength (j*m)) f g≤(5*fixedLength m+v+3)*(radixLength m n+1) := by
  have hlen : fixedLength (j*m)=j*fixedLength m := by unfold fixedLength; ring
  have hN := Nat.mul_le_mul_right (fixedLength m) hj
  unfold width
  rw [hlen] at hf hg ⊢
  nlinarith only [hf,hg,hv,hN]

/-- Actual time summed over every prefix and every fixed or polynomially many
moment channels. All hypotheses are literal cardinality or word-log bounds. -/
theorem all_prefix_time_bound {K k m b C A degree : ℕ}
    (hK : 0<K) (hk : 0<k) (hm : 0<m) (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (f g : ℕ→ℕ→Config) (groups wanted : ℕ→ℕ→ℕ) (channels : ℕ→ℕ)
    (hT : ∀ n, 1<n → ∀ j≤radixLength m n, (f n j).T=bankCut m j)
    (hgroups : ∀ n, 1<n → ∀ j≤radixLength m n, groups n j≤
      (b*(nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k)^j)
    (hwanted : ∀ n, 1<n → ∀ j≤radixLength m n, (wanted n j : ℝ)≤
      (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
        ((b*(nativeFamily K m k).length*rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) k : ℕ) : ℝ)^j)
    (hwidth : ∀ n, 1<n → ∀ j≤radixLength m n,
      width (fixedLength (j*m)) (f n j) (g n j)≤C*(radixLength m n+1))
    (hchannels : ∀ n, 1<n → channels n≤A*(radixLength m n+1)^degree)
    (n : ℕ) (hn : 1<n) :
    (allPrefixTime m f g groups wanted channels n : ℝ)≤
      ((A : ℝ)*dimensionConstant K k c d m*(C : ℝ)^3)*((radixLength m n : ℝ)+1)^(degree+4)*
        (n : ℝ)^principalExponent K k c d m := by
  let R := ((radixLength m n : ℝ)+1)
  let E := (n : ℝ)^principalExponent K k c d m
  let D := dimensionConstant K k c d m
  have hD : 0≤D := dimensionConstant_nonneg K k c d m
  have hR : 0≤R := by dsimp [R]; positivity
  have hE : 0≤E := by dsimp [E]; positivity
  have hp : ∀ j∈Finset.range (radixLength m n+1),
      (prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j) : ℝ)≤D*(C : ℝ)^3*R^3*E := by
    intro j hj
    have hj' : j≤radixLength m n := by have := Finset.mem_range.mp hj; omega
    have h := physical_prefix_bound hK hk hm hn hj' c d hb (f n j) (g n j)
      (hT n hn j hj') (hgroups n hn j hj') (hwanted n hn j hj')
    have hw : (width (fixedLength (j*m)) (f n j) (g n j) : ℝ)≤(C : ℝ)*R := by
      dsimp [R]
      exact_mod_cast hwidth n hn j hj'
    have hw3 := pow_le_pow_left₀ (by positivity : (0 : ℝ)≤width (fixedLength (j*m)) (f n j) (g n j)) hw 3
    have hmul := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hw3 hD) hE
    change _≤D*(C : ℝ)^3*R^3*E
    dsimp [D,E] at hmul
    exact h.trans (by simpa only [mul_pow,mul_assoc] using hmul)
  have hsum : ((∑ j ∈ Finset.range (radixLength m n+1),
      prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j) : ℕ) : ℝ)≤D*(C : ℝ)^3*R^4*E := by
    rw [Nat.cast_sum]
    have h := Finset.sum_le_sum hp
    have he : (∑ _j ∈ Finset.range (radixLength m n+1), D*(C : ℝ)^3*R^3*E)=D*(C : ℝ)^3*R^4*E := by
      simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul]
      dsimp [R]
      push_cast
      ring
    exact h.trans_eq he
  have hchan : (channels n : ℝ)≤(A : ℝ)*R^degree := by dsimp [R]; exact_mod_cast hchannels n hn
  have htotal := mul_le_mul hchan hsum (by positivity : (0 : ℝ)≤
    ((∑ j ∈ Finset.range (radixLength m n+1), prefixTime m n j (f n j) (g n j) (groups n j) (wanted n j) : ℕ) : ℝ))
      (by positivity : (0 : ℝ)≤(A : ℝ)*R^degree)
  unfold allPrefixTime
  rw [Nat.cast_mul]
  change _≤((A : ℝ)*D*(C : ℝ)^3)*R^(degree+4)*E
  exact htotal.trans_eq (by rw [pow_add]; ring)

def frontendExponent : ℝ :=19207/10000

theorem frontend_margin : targetExponent-frontendExponent=(3/10000 : ℝ) := by
  norm_num [targetExponent,frontendExponent]

theorem principal_exponent_lt {K m : ℕ} (hK : 100000000≤K) (c d : ℕ)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K) :
    principalExponent K (selectedMoment K) c d m<frontendExponent := by
  have hmax : max (TernaryOversizeRates.bankCharge K m) (TernaryOversizeRates.queryCharge K m)<softCertificate :=
    max_lt hgood.2.1 hgood.2.2.1
  have hkr : (100000000 : ℝ)≤K := by exact_mod_cast hK
  have hkp : (0 : ℝ)<K := by linarith
  have hmicro : microAllowance K<(1/10000 : ℝ) := by
    unfold microAllowance
    apply (div_lt_iff₀ (by positivity)).mpr
    nlinarith
  have hsum := add_lt_add hmax hover
  have hbound : softCertificate+microAllowance K<frontendExponent := by
    norm_num [softCertificate,frontendExponent]
    linarith
  exact hsum.trans hbound

/-- Uniform, genuine all-prefix natural time bound for the physical frontend,
including polynomial channel overhead, strictly below the requested 1.921. -/
theorem all_prefix_eventually {K m b C A degree : ℕ}
    (hK : 100000000≤K) (c d : ℕ) (hb : b≤c*(fixedLength m+1)^d)
    (hgood : GoodBlock K m)
    (hover : overheadCharge (selectedMoment K) c d m<microAllowance K)
    (f g : ℕ→ℕ→Config) (groups wanted : ℕ→ℕ→ℕ) (channels : ℕ→ℕ)
    (hT : ∀ n, 1<n → ∀ j≤radixLength m n, (f n j).T=bankCut m j)
    (hgroups : ∀ n, 1<n → ∀ j≤radixLength m n, groups n j≤
      (b*(nativeFamily K m (selectedMoment K)).length*
        rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) (selectedMoment K))^j)
    (hwanted : ∀ n, 1<n → ∀ j≤radixLength m n, (wanted n j : ℝ)≤
      (n : ℝ)*((nativePrime K m : ℝ)/partitionCap m)^j*
        ((b*(nativeFamily K m (selectedMoment K)).length*
          rawThreshold (nativePrime K m) (sourceCap m (nativePrime K m)) (selectedMoment K) : ℕ) : ℝ)^j)
    (hwidth : ∀ n, 1<n → ∀ j≤radixLength m n,
      width (fixedLength (j*m)) (f n j) (g n j)≤C*(radixLength m n+1))
    (hchannels : ∀ n, 1<n → channels n≤A*(radixLength m n+1)^degree) :
    ∀ᶠ n : ℕ in atTop, (allPrefixTime m f g groups wanted channels n : ℝ)≤(n : ℝ)^frontendExponent := by
  have hk : 0<K := by omega
  have hdim := dimensionConstant_nonneg K (selectedMoment K) c d m
  have hA : 0≤(A : ℝ)*dimensionConstant K (selectedMoment K) c d m*(C : ℝ)^3 := by positivity
  have he := principal_exponent_lt hK c d hgood hover
  have habsorb := TernaryRadixOverhead.polynomial_dimension_budget hgood.1
    ((A : ℝ)*dimensionConstant K (selectedMoment K) c d m*(C : ℝ)^3) 1
    (principalExponent K (selectedMoment K) c d m) frontendExponent hA (by norm_num) he (degree+4)
    (fun n => (n : ℝ)^principalExponent K (selectedMoment K) c d m) (by intro n hn; simp)
  filter_upwards [habsorb,eventually_gt_atTop (1 : ℕ)] with n hn hn'
  exact (all_prefix_time_bound hk (selectedMoment_pos hk) hgood.1 c d hb f g groups wanted channels
    hT hgroups hwanted hwidth hchannels n hn').trans hn

/-- The same fixed block satisfies the actual cardinality rates and the
small repeated-family overhead required above. -/
theorem exists_fixed_block {K : ℕ} (hK : 100000000≤K) (c d minimum : ℕ) :
    ∃ m, minimum≤m ∧ GoodBlock K m ∧
      overheadCharge (selectedMoment K) c d m<microAllowance K ∧
      principalExponent K (selectedMoment K) c d m<frontendExponent := by
  obtain ⟨m,hm,hgood,hover⟩ := common_fixed_block hK c d minimum
  exact ⟨m,hm,hgood,hover,principal_exponent_lt hK c d hgood hover⟩


/-- Group dispatch changes only source-bank pointers; it leaves the actual
prepared-query running-time function unchanged. -/
@[simp] theorem prepared_time_sourceConfig {N : ℕ} (f g : Config) (Q : TritWord N)
    (fbase gbase stride tail group : ℕ) :
    LightTernaryPreparedWanted.time
      (LightTernaryWantedRowDispatch.sourceConfig f fbase stride tail group)
      (LightTernaryWantedRowDispatch.sourceConfig g gbase stride tail group) Q=
      LightTernaryPreparedWanted.time f g Q := rfl

/-- Directly discharges CountFrontend.meets' per-literal-row time premise. -/
theorem literal_query_time_le_max {m j : ℕ} (f g : Config)
    (Q : TritWord (fixedLength (j*m))) (hQ : HasType Q (fixedPi (j*m)))
    (fbase gbase stride tail group : ℕ) :
    LightTernaryPreparedWanted.time
      (LightTernaryWantedRowDispatch.sourceConfig f fbase stride tail group)
      (LightTernaryWantedRowDispatch.sourceConfig g gbase stride tail group) Q≤queryMax m j f g := by
  simpa only [prepared_time_sourceConfig] using query_time_le_max f g Q hQ

end ThreeSum.TernaryCountFrontendBudget
