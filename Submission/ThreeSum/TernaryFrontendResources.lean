import Submission.ThreeSum.LightTernaryCountFrontend
import Submission.ThreeSum.PolynomialResources
import Submission.ThreeSum.ArithmeticStageBounds
import Submission.ThreeSum.TernaryRadixOverhead

/-! Concrete workspace and word limits for the physical ternary count frontend.
The workspace is translated by the caller's arbitrary free pointer. No word
bound depends on that pointer: each address is bounded separately by space. -/
noncomputable section
namespace ThreeSum.TernaryFrontendResources
open Light ThreeSum.TernaryJointType ThreeSum.TernaryBank ThreeSum.TernaryEuler
open ThreeSum.LightTernaryNearPair ThreeSum.LightTernaryQueryPlan
open ThreeSum.TernaryBankStageModel ThreeSum.LightTernaryPreparedWanted
open Filter StageBounds ThreeSum.TernaryCodeSemantics
open scoped Topology
set_option maxHeartbeats 6000000
set_option maxRecDepth 18000

def sourceZeta (N A : ℕ) : ℕ := 4^N*A
def eulerBound (N A : ℕ) : ℕ := 2*(N+1)*sourceZeta N A
def caps (a R : ℕ) : ℕ := a+R
def active (a N R : ℕ) : ℕ := caps a R+N
def powers (a N R : ℕ) : ℕ := active a N R+N
def fws (a N R : ℕ) : ℕ := powers a N R+(2*N+1)
def ranks (ws N R : ℕ) : ℕ := ws+2*N*R+N
def vals (ws N R : ℕ) : ℕ := ranks ws N R+R
def division (ws N R : ℕ) : ℕ := vals ws N R+R
def gws (a N R A : ℕ) : ℕ := division (fws a N R) N R+eulerBound N A+3
def out (a N R A : ℕ) : ℕ := division (gws a N R A) N R+eulerBound N A+3
def heapEnd (a N R A : ℕ) : ℕ := out a N R A+R

def config (a N R A bank nb bv T h ws : ℕ) : Config where
  a:= a; powers:= powers a N R; bank:= bank; nb:= nb; bv:= bv; L:= 2*N; T:= T
  activeBase:= active a N R; ws:= ws; rankBase:= ranks ws N R; vals:= vals ws N R
  h:= h; pcount:= division ws N R; fr:= division ws N R
  U:= sourceZeta N A; V:= eulerBound N A

def word (N nb groups count R A : ℕ) : ℕ :=
  100*(N+nb+groups+count+R+(N+1)*nb+2^(2*N+1)+4^(N+1)+sourceZeta N A+
    eulerBound N A+(sourceZeta N A)^2+4^N*(sourceZeta N A)^2+100)

/-- `priorCells` is the already proved size of the preceding host and bank layout. -/
def need (N nb groups count R A priorCells hostWord : ℕ) : Light.Need :=
  ⟨hostWord+word N nb groups count R A, heapEnd priorCells N R A,5*N+16⟩

@[simp] theorem sourceConfig_config (a N R A bank nb bv T h ws base stride tail group : ℕ) :
    LightTernaryWantedRowDispatch.sourceConfig (config a N R A bank nb bv T h ws)
      base stride tail group=
    config a N R A bank nb (base+group*stride+tail) T h ws := rfl

theorem heapEnd_eq (a N R A : ℕ) :
    heapEnd a N R A=a+(4*N+6)*R+6*N+2*eulerBound N A+7 := by
  unfold heapEnd out gws division vals ranks fws powers active caps
  ring

theorem heapEnd_translate (a b N R A : ℕ) :
    heapEnd (a+b) N R A=a+heapEnd b N R A := by
  simp only [heapEnd_eq]; omega

theorem controls (N nb groups count R A : ℕ) :
    nb+R+2^(2*N+1)+2*N+32≤ word N nb groups count R A ∧
    4*N+R+32≤ word N nb groups count R A ∧
    4*eulerBound N A+8*N+16≤ word N nb groups count R A ∧
    4^(N+1)≤ word N nb groups count R A ∧
    4*sourceZeta N A+3≤ word N nb groups count R A ∧
    (sourceZeta N A)^2≤ word N nb groups count R A ∧
    4*4^N*(sourceZeta N A)^2+3≤ word N nb groups count R A ∧
    groups+1≤ word N nb groups count R A ∧
    count+1≤ word N nb groups count R A := by
  simp only [word,pow_succ]
  generalize 4^N=q
  generalize 2^(2*N)=p
  generalize sourceZeta N A=z
  generalize eulerBound N A=v
  ring_nf
  omega

theorem bank_controls (N nb groups count R A : ℕ) :
    nb+2^(2*N+1)+16≤word N nb groups count R A ∧
    2*N+3≤word N nb groups count R A ∧
    (N+1)*nb≤word N nb groups count R A ∧
    N*nb≤word N nb groups count R A ∧
    4*(4^N*A)+3≤word N nb groups count R A ∧
    LightTernaryBankAssembly.valueBound N A≤word N nb groups count R A ∧
    4*(4^N*LightTernaryBankAssembly.valueBound N A)+3≤word N nb groups count R A := by
  simp only [word,LightTernaryBankAssembly.valueBound,sourceZeta]
  ring_nf
  omega

theorem zeta_abs {N A : ℕ} (F : TritWord N→ ℤ)
    (hF : ∀ R, |F R|≤ (A:ℤ)) (R : TritWord N) :
    |binomialZeta F R|≤ (sourceZeta N A:ℤ) := by
  have h:= forwardStage_abs N le_rfl F A hF R
  rw [forwardStage_full] at h
  simpa [sourceZeta] using h

/-- The two metadata matrices, memo values, and division scratch have a
literal layout. The division reserve uses `V+3`, a conservative polynomial
upper bound on the actual logarithmic table length. -/
theorem resources {lim : Limits} {a N R A bank nb bv T h ws rows groups count : ℕ}
    (hrows : rows≤ R) (hT : T≤ 2*N) (hh : h≤ T)
    (hnb : nb< 2^(2*N)) (hnn : rows< 2^(2*N)) (hpos : 0< nb)
    (hbank : bank+nb≤ a) (hbv : bv+nb≤ a)
    (hstart : powers a N R+(2*N+1)≤ ws)
    (hend : division ws N R+eulerBound N A+3≤ lim.space)
    (hw : (lim.space:ℤ)≤ lim.word)
    (hword : (word N nb groups count R A:ℤ)≤ lim.word)
    (F : TritWord N→ ℤ) (hhom : ∀ W, F W≠ 0→ rank W=h)
    (hF : ∀ W, |F W|≤ (A:ℤ)) :
    Resources lim rows (config a N R A bank nb bv T h ws) F := by
  obtain ⟨hc,hc',hd,_,_,_,_,_,_⟩:= controls N nb groups count R A
  have hmul : 2*N*rows≤ 2*N*R:= Nat.mul_le_mul_left _ hrows
  have hlog : Nat.log 2 (eulerBound N A+1)≤ eulerBound N A+1:= Nat.log_le_self _ _
  have hcZ : ((nb+rows+2^(2*N+1)+2*N+32:ℕ):ℤ)≤ lim.word:=
    (Int.ofNat_le.mpr (by omega)).trans hword
  have hcZ' : ((4*N+rows+32:ℕ):ℤ)≤ lim.word:=
    (Int.ofNat_le.mpr (by omega)).trans hword
  have hdZ : ((4*eulerBound N A+8*N+16:ℕ):ℤ)≤ lim.word:=
    (Int.ofNat_le.mpr hd).trans hword
  refine {
    homogeneous := hhom
    division := ?_
    hw := hw
    ha := ?_
    hb := ?_
    hp := hstart
    hactiveSpace := ?_
    hbankVals := ?_
    hmetadataRanks := ?_
    hrankVals := ?_
    hvals := ?_
    hfr := ?_
    hcount := ?_
    hspace := ?_
    hword := hcZ
    hcontrols := ?_
    hmemoWord := ?_
    hL := le_rfl
    hnb := hnb
    hnn := hnn
    hnbpos := hpos
    hT := hT
    hh := hh
    hvalue := zeta_abs F hF
    hV := le_rfl }
  · intro current hl hu
    refine ⟨by dsimp [config] at *; omega,hw,?_,?_⟩
    · dsimp [config]
      have hs : current-h≤ 2*N:= by omega
      have hsZ : ((current-h:ℕ):ℤ)≤ 2*(N:ℤ) := by exact_mod_cast hs
      push_cast at hdZ ⊢
      omega
    · dsimp [config]; omega
  all_goals dsimp [config,division,vals,ranks,powers,active,caps] at *
  all_goals omega

theorem need_space {lim : Limits} {free d N nb groups count R A priorCells hostWord : ℕ}
    (H : (need N nb groups count R A priorCells hostWord).Ok lim free d) :
    heapEnd (free+priorCells) N R A≤ lim.space ∧
    (word N nb groups count R A:ℤ)≤ lim.word ∧ d+5*N+16≤ lim.depth := by
  refine ⟨?_,?_,?_⟩
  · rw [heapEnd_translate]; exact H.cells
  · exact (Int.ofNat_le.mpr (Nat.le_add_left _ _)).trans H.word
  · exact H.depth

/-- A complete scalar plan for the actual prepared query, instantiated from
one canonical layout and elementary bounds on the source histograms. -/
theorem plan {lim : Limits} {a N R A bank nb fbv gbv T fh gh bankValues groups count : ℕ}
    (Q : TritWord N) (E : Enumeration N T nb) (F G : TritWord N→ ℤ)
    (hrows : rows Q T≤ R) (hT : T≤ 2*N) (hfh : fh≤ T) (hgh : gh≤ T)
    (hnb : nb< 2^(2*N)) (hnn : rows Q T< 2^(2*N)) (hpos : 0< nb)
    (hbank : bank+nb≤ a) (hfbv : fbv+nb≤ a) (hgbv : gbv+nb≤ a)
    (hH : bankValues+(N+1)*nb≤ a)
    (hend : heapEnd a N R A≤ lim.space) (hw : (lim.space:ℤ)≤ lim.word)
    (hword : (word N nb groups count R A:ℤ)≤ lim.word)
    (hFhom : ∀ W, F W≠ 0→ rank W=fh) (hGhom : ∀ W, G W≠ 0→ rank W=gh)
    (hF : ∀ W, |F W|≤ (A:ℤ)) (hG : ∀ W, |G W|≤ (A:ℤ))
    (houtside : T< rank Q)
    (hsorted : ∀ j k, j< k→ k< nb→ address (E.word j)< address (E.word k)) :
    LightTernaryPreparedState.Plan lim (out a N R A) bankValues (caps a R)
      (config a N R A bank nb fbv T fh (fws a N R))
      (config a N R A bank nb gbv T gh (gws a N R A)) Q E F G := by
  have hfend : division (fws a N R) N R+eulerBound N A+3≤ lim.space := by
    dsimp [heapEnd,out,gws,division,vals,ranks] at hend ⊢; omega
  have hgend : division (gws a N R A) N R+eulerBound N A+3≤ lim.space := by
    unfold heapEnd out at hend; omega
  have hgstart : powers a N R+(2*N+1)≤ gws a N R A := by
    unfold gws division vals ranks fws; omega
  have hrf:= resources hrows hT hfh hnb hnn hpos hbank hfbv le_rfl hfend hw hword F hFhom hF
  have hrg:= resources hrows hT hgh hnb hnn hpos hbank hgbv hgstart hgend hw hword G hGhom hG
  obtain ⟨_,_,_,hsetup,_,hprod,hquery,_,_⟩:= controls N nb groups count R A
  refine {
    fResources:= hrf
    gResources:= hrg
    outside:= houtside
    ga:= rfl
    gp:= rfl
    gactive:= rfl
    gbank:= rfl
    gnb:= rfl
    gT:= rfl
    bankSorted:= hsorted
    bankBefore:= hbank
    Fbefore:= hfbv
    Gbefore:= hgbv
    Hbefore:= hH
    dst:= by dsimp [config,caps]; omega
    caps:= le_rfl
    active:= le_rfl
    setupWord:= (Int.ofNat_le.mpr hsetup).trans hword
    GRead:= ?_
    FbeforeG:= ?_
    Fout:= ?_
    Gout:= ?_
    outSpace:= by dsimp [config]; unfold heapEnd at hend; omega
    outKeep:= ?_
    productWord:= ?_
    queryWord:= ?_ }
  · dsimp [ReadBefore,config,powers,active,caps,fws]
    exact ⟨by omega,by omega,le_rfl,by omega,by omega⟩
  all_goals try { dsimp [config,out,gws,division,vals,ranks,fws,powers,active,caps]; omega }
  · dsimp [config]
    simpa [pow_two] using (Int.ofNat_le.mpr hprod).trans hword
  · dsimp [config]
    have hh:= (Int.ofNat_le.mpr hquery).trans hword
    simpa [pow_two,Nat.cast_mul,mul_assoc] using hh

def envelope (B : ℕ) : ℕ := 20000*(B+1)^6

theorem rows_le_full {N : ℕ} (Q : TritWord N) (T : ℕ) : rows Q T≤3^N := by
  unfold rows
  rw [TernaryNearBankEnumeration.codes_length_eq_nearWords_card]
  exact (Finset.card_le_univ _).trans_eq (by simp [TritWord,Fintype.card_fun])

theorem rows_lt_mask {N : ℕ} (hN : 0<N) (Q : TritWord N) (T : ℕ) :
    rows Q T<2^(2*N) := by
  have hpow : (3:ℕ)^N<4^N := Nat.pow_lt_pow_left (by decide) (by omega)
  have he : 2^(2*N)=4^N := by rw [pow_mul]; norm_num
  rw [he]
  exact (rows_le_full Q T).trans_lt hpow

/-- An explicit polynomial in the literal dimensions and source magnitudes.
It bounds the actual workspace, all scalar words, and recursive depth. -/
theorem need_bound {N nb groups count R A priorCells hostWord B : ℕ}
    (hN : N≤ B) (hnb : nb≤ B) (hgroups : groups≤ B) (hcount : count≤ B)
    (hR : R≤ B) (hA : A≤ B) (hprior : priorCells≤ B) (hhost : hostWord≤ B)
    (hfour : 4^N≤ B) :
    (need N nb groups count R A priorCells hostWord).word≤ envelope B ∧
    (need N nb groups count R A priorCells hostWord).cells≤ envelope B ∧
    (need N nb groups count R A priorCells hostWord).depth≤ envelope B := by
  let C:= B+1
  have hC : 1≤ C := by dsimp [C]; omega
  have hNC : N+1≤ C := by dsimp [C]; omega
  have h4C : 4^N≤ C := by dsimp [C]; omega
  have hAC : A≤ C := by dsimp [C]; omega
  have h1 : 1≤ C^6 := Nat.one_le_pow _ _ hC
  have hp (k : ℕ) (hk : k≤ 6) : C^k≤ C^6 := Nat.pow_le_pow_right hC hk
  have hCC : C≤ C^6 := by simpa using hp 1 (by decide)
  have hZ : sourceZeta N A≤ C^2 := by
    unfold sourceZeta
    simpa [pow_two] using Nat.mul_le_mul h4C hAC
  have hV : eulerBound N A≤ 2*C^3 := by
    unfold eulerBound
    calc
      _≤ 2*C*C^2 := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hNC) hZ
      _=_ := by ring
  have hZZ : (sourceZeta N A)^2≤ C^4 := by
    simpa [←pow_mul] using Nat.pow_le_pow_left hZ 2
  have hH : 4^N*(sourceZeta N A)^2≤ C^5 := by
    calc
      _≤ C*C^4 := Nat.mul_le_mul h4C hZZ
      _=_ := by ring
  have hpow2 : 2^(2*N+1)≤ 2*C := by
    rw [pow_succ,show 2^(2*N)=4^N by rw [pow_mul]; norm_num]
    simpa [mul_comm] using Nat.mul_le_mul_right 2 h4C
  have hpow4 : 4^(N+1)≤ 4*C := by
    simpa [pow_succ,mul_comm] using Nat.mul_le_mul_left 4 h4C
  have hprod : N*R≤ C^2 := by
    have hNC' : N≤ C := by omega
    have hRC : R≤ C := by dsimp [C]; omega
    simpa [pow_two] using Nat.mul_le_mul hNC' hRC
  have hs : N≤ C^6 ∧ nb≤ C^6 ∧ groups≤ C^6 ∧ count≤ C^6 ∧ R≤ C^6 ∧
      priorCells≤ C^6 ∧ hostWord≤ C^6 := by dsimp [C] at *; omega
  obtain ⟨hn,hn',hg,hc,hr,hp',hh⟩:= hs
  have hz6:= hZ.trans (hp 2 (by decide))
  have hv6:= hV.trans (Nat.mul_le_mul_left 2 (hp 3 (by decide)))
  have hzz6:= hZZ.trans (hp 4 (by decide))
  have hh6:= hH.trans (hp 5 (by decide))
  have hp26:= hpow2.trans (Nat.mul_le_mul_left 2 hCC)
  have hp46:= hpow4.trans (Nat.mul_le_mul_left 4 hCC)
  have hnR6:= hprod.trans (hp 2 (by decide))
  have hstride : (N+1)*nb≤ C^2 := by
    have hb : nb≤ C := by dsimp [C]; omega
    simpa [pow_two] using Nat.mul_le_mul hNC hb
  have hstride6:= hstride.trans (hp 2 (by decide))
  refine ⟨?_,?_,?_⟩
  · change hostWord+word N nb groups count R A≤ 20000*C^6
    unfold word
    omega
  · change heapEnd priorCells N R A≤ 20000*C^6
    rw [heapEnd_eq]
    nlinarith only [h1,hn,hr,hp',hv6,hnR6]
  · change 5*N+16≤ 20000*C^6
    omega

/-- Fixed-degree moment channels may make source magnitudes large, but only
polynomially in the original input magnitude. This is the compiler's actual
two-parameter polynomial-resource predicate. -/
theorem polyNeed {N nb groups count R : ℕ→ ℕ} {A priorCells hostWord : ℕ→ ℕ→ ℕ}
    {B : ℕ→ ℕ} {a : ℝ} (hB : PowerBound B a) (H : ℕ)
    (hN : ∀ n, N n≤ B n) (hnb : ∀ n, nb n≤ B n)
    (hgroups : ∀ n, groups n≤ B n) (hcount : ∀ n, count n≤ B n)
    (hR : ∀ n, R n≤ B n) (hfour : ∀ n, 4^(N n)≤ B n)
    (hA : ∀ n U, A n U≤ B n*(U+1)^H)
    (hprior : ∀ n U, priorCells n U≤ B n*(U+1)^H)
    (hhost : ∀ n U, hostWord n U≤ B n*(U+1)^H) :
    Light.PolyNeed (fun n U=>need (N n) (nb n) (groups n) (count n) (R n)
      (A n U) (priorCells n U) (hostWord n U)) := by
  let D:= fun n=>B n+1
  have hD : PowerBound D (max a 0) :=
    (hB.mono_exponent (le_max_left _ _)).add_same
      ((PowerBound.const 1).mono_exponent (le_max_right _ _))
  have he : PowerBound (fun n=>20000*(D n)^6) (0+6*max a 0) :=
    (PowerBound.const 20000).mul (hD.pow 6)
  apply PolynomialResources.polyNeed_of_envelope he (6*H)
  all_goals
    intro n U
    let M:= (U+1)^H
    have hM : 1≤ M := Nat.one_le_pow _ _ (by omega)
    have hBM : B n≤ B n*M := Nat.le_mul_of_pos_right _ hM
    have hh:= need_bound ((hN n).trans hBM) ((hnb n).trans hBM)
      ((hgroups n).trans hBM) ((hcount n).trans hBM) ((hR n).trans hBM)
      (hA n U) (hprior n U) (hhost n U) ((hfour n).trans hBM)
    have hplus : B n*M+1≤ D n*M := by dsimp [D]; nlinarith
    have hpow:= Nat.pow_le_pow_left hplus 6
    have hb : envelope (B n*M)≤ 20000*(D n)^6*(U+1)^(6*H) := by
      unfold envelope
      calc
        _≤ 20000*(D n*M)^6 := Nat.mul_le_mul_left _ hpow
        _=_ := by simp [M,mul_pow,←pow_mul]; ring
    first
    | exact hh.1.trans hb
    | exact hh.2.1.trans hb
    | exact hh.2.2.trans hb

open ThreeSum.TernaryCoverScale ThreeSum.TernaryPrincipalDimensions

/-- Every fixed native alphabet, occurrence-map family, carry alphabet, or
bit-mask base raised to the actual number of prefixes is polynomial. -/
theorem fixed_radix_powerBound {m : ℕ} (hm : 0< m) (b : ℕ) :
    PowerBound (fun n=>(b+1)^radixLength m n)
      (2*Real.log (b+1:ℕ)/Real.log (outputSize m:ℝ)) := by
  intro δ hδ
  have hM : 1< outputSize m := by have := outputSize_ge_sixteen hm; omega
  have ha : 0≤ Real.log (b+1:ℕ) := Real.log_nonneg (by exact_mod_cast (Nat.le_add_left 1 b))
  have hp : 0< (b+1:ℝ) := by positivity
  let e:= 2*Real.log (b+1:ℕ)/Real.log (outputSize m:ℝ)
  have hb (n : ℕ) (hn : 1< n) :
      (((b+1)^radixLength m n:ℕ):ℝ)≤ (b+1:ℝ)*(n:ℝ)^e := by
    have he:= prefix_dimension_bound hM hn (le_rfl : radixLength m n≤ _)
      ha (Nat.cast_nonneg ((b+1)^radixLength m n))
      (by rw [Nat.cast_pow,Real.log_pow])
    simpa only [e,Nat.cast_add,Nat.cast_one,Real.exp_log hp] using he
  have hh:= TernaryRadixOverhead.polynomial_dimension_budget hm 1 (b+1) e (e+δ)
    (by norm_num) hp.le (by linarith) 0
    (fun n=>(((b+1)^radixLength m n:ℕ):ℝ)) hb
  simpa only [pow_zero,mul_one,one_mul] using hh

theorem radix_length_powerBound {m : ℕ} (hm : 0< m) :
    PowerBound (radixLength m) 0 := by
  intro δ hδ
  have hh:= TernaryRadixOverhead.polynomial_radix_budget hm 1 (by norm_num) 1 hδ
  filter_upwards [hh] with n hn
  norm_num at hn ⊢
  linarith

theorem fixed_dimension_powerBound {m : ℕ} (hm : 0< m) :
    PowerBound (fun n=>TernaryLocalParameters.fixedLength (radixLength m n*m)) 0 := by
  have hh:= (PowerBound.const (TernaryLocalParameters.fixedLength m)).mul (radix_length_powerBound hm)
  convert hh using 1
  · funext n; unfold TernaryLocalParameters.fixedLength; ring
  · norm_num

theorem full_mask_powerBound {m : ℕ} (hm : 0< m) :
    PowerBound (fun n=>4^TernaryLocalParameters.fixedLength (radixLength m n*m))
      (2*Real.log (4^TernaryLocalParameters.fixedLength m:ℕ)/Real.log (outputSize m:ℝ)) := by
  have hpos : 0< 4^TernaryLocalParameters.fixedLength m := by positivity
  have hh:= fixed_radix_powerBound hm (4^TernaryLocalParameters.fixedLength m-1)
  have hbase : 4^TernaryLocalParameters.fixedLength m-1+1=4^TernaryLocalParameters.fixedLength m := by omega
  rw [hbase] at hh
  convert hh using 1
  funext n
  rw [←pow_mul]
  congr 1
  unfold TernaryLocalParameters.fixedLength
  ring

end ThreeSum.TernaryFrontendResources
