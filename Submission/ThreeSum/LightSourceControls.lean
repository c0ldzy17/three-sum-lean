import Submission.ThreeSum.LightSourceControlsSpan
import Submission.ThreeSum.LightDownsetSize

/-!
# Actual occurrence count, compact capacity, and exact bank stride

Only the block dimensions and previously constructed local schedule controls
are supplied. Scalar powering, the compact downset-size program, two actual
logarithms, and exact span arithmetic construct all three source controls.
-/

namespace ThreeSum.LightSourceControls

open Light GlobalEncoding LocalCoverBounds BlockSourceEncoding SubsetAddress

set_option maxHeartbeats 3500000
set_option maxRecDepth 16000

def spanWord (h J cut : ℕ) : ℕ :=
  SourceControlLayout.word J (J*(512*h)) (downsetCap (J*(512*h)) cut)
    (LightBlockSourceCatalog.count h J) (Nat.log 2 ((512*h)*localPrime h+1))
    (Nat.log 2 (LightBlockSourceBuild.endpointBound h J+1))

def word (h J cut : ℕ) : ℕ :=
  spanWord h J cut+(J*(512*h)+1)*2^(J*(512*h)+1)+(scheduleSize h+1)^(J+1)+
    2*((512*h)*localPrime h+1)+2*(LightBlockSourceBuild.endpointBound h J+1)+
    modulus h J*localPrime h+J+512*h+localPrime h+cut+scheduleSize h+modulus h J+J*(512*h)+50

def space (work h J : ℕ) : ℕ := work+LightPascal.tableSize (J*(512*h))+(J*(512*h)+1)

def time (h J : ℕ) : ℕ :=
  LightNatPower.time J+LightDownsetSize.time (J*(512*h))+
    log2Time ((512*h)*localPrime h+1)+log2Time (LightBlockSourceBuild.endpointBound h J+1)+2000

/-- J, local width, local prime, cutoff, schedule size, original local
prime power, three-cell destination, and polynomial scratch. -/
def body (pPower pDownset pLog pSpan : ℕ) : Stmt :=
  .call pPower [v 4,v 0] 8 ;;
  .set 9 (v 0 *' v 1) ;;
  .call pDownset [v 9,v 3,v 7] 10 ;;
  .call pLog [v 1 *' v 2 +' k 1] 11 ;;
  .call pLog [v 9 *' (v 5 *' v 2) +' k 1] 12 ;;
  .call pSpan [v 0,v 9,v 10,v 8,v 11,v 12] 13 ;;
  .store (v 6) (v 10) ;;
  .store (v 6 +' k 1) (v 8) ;;
  .store (v 6 +' k 2) (v 13) ;;
  .set 0 (v 13)

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pDownset : ℕ
  pLog : ℕ
  pSpan : ℕ
  pMax : ℕ
  pSetup : ℕ
  pBuild : ℕ
  pFill : ℕ
  pRow : ℕ
  pLinear : ℕ
  pPowers : ℕ
  pRank : ℕ
  pOffset : ℕ
  power : P[pPower]?=some LightNatPower.body
  downset : P[pDownset]?=some (LightDownsetSize.body pSetup pOffset)
  setup : LightSubsetSetup.Procs P pSetup pBuild pFill pRow pLinear pPowers pRank
  offset : P[pOffset]?=some LightSubsetOffset.body
  log : P[pLog]?=some log2Body
  span : P[pSpan]?=some (LightSourceControlsSpan.body pMax)
  maximum : P[pMax]?=some LightSourceControlsMax.body
  main : P[pMain]?=some (body pPower pDownset pLog pSpan)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (C : Procs P pMain)
    {μ : ℕ → ℤ} {h J cut dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+J*(512*h)+5 ≤ lim.depth)
    (hcut : cut ≤ J*(512*h)) (hdst : dst+3 ≤ work)
    (hspace : space work h J ≤ lim.space) (hword : (word h J cut : ℤ) ≤ lim.word) :
    Meets lim P pMain d [J,512*h,localPrime h,cut,scheduleSize h,modulus h J,dst,work]
      μ (time h J) (fun r ν => r=(SourceBandBankLayout.span h J cut : ℤ) ∧
        Seg ν dst (SourceControlLayout.values h J cut) ∧ Kept μ ν dst) := by
  have hall (x : ℕ) (hx : x ≤ word h J cut) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hsSpan := hall (spanWord h J cut) (by unfold word; omega)
  have hSpanAll (x : ℕ) (hx : x ≤ spanWord h J cut) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hsSpan
  have hJ := hall J (by unfold word; omega)
  have hW := hall (J*(512*h)) (by unfold word; omega)
  have hWZ : (J : ℤ)*(512*(h : ℤ)) ≤ lim.word := by exact_mod_cast hW
  have hWnonneg : (0 : ℤ) ≤ (J : ℤ)*(512*(h : ℤ)) := by positivity
  have hL := hall (512*h) (by unfold word; omega)
  have hLP := hall (localPrime h) (by unfold word; omega)
  have hM := hall (modulus h J) (by unfold word; omega)
  have hT := hall (scheduleSize h) (by unfold word; omega)
  have hC := hall cut (by unfold word; omega)
  have hK := hSpanAll (downsetCap (J*(512*h)) cut) (by unfold spanWord SourceControlLayout.word; omega)
  have hS := hSpanAll (LightBlockSourceCatalog.count h J) (by unfold spanWord SourceControlLayout.word; omega)
  have hSpanNat : SourceBandBankLayout.span h J cut ≤ spanWord h J cut := by
    rw [← SourceControlLayout.span_eq]
    unfold spanWord SourceControlLayout.word
    omega
  have hSpan := hSpanAll (SourceBandBankLayout.span h J cut) hSpanNat
  have hPower := hall ((scheduleSize h+1)^(J+1)) (by unfold word; omega)
  have hDownset := hall ((J*(512*h)+1)*2^(J*(512*h)+1)) (by unfold word; omega)
  have hLogP := hall (2*((512*h)*localPrime h+1)+2) (by unfold word; omega)
  have hLogPZ : 2*((512*(h : ℤ))*(localPrime h : ℤ)+1)+2 ≤ lim.word := by exact_mod_cast hLogP
  have hLogE := hall (2*(LightBlockSourceBuild.endpointBound h J+1)+2) (by unfold word; omega)
  have hLogEZ : 2*((J*(512*h) : ℤ)*((modulus h J : ℤ)*(localPrime h : ℤ))+1)+2 ≤ lim.word := by
    simpa only [LightBlockSourceBuild.endpointBound,modulus,Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one] using hLogE
  have hMulP := hall ((512*h)*localPrime h) (by unfold word; omega)
  have hMulPZ : (512*(h : ℤ))*(localPrime h : ℤ) ≤ lim.word := by exact_mod_cast hMulP
  have hMulPNonneg : (0 : ℤ) ≤ (512*(h : ℤ))*(localPrime h : ℤ) := by positivity
  have hMP := hall (modulus h J*localPrime h) (by unfold word; omega)
  have hMPZ : (modulus h J : ℤ)*(localPrime h : ℤ) ≤ lim.word := by exact_mod_cast hMP
  have hMPNonneg : (0 : ℤ) ≤ (modulus h J : ℤ)*(localPrime h : ℤ) := by positivity
  have hEndpoint := hall (LightBlockSourceBuild.endpointBound h J) (by unfold word; omega)
  have hEndpointZ : (J*(512*h) : ℤ)*((modulus h J : ℤ)*(localPrime h : ℤ)) ≤ lim.word := by
    simpa only [LightBlockSourceBuild.endpointBound,modulus,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] using hEndpoint
  have hEndpointNonneg : (0 : ℤ) ≤ (J*(512*h) : ℤ)*((modulus h J : ℤ)*(localPrime h : ℤ)) := by positivity
  have hEndpointEq : (J*(512*h) : ℤ)*((modulus h J : ℤ)*(localPrime h : ℤ))+1 =
      ((LightBlockSourceBuild.endpointBound h J+1 : ℕ) : ℤ) := by
    simp [LightBlockSourceBuild.endpointBound,modulus]
  have hMPG : globalModulus h J*(localPrime h : ℤ) ≤ lim.word := by
    simpa only [modulus_cast] using hMPZ
  have hMPG0 : (0 : ℤ) ≤ globalModulus h J*(localPrime h : ℤ) := by
    simpa only [modulus_cast] using hMPNonneg
  have hEndpointG : (J*(512*h) : ℤ)*(globalModulus h J*(localPrime h : ℤ)) ≤ lim.word := by
    simpa only [modulus_cast] using hEndpointZ
  have hEndpointG0 : (0 : ℤ) ≤ (J*(512*h) : ℤ)*(globalModulus h J*(localPrime h : ℤ)) := by
    simpa only [modulus_cast] using hEndpointNonneg
  have hLogEG : 2*((J*(512*h) : ℤ)*(globalModulus h J*(localPrime h : ℤ))+1)+2 ≤ lim.word := by
    simpa only [modulus_cast] using hLogEZ
  have hEndpointEqG : (J*(512*h) : ℤ)*(globalModulus h J*(localPrime h : ℤ))+1 =
      ((LightBlockSourceBuild.endpointBound h J+1 : ℕ) : ℤ) := by
    simpa only [modulus_cast] using hEndpointEq
  have hhead : dst+3 ≤ lim.space := by unfold space at hspace; omega
  apply Meets.of_body C.main
  unfold body time
  have hpowCall := LightNatPower.bounded_meets (d := d+1) C.power μ hJ hPower
  light_call hpowCall with rS ν₁ ⟨hrS,hν₁⟩
  subst ν₁
  have hrS' : rS=(LightBlockSourceCatalog.count h J : ℤ) := hrS
  light_set (J*(512*h) : ℕ)
  have hsizeCall := LightDownsetSize.meets (d := d+1) (μ := μ) C.downset C.setup C.offset
    hw hspace hDownset hcut (by omega)
  light_call hsizeCall with rK ν₂ ⟨hrK,kept⟩
  have hlogCall₁ := log2_meets (d := d+1) C.log ν₂ hLogP
  light_call hlogCall₁ with rLogP ν₃ ⟨hrLogP,hν₃⟩
  subst ν₃
  have hlogCall₂ := log2_meets (d := d+1) C.log ν₂ hLogE
  light_call hlogCall₂ using hEndpointEqG with rLogE ν₄ ⟨hrLogE,hν₄⟩
  subst ν₄
  have hspanCall := LightSourceControlsSpan.meets (d := d+1) C.span C.maximum ν₂ (by omega) hsSpan
  light_call hspanCall using hrK,hrS',hrLogP,hrLogE,spanWord with rSpan ν₅ ⟨hrSpan,hν₅⟩
  subst ν₅
  have hrSpan' : rSpan=(SourceBandBankLayout.span h J cut : ℤ) := by
    rw [← SourceControlLayout.span_eq]
    exact hrSpan
  light_store dst (downsetCap (J*(512*h)) cut : ℕ) using hrK
  light_store (dst+1) (LightBlockSourceCatalog.count h J : ℕ) using hrS'
  light_store (dst+2) (SourceBandBankLayout.span h J cut : ℕ) using hrSpan'
  light_set (SourceBandBankLayout.span h J cut : ℕ) using hrSpan'
  dsimp only
  refine ⟨rfl,?_,?_⟩
  · intro i hi
    have hi' : i < 3 := by simpa [SourceControlLayout.values] using hi
    interval_cases i <;> simp [SourceControlLayout.values]
  · intro a ha
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact kept a (by omega)

end ThreeSum.LightSourceControls
