import Submission.ThreeSum.LightOutputDecodeDigits
import Submission.ThreeSum.LightOutputDecodeStep

/-!
# Complete physical output-index decoding

The first pass writes the actual big-endian local-record digit array.
The second pass splits each digit, reads its retained layer mask, and
accumulates the occurrence-only source-bank code. Both output rows are
in forward original block order, including repeated record values.
-/

namespace ThreeSum.LightOutputDecode

open Light

set_option maxHeartbeats 2200000
set_option maxRecDepth 8000

def body (pDigits pStep : ℕ) : Stmt :=
  .set 7 (v 2 *' v 3) ;;
  .call pDigits [v 0,v 1,v 7,v 5,v 6] 8 ;;
  .set 9 (k 0) ;;
  .set 10 (k 1) ;;
  .for 11 (v 1) (
    .set 12 (M (v 5 +' v 1 -' k 1 -' v 11)) ;;
    .call pStep [v 12,v 2,v 3,v 4,v 9,v 10,
      v 5 +' v 1 -' k 1 -' v 11,
      v 5 +' v 1 +' v 1 -' k 1 -' v 11,v 6] 9 ;;
    .set 10 (v 10 *' v 2)) ;;
  .set 0 (v 9)

def time (J V : ℕ) : ℕ :=
  LightOutputDecodeDigits.time J V+J*(LightOutputDecodeStep.time V+100)+100

def word (V T M J U : ℕ) : ℕ := 32*(V+T*M+T+M+J+T^J+U+10)

def space (work V : ℕ) : ℕ := work+(Nat.log 2 (V+1)+2)

def Inv (μ : ℕ → ℤ) (k J T M masks dst work : ℕ) (q : ℤ)
    (f : ℕ → ℕ) (i : ℕ) (σ : State) : Prop :=
  ∃ (x : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [k,J,T,M,masks,dst,work,T*M,q,
      OutputDecodeOccurrenceCode.code T M i k,T^i,i,x],ν⟩ ∧
    (∀ j, i ≤ j → j < J →
      ν (dst+J-1-j)=(((k/(T*M)^j)%(T*M) : ℕ) : ℤ)) ∧
    (∀ j < i,
      ν (dst+J-1-j)=(((k/(T*M)^j)%(T*M)/M : ℕ) : ℤ) ∧
      ν (dst+J+J-1-j)=(f ((k/(T*M)^j)%(T*M)%M) : ℤ)) ∧
    Kept μ ν dst

structure Procs (P : Program) (pMain : ℕ) where
  pDigits : ℕ
  pStep : ℕ
  pDivide : ℕ
  digits : P[pDigits]?=some (LightOutputDecodeDigits.body pDivide)
  step : P[pStep]?=some (LightOutputDecodeStep.body pDivide)
  divide : P[pDivide]?=some LightOutputDecodeDivide.body
  main : P[pMain]?=some (body pDigits pStep)

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J T M masks dst work V U : ℕ} {f : ℕ → ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M) (hk : k ≤ V)
    (hmask : masks+M ≤ dst) (hsep : dst+J+J ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word V T M J U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    Meets lim P pMain d [k,J,T,M,masks,dst,work] μ (time J V)
      (fun r ν => r=(OutputDecodeOccurrenceCode.code T M J k : ℤ) ∧
        (∀ j < J, ν (dst+j)=(((OutputDecodeOrder.indices (T*M) J k).getD j 0/M : ℕ) : ℤ)) ∧
        (∀ j < J, ν (dst+J+j)=(f ((OutputDecodeOrder.indices (T*M) J k).getD j 0%M) : ℤ)) ∧
        Kept μ ν dst) := by
  have hbudget (a : ℕ) (ha : a ≤ word V T M J U) : (a : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ha).trans hword
  have hVWord := hbudget V (by unfold word; omega)
  have hkWord : (k : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hk).trans hVWord
  have hTWord := hbudget T (by unfold word; omega)
  have hMWord := hbudget M (by unfold word; omega)
  have hTMWord := hbudget (T*M) (by unfold word; omega)
  have hTMWord' : (T : ℤ)*(M : ℤ) ≤ lim.word := by exact_mod_cast hTMWord
  have hJWord := hbudget J (by unfold word; omega)
  have hpowerWord := hbudget (T^J) (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  have hwork : work ≤ lim.space := by unfold space at hspace; omega
  have hdigitsWord := hbudget (LightOutputDecodeDigits.word V (T*M) J)
    (by unfold LightOutputDecodeDigits.word word; omega)
  have hTM : 1 ≤ T*M := Nat.mul_pos hT hM
  apply Meets.of_body S.main
  unfold body time
  light_set (T*M : ℕ)
  light_call (LightOutputDecodeDigits.meets (d := d+1) (μ := μ) (dst := dst)
    (work := work) S.digits S.divide hw
    (by omega) hTM hk (by omega) hspace hdigitsWord)
    with q ν ⟨hq,digits,kept⟩
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := J*(LightOutputDecodeStep.time V+100)+6)
    (Q := Inv μ k J T M masks dst work q f J)
    (Inv μ k J T M masks dst work q f) J
    (LightOutputDecodeStep.time V+92) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,ν,?_,?_,?_,kept⟩
    · simp only [OutputDecodeOccurrenceCode.code,pow_zero]
      simp [update_frame_setLocal]
      exact (frame_append_zeros [k,J,T,M,masks,dst,work,T*M,q,0,1,0] 1).symm
    · intro j _ hj
      have hr := OutputDecodeOrder.indices_getD_reverse (T*M) J k hj
      have he := digits (J-1-j) (by omega)
      have ha : dst+(J-1-j)=dst+J-1-j := by omega
      simpa only [hr,ha] using he
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨x,ν',rfl,remaining,written,kept'⟩
    have hpow : T^i ≤ T^J := Nat.pow_le_pow_right hT (by omega)
    have hpowNext : T^(i+1) ≤ T^J := Nat.pow_le_pow_right hT (by omega)
    have hcode := OutputDecodeOccurrenceCode.code_lt hT hM i k
    have hcurrent : (k/(T*M)^i)%(T*M) ≤ V :=
      (Nat.mod_le _ _).trans ((Nat.div_le_self _ _).trans hk)
    have hcurrentWord : (((k/(T*M)^i)%(T*M) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hcurrent).trans hVWord
    have haccWord : (OutputDecodeOccurrenceCode.code T M i k : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr (hcode.le.trans hpow)).trans hpowerWord
    have hpowWord : ((T^i : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hpow).trans hpowerWord
    have hnextWord : ((T^(i+1) : ℕ) : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hpowNext).trans hpowerWord
    have hnextWord' : (T : ℤ)^i*(T : ℤ) ≤ lim.word := by
      rw [← pow_succ]
      exact_mod_cast hnextWord
    have hnextNonneg : (0 : ℤ) ≤ (T : ℤ)^i*(T : ℤ) := by positivity
    have hstepWord := hbudget
      (LightOutputDecodeStep.word V T M (OutputDecodeOccurrenceCode.code T M i k) (T^i) U)
      (by unfold LightOutputDecodeStep.word word; rw [← pow_succ]; omega)
    have haddr : (dst : ℤ)+(J : ℤ)-1-(i : ℤ)=((dst+J-1-i : ℕ) : ℤ) := by omega
    have haddrMask : (dst : ℤ)+(J : ℤ)+(J : ℤ)-1-(i : ℤ)=
        ((dst+J+J-1-i : ℕ) : ℤ) := by omega
    have hmaskRead : ∀ s < M, ν' (masks+s)=(f s : ℤ) := by
      intro s hs
      rw [kept' _ (by omega)]
      exact hread s hs
    have hxRead := remaining i le_rfl hi
    light_set ((k/(T*M)^i)%(T*M) : ℕ) using haddr,hxRead
    have hcall := LightOutputDecodeStep.meets_code_step (d := d+1)
      (x := (k/(T*M)^i)%(T*M)) (acc := OutputDecodeOccurrenceCode.code T M i k)
      (power := T^i) (outOcc := dst+J-1-i) (outMask := dst+J+J-1-i)
      S.step S.divide hw (by omega) hT hM rfl rfl rfl hcurrent
      (by omega) (by omega) (by omega) (by omega) hspace hstepWord hf hmaskRead
    light_call hcall using haddr,haddrMask with value ν₁ ⟨hv,hocc,hout,hkept⟩
    light_set (T^(i+1) : ℕ) using pow_succ
    refine ⟨by simp,((k/(T*M)^i)%(T*M) : ℕ),ν₁,?_,?_,?_,?_⟩
    · simp [update_frame_setLocal,hv]
    · intro j hij hj
      rw [hkept _ ⟨by omega,by omega,by omega⟩]
      exact remaining j (by omega) hj
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · constructor
        · rw [hkept _ ⟨by omega,by omega,by omega⟩]
          exact (written j hj).1
        · rw [hkept _ ⟨by omega,by omega,by omega⟩]
          exact (written j hj).2
      · exact ⟨hocc,hout⟩
    · intro a ha
      rw [hkept a ⟨by omega,by omega,by omega⟩,kept' a ha]
  case done =>
    rintro _ _ ⟨x,ν',rfl,remaining,written,kept'⟩
    exact ⟨x,ν',rfl,remaining,written,kept'⟩
  case bound =>
    rintro i _ _ _ ⟨x,ν',rfl,_,_,_⟩
    light_side
  case finish =>
    rintro _ ⟨x,ν',rfl,_,written,kept'⟩
    have hc := OutputDecodeOccurrenceCode.code_lt hT hM J k
    have hcWord : (OutputDecodeOccurrenceCode.code T M J k : ℤ) ≤ lim.word :=
      (Int.ofNat_le.mpr hc.le).trans hpowerWord
    light_set (OutputDecodeOccurrenceCode.code T M J k : ℕ)
    refine ⟨rfl,?_,?_,kept'⟩
    · intro j hj
      have ht : J-1-j < J := by omega
      have hdigit := OutputDecodeOrder.indices_getD_reverse (T*M) J k ht
      have he := (written (J-1-j) ht).1
      have hcoord : J-1-(J-1-j)=j := by omega
      have haddr : dst+J-1-(J-1-j)=dst+j := by omega
      rw [hcoord] at hdigit
      simpa only [haddr,hdigit] using he
    · intro j hj
      have ht : J-1-j < J := by omega
      have hdigit := OutputDecodeOrder.indices_getD_reverse (T*M) J k ht
      have he := (written (J-1-j) ht).2
      have hcoord : J-1-(J-1-j)=j := by omega
      have haddr : dst+J+J-1-(J-1-j)=dst+J+j := by omega
      rw [hcoord] at hdigit
      simpa only [haddr,hdigit] using he

def program : Program :=
  [body 1 2,LightOutputDecodeDigits.body 3,
    LightOutputDecodeStep.body 3,LightOutputDecodeDivide.body]

def programProcs : Procs program 0 := ⟨1,2,3,rfl,rfl,rfl,rfl⟩

theorem program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth)
    (hT : 1 ≤ T) (hM : 1 ≤ M) (hk : k ≤ V)
    (hmask : masks+M ≤ dst) (hsep : dst+J+J ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word V T M J U : ℤ) ≤ lim.word)
    (hf : ∀ s < M, f s ≤ U) (hread : ∀ s < M, μ (masks+s)=(f s : ℤ)) :
    Meets lim program 0 d [k,J,T,M,masks,dst,work] μ (time J V)
      (fun r ν => r=(OutputDecodeOccurrenceCode.code T M J k : ℤ) ∧
        (∀ j < J, ν (dst+j)=(((OutputDecodeOrder.indices (T*M) J k).getD j 0/M : ℕ) : ℤ)) ∧
        (∀ j < J, ν (dst+J+j)=(f ((OutputDecodeOrder.indices (T*M) J k).getD j 0%M) : ℤ)) ∧
        Kept μ ν dst) :=
  programProcs.meets hw hd hT hM hk hmask hsep hspace hword hf hread

theorem time_bound (J V : ℕ) :
    time J V ≤ 500*(J+1)*(Nat.log 2 (V+1)+2) := by
  unfold time LightOutputDecodeDigits.time LightOutputDecodeStep.time
    LightOutputDecodeDivide.budget
  nlinarith

end ThreeSum.LightOutputDecode
