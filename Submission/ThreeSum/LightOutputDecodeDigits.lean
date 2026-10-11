import Submission.ThreeSum.LightOutputDecodeDivide
import Submission.ThreeSum.OutputDecodeOrder

/-!
# Actual big-endian radix digit arrays

The running quotient is divided by the radix once per coordinate, using
the checked binary quotient routine. Digits are written backwards into a
forward-order array. This works for an arbitrary positive radix, including
the occurrence-only radix used by the shared source catalog.
-/

namespace ThreeSum.LightOutputDecodeDigits

open Light

set_option maxHeartbeats 1800000
set_option maxRecDepth 7000

def body (pDivide : ℕ) : Stmt :=
  .set 5 (v 0) ;;
  .for 6 (v 1) (
    .call pDivide [v 5,v 2,v 4] 7 ;;
    .set 8 (v 5 -' v 7 *' v 2) ;;
    .store (v 3 +' v 1 -' k 1 -' v 6) (v 8) ;;
    .set 5 (v 7)) ;;
  .set 0 (v 5)

def time (J V : ℕ) : ℕ := J*(LightOutputDecodeDivide.budget V+100)+30
def word (V m J : ℕ) : ℕ := 4*V+4*m+4*J+32
def space (work V : ℕ) : ℕ := work+(Nat.log 2 (V+1)+2)

def Inv (μ : ℕ → ℤ) (k J m dst work i : ℕ) (σ : State) : Prop :=
  ∃ (q r : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [k,J,m,dst,work,(k/m^i : ℕ),i,q,r],ν⟩ ∧
    (∀ j < i, ν (dst+J-1-j)=(((k/m^j)%m : ℕ) : ℤ)) ∧
    Kept μ ν dst

variable {lim : Limits} {P : Program} {d : ℕ} {μ : ℕ → ℤ}
    {k J m dst work V : ℕ}

theorem meets {pMain pDivide : ℕ}
    (hmain : P[pMain]?=some (body pDivide))
    (hdivide : P[pDivide]?=some LightOutputDecodeDivide.body)
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hm : 1 ≤ m) (hk : k ≤ V) (hsep : dst+J ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word V m J : ℤ) ≤ lim.word) :
    Meets lim P pMain d [k,J,m,dst,work] μ (time J V)
      (fun r ν => r=((k/m^J : ℕ) : ℤ) ∧
        (∀ j < J, ν (dst+j)=((OutputDecodeOrder.indices m J k).getD j 0 : ℤ)) ∧
        Kept μ ν dst) := by
  have hbudget (x : ℕ) (hx : x ≤ word V m J) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hVWord := hbudget V (by unfold word; omega)
  have hkWord : (k : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hk).trans hVWord
  have hmWord := hbudget m (by unfold word; omega)
  have hJWord := hbudget J (by unfold word; omega)
  have h1Word := hbudget 1 (by unfold word; omega)
  have hwork : work ≤ lim.space := by unfold space at hspace; omega
  have hfr : Light.Emod.Pre lim m V work := by
    refine ⟨hm,hw,?_,hspace⟩
    have hh := hbudget (4*V+4*m+16) (by unfold word; omega)
    exact_mod_cast hh
  apply Meets.of_body hmain
  unfold body time
  light_set (k : ℕ)
  refine Ends.pieceThen (Ends.for
    (T := J*(LightOutputDecodeDivide.budget V+100)+6)
    (Q := Inv μ k J m dst work J) (Inv μ k J m dst work) J
    (LightOutputDecodeDivide.budget V+92) ?start ?round ?done ?bound) ?finish
  case start =>
    refine ⟨0,0,μ,?_,?_,SameOn.refl⟩
    · simp only [pow_zero,Nat.div_one]
      exact congrArg (fun loc => (⟨loc,μ⟩ : State))
        ((update_frame_setLocal [k,J,m,dst,work,k] 6 0).trans
          (frame_append_zeros [k,J,m,dst,work,k,0] 2).symm)
    · intro j hj; omega
  case round =>
    rintro i _ hi _ ⟨q,r,ν,rfl,written,kept⟩
    have hrun : k/m^i ≤ V := (Nat.div_le_self _ _).trans hk
    have hqle : (k/m^i)/m ≤ k/m^i := Nat.div_le_self _ _
    have hrem : (k/m^i)%m ≤ V := (Nat.mod_le _ _).trans hrun
    have heq : (k/m^i)/m=k/m^(i+1) := by rw [Nat.div_div_eq_div_mul,pow_succ]
    have hdecomp := Nat.div_add_mod (k/m^i) m
    have hprod : ((k/m^i)/m)*m ≤ V := by rw [Nat.mul_comm]; omega
    have hprodWord : (((k/m^i)/m : ℕ) : ℤ)*(m : ℤ) ≤ lim.word :=
      (by exact_mod_cast hprod : (((k/m^i)/m : ℕ) : ℤ)*(m : ℤ) ≤ (V : ℤ)).trans hVWord
    have hprodNonneg : (0 : ℤ) ≤ (((k/m^i)/m : ℕ) : ℤ)*(m : ℤ) := by positivity
    have hprodWord' : (k : ℤ)/(m : ℤ)^i/(m : ℤ)*(m : ℤ) ≤ lim.word := by
      exact_mod_cast hprodWord
    have hprodNonneg' : (0 : ℤ) ≤ (k : ℤ)/(m : ℤ)^i/(m : ℤ)*(m : ℤ) := by positivity
    have hcurrentWord : (k : ℤ)/(m : ℤ)^i ≤ lim.word := by
      exact_mod_cast (Int.ofNat_le.mpr hrun).trans hVWord
    have hcurrentNonneg : (0 : ℤ) ≤ (k : ℤ)/(m : ℤ)^i := by positivity
    have hremWord' : (k : ℤ)/(m : ℤ)^i%(m : ℤ) ≤ lim.word := by
      exact_mod_cast (Int.ofNat_le.mpr hrem).trans hVWord
    have hremNonneg' : (0 : ℤ) ≤ (k : ℤ)/(m : ℤ)^i%(m : ℤ) :=
      Int.emod_nonneg _ (by omega)
    have hdiff : ((k/m^i : ℕ) : ℤ)-(((k/m^i)/m : ℕ) : ℤ)*(m : ℤ) =
        (((k/m^i)%m : ℕ) : ℤ) := by
      have hh : (m : ℤ)*(((k/m^i)/m : ℕ) : ℤ)+(((k/m^i)%m : ℕ) : ℤ)=
          ((k/m^i : ℕ) : ℤ) := by exact_mod_cast hdecomp
      nlinarith
    have hdiff' : (k : ℤ)/(m : ℤ)^i-(k : ℤ)/(m : ℤ)^i/(m : ℤ)*(m : ℤ)=
        (((k/m^i)%m : ℕ) : ℤ) := by exact_mod_cast hdiff
    have haddr : (dst : ℤ)+(J : ℤ)-1-(i : ℤ)=((dst+J-1-i : ℕ) : ℤ) := by omega
    light_call (LightOutputDecodeDivide.bounded_meets (d := d+1) hdivide hfr hrun)
      with value ν₁ ⟨hv,hkeep⟩
    light_set ((k/m^i)%m : ℕ) using hv,hdiff,hdiff'
    light_store (dst+J-1-i) ((k/m^i)%m : ℕ) using haddr
    light_set (k/m^(i+1) : ℕ) using hv,heq
    refine ⟨by simp,value,((k/m^i)%m : ℕ),
      Function.update ν₁ (dst+J-1-i) (((k/m^i)%m : ℕ) : ℤ),
      by simp [update_frame_setLocal],?_,?_⟩
    · intro j hj
      rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
      · rw [Function.update_of_ne (by omega),hkeep _ (by omega)]
        exact written j hj
      · simp
    · intro a ha
      rw [Function.update_of_ne (by omega),hkeep _ (by omega),kept _ ha]
  case done =>
    rintro _ _ ⟨q,r,ν,rfl,written,kept⟩
    exact ⟨q,r,ν,rfl,written,kept⟩
  case bound =>
    rintro i _ _ _ ⟨q,r,ν,rfl,_,_⟩
    light_side
  case finish =>
    rintro _ ⟨q,r,ν,rfl,written,kept⟩
    have hrun : k/m^J ≤ V := (Nat.div_le_self _ _).trans hk
    light_set (k/m^J : ℕ)
    refine ⟨rfl,?_,kept⟩
    intro j hj
    have ht : J-1-j < J := by omega
    have he := OutputDecodeOrder.indices_getD_reverse m J k ht
    have hwritten := written (J-1-j) ht
    have hcoord : J-1-(J-1-j)=j := by omega
    have haddress : dst+J-1-(J-1-j)=dst+j := by omega
    rw [hcoord] at he
    rw [haddress] at hwritten
    simpa only [he] using hwritten

def program : Program := [body 1,LightOutputDecodeDivide.body]

theorem program_meets
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+1 < lim.depth)
    (hm : 1 ≤ m) (hk : k ≤ V) (hsep : dst+J ≤ work)
    (hspace : space work V ≤ lim.space)
    (hword : (word V m J : ℤ) ≤ lim.word) :
    Meets lim program 0 d [k,J,m,dst,work] μ (time J V)
      (fun r ν => r=((k/m^J : ℕ) : ℤ) ∧
        (∀ j < J, ν (dst+j)=((OutputDecodeOrder.indices m J k).getD j 0 : ℤ)) ∧
        Kept μ ν dst) := meets rfl rfl hw hd hm hk hsep hspace hword

end ThreeSum.LightOutputDecodeDigits
