import Submission.ThreeSum.LightNatPower
import Submission.ThreeSum.LightSmallDivide
import Submission.ThreeSum.BandScales
import Submission.ThreeSumApsp.Lang.Lib.Sqrt
import Submission.ThreeSumApsp.Lang.Lib.Seg

/-!
# Executing global powers and rounded band sizes

This routine consumes the already computed local output count, local prime,
block count, and total inner size. All global powers, the square-root
rounding, and the final ceiling division are actual Light computations.
The square-root loop and quotient loop are included in the stated time.
-/

namespace ThreeSum.LightGlobalSizes

set_option maxHeartbeats 1000000

open Light LocalCoverBounds

def divisor (mu : ℕ) : ℕ := 2^(mu/20)
def root (C J : ℕ) : ℕ := rootCeiling (C^J)
def numerator (C J mu : ℕ) : ℕ := root C J+divisor mu-1
def band (C J mu : ℕ) : ℕ := numerator C J mu/divisor mu

def values (C p J mu : ℕ) : List ℤ :=
  [((C^J : ℕ) : ℤ),((p^J : ℕ) : ℤ),root C J,divisor mu,band C J mu]

def body (pPower pDiv pSqrt : ℕ) : Stmt :=
  .call pPower [v 0,v 2] 5 ;;
  .call pPower [v 1,v 2] 6 ;;
  .call pDiv [v 3,k 20] 7 ;;
  .call pPower [k 2,v 7] 8 ;;
  .call pSqrt [v 5 -' k 1] 9 ;;
  .set 10 (v 9 +' k 1) ;;
  .set 11 (v 10 +' v 8 -' k 1) ;;
  .call pDiv [v 11,v 8] 12 ;;
  .store (v 4) (v 5) ;;
  .store (v 4 +' k 1) (v 6) ;;
  .store (v 4 +' k 2) (v 10) ;;
  .store (v 4 +' k 3) (v 8) ;;
  .store (v 4 +' k 4) (v 12) ;;
  .set 0 (v 6)

def time (C J mu : ℕ) : ℕ := 2*LightNatPower.time J+
  LightSmallDivide.time mu 20+LightNatPower.time (mu/20)+sqrtTime (C^J-1)+
  LightSmallDivide.time (numerator C J mu) (divisor mu)+300

def word (C p J mu : ℕ) : ℕ := 1000*(C+p+J+mu+C^J+p^J+divisor mu+1)

structure Procs (P : Program) (pMain : ℕ) where
  pPower : ℕ
  pDiv : ℕ
  pSqrt : ℕ
  power : P[pPower]? = some LightNatPower.body
  divide : P[pDiv]? = some LightSmallDivide.body
  sqrt : P[pSqrt]? = some sqrtBody
  main : P[pMain]? = some (body pPower pDiv pSqrt)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {C p J mu dst : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hC : 1 ≤ C) (hp : 1 ≤ p) (hspace : dst+5 ≤ lim.space)
    (hword : (word C p J mu : ℤ) ≤ lim.word) :
    Meets lim P pMain d [C,p,J,mu,dst] μ (time C J mu)
      (fun r μ' => r = ((p^J : ℕ) : ℤ) ∧ Seg μ' dst (values C p J mu) ∧
        SameOutside μ μ' dst 5) := by
  have hMpos : 0 < C^J := Nat.pow_pos (by omega)
  have hRpos : 0 < p^J := Nat.pow_pos (by omega)
  have hDpos : 0 < divisor mu := Nat.two_pow_pos _
  have hroot : root C J ≤ C^J+1 := by
    unfold root rootCeiling
    have hs := Nat.sqrt_le_self (C^J-1)
    omega
  have hrootPos : 0 < root C J := rootCeiling_pos _
  have heLe : mu/20 ≤ mu := Nat.div_le_self _ _
  have hnum : numerator C J mu ≤ C^J+divisor mu+1 := by unfold numerator; omega
  have hband : band C J mu ≤ numerator C J mu := Nat.div_le_self _ _
  have hbound (x : ℕ) (hx : x ≤ word C p J mu) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hconst : (20 : ℤ) ≤ lim.word := hbound 20 (by unfold word; omega)
  have hCw := hbound C (by unfold word; omega)
  have hpw := hbound p (by unfold word; omega)
  have hJw := hbound J (by unfold word; omega)
  have hmuw := hbound mu (by unfold word; omega)
  have hMw := hbound (C^J) (by unfold word; omega)
  have hRw := hbound (p^J) (by unfold word; omega)
  have hMZpos : (0 : ℤ) < (C : ℤ)^J := by exact_mod_cast hMpos
  have hMZw : (C : ℤ)^J ≤ lim.word := by exact_mod_cast hMw
  have hRZpos : (0 : ℤ) < (p : ℤ)^J := by exact_mod_cast hRpos
  have hRZw : (p : ℤ)^J ≤ lim.word := by exact_mod_cast hRw
  have hDw := hbound (divisor mu) (by unfold word; omega)
  have hrw := hbound (root C J) (by unfold word; omega)
  have hnw := hbound (numerator C J mu) (by unfold word; omega)
  have hsumw := hbound (root C J+divisor mu) (by unfold word; omega)
  have hsumZw : (root C J : ℤ)+(divisor mu : ℤ) ≤ lim.word := by exact_mod_cast hsumw
  have hbw := hbound (band C J mu) (by unfold word; omega)
  have hew := hbound (mu/20) (by unfold word; omega)
  have heZ : (0 : ℤ) ≤ (mu : ℤ)/20 := by positivity
  have heZw : (mu : ℤ)/20 ≤ lim.word := by exact_mod_cast hew
  have hpowC (i : ℕ) (hi : i ≤ J) : ((C^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hC hi)).trans hMw
  have hpowP (i : ℕ) (hi : i ≤ J) : ((p^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right hp hi)).trans hRw
  have hpowD (i : ℕ) (hi : i ≤ mu/20) : ((2^i : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hDw
  have hsub : ((C^J : ℕ) : ℤ)-1 = ((C^J-1 : ℕ) : ℤ) := by omega
  have hnumEq : (root C J : ℤ)+(divisor mu : ℤ)-1 = (numerator C J mu : ℤ) := by
    unfold numerator
    omega
  apply Meets.of_body S.main
  unfold body time
  light_call (LightNatPower.meets (d := d+1) S.power μ hJw hpowC)
    using LightNatPower.time,LightSmallDivide.time with mval μ₁ ⟨hmval,hmem₁⟩
  subst μ₁
  have hmvalZ : mval = (C : ℤ)^J := by simpa only [Nat.cast_pow] using hmval
  light_call (LightNatPower.meets (d := d+1) S.power μ hJw hpowP)
    using LightNatPower.time,LightSmallDivide.time with rval μ₂ ⟨hrval,hmem₂⟩
  subst μ₂
  have hrvalZ : rval = (p : ℤ)^J := by simpa only [Nat.cast_pow] using hrval
  light_call (LightSmallDivide.meets (d := d+1) (a := mu) (b := 20) S.divide μ
    (hbound _ (by unfold word; omega)))
    using LightNatPower.time,LightSmallDivide.time with e μ₃ ⟨he,hmem₃⟩
  subst μ₃
  light_call (LightNatPower.meets (d := d+1) S.power μ hew hpowD)
    using he,LightNatPower.time,LightSmallDivide.time with dval μ₄ ⟨hdval,hmem₄⟩
  subst μ₄
  have hdval' : dval = (divisor mu : ℤ) := hdval
  light_call (sqrt_meets (d := d+1) (K := C^J-1) S.sqrt μ
    (hbound _ (by unfold word; omega)))
    using hmvalZ,hsub,LightNatPower.time,LightSmallDivide.time with s μ₅ ⟨hs,hmem₅⟩
  subst μ₅
  have hs' : s+1 = (root C J : ℤ) := by
    simpa [root,rootCeiling] using congrArg (fun z : ℤ => z+1) hs
  light_set (root C J : ℕ) using hs',LightNatPower.time,LightSmallDivide.time
  light_set (numerator C J mu : ℕ) using hdval',hnumEq,LightNatPower.time,LightSmallDivide.time
  light_call (LightSmallDivide.meets (d := d+1) (a := numerator C J mu) (b := divisor mu) S.divide μ
    (hbound _ (by unfold word; omega)))
    using hdval',LightNatPower.time,LightSmallDivide.time with bval μ₆ ⟨hbval,hmem₆⟩
  subst μ₆
  have hbval' : bval = (band C J mu : ℤ) := hbval
  light_store dst (C^J : ℕ) using hmvalZ,LightNatPower.time,LightSmallDivide.time
  light_store (dst+1) (p^J : ℕ) using hrvalZ,LightNatPower.time,LightSmallDivide.time
  light_store (dst+2) (root C J : ℕ) using LightNatPower.time,LightSmallDivide.time
  light_store (dst+3) (divisor mu : ℕ) using hdval',LightNatPower.time,LightSmallDivide.time
  light_store (dst+4) (band C J mu : ℕ) using hbval',LightNatPower.time,LightSmallDivide.time
  light_set (p^J : ℕ) using hrvalZ,LightNatPower.time,LightSmallDivide.time
  exact ⟨rfl,by simp [values,seg_cons],by light_keep⟩

def program : Program := [body 1 2 3,LightNatPower.body,LightSmallDivide.body,sqrtBody]
def procs : Procs program 0 := ⟨1,2,3,rfl,rfl,rfl,rfl⟩

theorem program_meets {μ : ℕ → ℤ} {C p J mu dst : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d < lim.depth)
    (hC : 1 ≤ C) (hp : 1 ≤ p) (hspace : dst+5 ≤ lim.space)
    (hword : (word C p J mu : ℤ) ≤ lim.word) :
    Meets lim program 0 d [C,p,J,mu,dst] μ (time C J mu)
      (fun r μ' => r = ((p^J : ℕ) : ℤ) ∧ Seg μ' dst (values C p J mu) ∧
        SameOutside μ μ' dst 5) := procs.meets hw hd hC hp hspace hword

theorem band_eq (C J mu : ℕ) : band C J mu = root C J ⌈/⌉ divisor mu := rfl

theorem time_bound (C J mu : ℕ) :
    time C J mu ≤ 1000*(J+mu+root C J+divisor mu+1) := by
  have he := Nat.div_le_self mu 20
  have hb := Nat.div_le_self (numerator C J mu) (divisor mu)
  have hn : numerator C J mu ≤ root C J+divisor mu := Nat.sub_le _ _
  have hs : Nat.sqrt (C^J-1) ≤ root C J := by unfold root rootCeiling; omega
  unfold time LightNatPower.time LightSmallDivide.time sqrtTime
  omega

def localCount (n : ℕ) : ℕ :=
  outputCount (512*Scales.microHalf (Scales.inputBits n)) (Scales.microHalf (Scales.inputBits n))

theorem localCount_pos (n : ℕ) : 0 < localCount n := Nat.choose_pos (by omega)

theorem localCount_pow (n : ℕ) :
    localCount n ^ Scales.blockCount (Scales.inputBits n) = Scales.typedOutputs n := by
  have hwidth : 256*Scales.muZero n = 512*Scales.microHalf (Scales.inputBits n) := by
    rw [Scales.muZero_eq_twice_half]
    ring
  unfold Scales.typedOutputs
  rw [hwidth,Scales.muZero_eq_twice_half]
  rfl

theorem values_scales (n : ℕ) :
    values (localCount n) (Scales.localRadix n) (Scales.blockCount (Scales.inputBits n)) (Scales.mu n) =
      [(Scales.typedOutputs n : ℤ),Scales.radix n,BandScales.bandRoot n,
        BandScales.bandDivisor n,BandScales.bandSize n] := by
  simp only [values,root,localCount_pow,divisor,band,numerator,
    Scales.radix,BandScales.bandRoot,BandScales.bandDivisor,BandScales.bandSize,Nat.ceilDiv_eq_add_pred_div]

end ThreeSum.LightGlobalSizes
