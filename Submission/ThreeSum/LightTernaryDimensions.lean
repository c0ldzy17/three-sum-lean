import Submission.ThreeSum.LightArray
import Submission.ThreeSum.LightTernaryDigitLength
import Submission.ThreeSum.LightNatPower
import Submission.ThreeSum.TernaryExtensionCandidates

namespace ThreeSum.LightTernaryDimensions
open Light TernarySignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 3000000

def body (M b p K : ℕ) : Stmt :=
  .set 3 (v 0 *' v 0) ;;
  .call 1 [v 3,k M] 4 ;;
  .call 2 [v 1,k b,v 4] 5 ;;
  .set 8 (k (8*p^(4*K)) *' (v 5 +' k 3)) ;;
  .call 1 [v 8,k p] 6 ;;
  .call 3 [k p,v 6] 7 ;;
  .store (v 2) (v 4) ;;
  .store (v 2 +' k 1) (v 5) ;;
  .store (v 2 +' k 2) (v 6) ;;
  .store (v 2 +' k 3) (v 7) ;;
  .set 0 (v 7)

def program (M b p K : ℕ) : Program :=
  [body M b p K,LightTernaryDigitLength.clogBody,
    LightTernaryDigitLength.body 1,LightNatPower.body]

def r (M n : ℕ) := Nat.clog M (n^2)
def J (M b n U : ℕ) := paddedLength b U (r M n)
def dim (M b p K n U : ℕ) := menuDegree p (J M b n U+2) K

def word (M b p K n U : ℕ) : ℕ :=
  2*(LightTernaryDigitLength.word M (n^2)+LightTernaryDigitLength.word b (4*U+1)+
    LightTernaryDigitLength.word p (8*(J M b n U+3)*p^(4*K))+
    p^(dim M b p K n U)+r M n+J M b n U+dim M b p K n U+100)

def time (M b p K n U : ℕ) : ℕ :=
  LightTernaryDigitLength.clogTime M (n^2)+LightTernaryDigitLength.time b U+
    LightTernaryDigitLength.clogTime p (8*(J M b n U+3)*p^(4*K))+
    LightNatPower.time (dim M b p K n U)+250

variable {lim : Limits} {depth : ℕ}

theorem program_meets {M b p K n U dst : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : dst+4≤lim.space)
    (hdepth : depth+1<lim.depth) (hword : (word M b p K n U : ℤ)≤lim.word) :
    Meets lim (program M b p K) 0 depth [n,U,dst] μ (time M b p K n U)
      (fun z ν => z=((p^(dim M b p K n U) : ℕ) : ℤ) ∧
        Seg ν dst [(r M n : ℤ),J M b n U,dim M b p K n U,(p^(dim M b p K n U) : ℕ)] ∧
        Kept μ ν dst) := by
  have hbudget (v : ℕ) (hv : v≤word M b p K n U) : (v : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hv).trans hword
  have hMword := hbudget (LightTernaryDigitLength.word M (n^2)) (by unfold word; omega)
  have hBword : ((LightTernaryDigitLength.word b (4*U+1)+r M n+4 : ℕ) : ℤ)≤lim.word := by
    apply hbudget
    unfold word
    omega
  have hPword := hbudget (LightTernaryDigitLength.word p (8*(J M b n U+3)*p^(4*K))) (by unfold word; omega)
  have hMliteral : (M : ℤ)≤lim.word := by unfold LightTernaryDigitLength.word at hMword; omega
  have hBliteral : (b : ℤ)≤lim.word := by unfold LightTernaryDigitLength.word at hBword; omega
  have hPliteral : (p : ℤ)≤lim.word := by unfold LightTernaryDigitLength.word at hPword; omega
  have hRword := hbudget (r M n) (by unfold word; omega)
  have hJword := hbudget (J M b n U) (by unfold word; omega)
  have hDword := hbudget (dim M b p K n U) (by unfold word; omega)
  have hQword := hbudget (p^(dim M b p K n U)) (by unfold word; omega)
  have hn2Word := hbudget (n^2) (by unfold word LightTernaryDigitLength.word; omega)
  have hnWord : (n : ℤ)≤lim.word := by
    have hh : n≤n^2 := by nlinarith
    exact (Int.ofNat_le.mpr hh).trans hn2Word
  have hn2Nonneg : 0≤(n : ℤ)*(n : ℤ) := by positivity
  have hn2Int : (n : ℤ)*(n : ℤ)≤lim.word := by simpa only [pow_two,Nat.cast_mul] using hn2Word
  have htarget : 0<8*(J M b n U+3)*p^(4*K) := by have hp := (Fact.out : p.Prime).pos; positivity
  have htargetWord := hbudget (8*(J M b n U+3)*p^(4*K)) (by unfold word LightTernaryDigitLength.word; omega)
  have hconstantWord : ((8*p^(4*K) : ℕ) : ℤ)≤lim.word := by
    have hh : 8*p^(4*K)≤8*(J M b n U+3)*p^(4*K) :=
      Nat.mul_le_mul_right _ (by omega : 8≤8*(J M b n U+3))
    exact (Int.ofNat_le.mpr hh).trans htargetWord
  have hJ3Word := hbudget (J M b n U+3) (by unfold word; omega)
  have hpow (i : ℕ) (hi : i≤dim M b p K n U) : ((p^i : ℕ) : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by have := (Fact.out : p.Prime).one_lt; omega) hi)).trans hQword
  apply Meets.of_body (by rfl)
  unfold body time
  light_set (n^2 : ℕ) using pow_two,LightTernaryDigitLength.clogTime,LightTernaryDigitLength.time,LightNatPower.time
  light_call (LightTernaryDigitLength.clog_meets (P := program M b p K) (p := 1)
    (d := depth+1) rfl μ hM (by positivity : 0<n^2) hMword)
    using LightTernaryDigitLength.clogTime,LightTernaryDigitLength.time,LightNatPower.time
    with rr ν ⟨hr,hν⟩
  subst ν
  light_call (LightTernaryDigitLength.meets (P := program M b p K) (pMain := 2) (pClog := 1)
    (d := depth+1) rfl rfl μ hb (by omega) hBword)
    using r,hr,LightTernaryDigitLength.clogTime,LightTernaryDigitLength.time,LightNatPower.time
    with jj ν ⟨hj,hν⟩
  subst ν
  have htInt : ((8*p^(4*K) : ℕ) : ℤ)*((J M b n U : ℤ)+3)≤lim.word := by
    convert htargetWord using 1 <;> push_cast <;> ring
  push_cast at hconstantWord htInt
  have hconstantNonneg : 0≤(8 : ℤ)*(p : ℤ)^(4*K) := by positivity
  have htNonneg : 0≤(8 : ℤ)*(p : ℤ)^(4*K)*((J M b n U : ℤ)+3) := by positivity
  dsimp only [J,r] at htInt htNonneg hJ3Word
  have htAlias : (8 : ℤ)*(p : ℤ)^(4*K)*((paddedLength b U (Nat.clog M (n^2)) : ℤ)+3)=
      8*((paddedLength b U (Nat.clog M (n^2)) : ℤ)+3)*(p : ℤ)^(4*K) := by ring
  light_set (8*(J M b n U+3)*p^(4*K) : ℕ)
    using J,hj,r,hr,LightTernaryDigitLength.clogTime,LightTernaryDigitLength.time,LightNatPower.time
  light_call (LightTernaryDigitLength.clog_meets (P := program M b p K) (p := 1)
    (d := depth+1) rfl μ (Fact.out : p.Prime).one_lt htarget hPword)
    using LightTernaryDigitLength.clogTime,LightTernaryDigitLength.time,LightNatPower.time
    with dd ν ⟨hd,hν⟩
  subst ν
  light_call (LightNatPower.meets (P := program M b p K) (p := 3) (d := depth+1)
    rfl μ hDword hpow) using dim,menuDegree,hd,LightTernaryDigitLength.clogTime,
      LightTernaryDigitLength.time,LightNatPower.time
    with qq ν ⟨hq,hν⟩
  subst ν
  light_store dst (r M n) using r,hr,LightNatPower.time
  light_store (dst+1) (J M b n U) using J,hj,r,LightNatPower.time
  light_store (dst+2) (dim M b p K n U) using dim,menuDegree,hd,LightNatPower.time
  light_store (dst+3) (p^(dim M b p K n U)) using hq,LightNatPower.time
  light_set (p^(dim M b p K n U) : ℕ) using hq,LightNatPower.time
  refine ⟨rfl,?_,?_⟩
  · intro i hi
    have hi4 : i<4 := by simpa using hi
    interval_cases i <;> simp
  · light_keep

end ThreeSum.LightTernaryDimensions
