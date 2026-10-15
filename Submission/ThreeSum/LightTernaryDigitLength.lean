import Submission.ThreeSum.TernarySignedPadding
import Submission.ThreeSumApsp.Lang.Lib.Logs

/-! Executed arbitrary fixed-base digit length and exact zero-padding. -/
namespace ThreeSum.LightTernaryDigitLength
open Light TernarySignedPadding

def clogBody : Stmt :=
  .set 2 (k 0) ;;
  .set 3 (k 1) ;;
  .while (v 3 <' v 0) (
    .set 3 (v 3 *' v 1) ;;
    .set 2 (v 2 +' k 1)) ;;
  .set 0 (v 2)

def clogTime (b x : ℕ) : ℕ := 20*Nat.clog b x+20
def word (b x : ℕ) : ℕ := b*x+b+x+8

variable {lim : Limits} {P : Program} {d : ℕ}

theorem clog_meets {p b x : ℕ} (hp : P[p]?=some clogBody) (μ : ℕ→ℤ)
    (hb : 1<b) (hx : 0<x) (hword : (word b x : ℤ)≤lim.word) :
    Meets lim P p d [x,b] μ (clogTime b x)
      (fun r ν => r=(Nat.clog b x : ℤ) ∧ ν=μ) := by
  have hfit (z : ℕ) (hz : z≤word b x) : (z : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr hz).trans hword
  have hX := hfit x (by unfold word; omega)
  have hB := hfit b (by unfold word; omega)
  have h1 := hfit 1 (by unfold word; omega)
  have hcap := clog_power_bound hb hx
  have hle := Nat.le_pow_clog hb x
  have hcount : Nat.clog b x≤x := Nat.clog_le_of_le_pow (Nat.lt_pow_self hb).le
  have hCount := hfit (Nat.clog b x) (by unfold word; omega)
  apply Meets.of_body hp
  unfold clogBody clogTime
  light_set (0 : ℕ)
  light_set (1 : ℕ)
  refine Ends.next (12*Nat.clog b x+4) (Ends.whileBlock
    (fun i σ => σ=⟨frame [x,b,i,(b^i : ℕ)],μ⟩) (Nat.clog b x)
    (by simp) ?round ?done (by light_time))
  case round =>
    rintro i _ hi rfl
    have hlt : b^i<x := (Nat.lt_clog_iff_pow_lt hb).mp hi
    have hiX : i<x := lt_trans (Nat.lt_pow_self hb) hlt
    have hprod : b^i*b≤word b x := by
      have hm := Nat.mul_le_mul_right b hlt.le
      unfold word
      nlinarith
    have hprodW : ((b^i : ℕ) : ℤ)*(b : ℤ)≤lim.word := by
      exact_mod_cast hfit (b^i*b) hprod
    have hprod0 : (0 : ℤ)≤((b^i : ℕ) : ℤ)*(b : ℤ) := by positivity
    rw [pow_succ]
    generalize b^i=q at hlt hprodW hprod0 ⊢
    exact ⟨by light_side,by light_side,by light_side,by simp [update_frame_setLocal]⟩
  case done =>
    rintro _ rfl
    have hpower := hfit (b^Nat.clog b x) (by unfold word; omega)
    generalize b^Nat.clog b x=q at hle hpower ⊢
    refine ⟨by light_side,by light_side,?_⟩
    light_set (Nat.clog b x : ℕ)
    exact ⟨rfl,rfl⟩

def body (pClog : ℕ) : Stmt :=
  .set 3 (k 4 *' v 0 +' k 1) ;;
  .call pClog [v 3,v 1] 4 ;;
  .set 0 (v 4 +' v 2 +' k 1)

def time (b U : ℕ) : ℕ := clogTime b (4*U+1)+60

theorem meets {pMain pClog b U r : ℕ}
    (hmain : P[pMain]?=some (body pClog)) (hclog : P[pClog]?=some clogBody)
    (μ : ℕ→ℤ) (hb : 1<b) (hd : d<lim.depth)
    (hword : (word b (4*U+1)+r+4 : ℤ)≤lim.word) :
    Meets lim P pMain d [U,b,r] μ (time b U)
      (fun J ν => J=(paddedLength b U r : ℤ) ∧ ν=μ) := by
  have hW : (word b (4*U+1) : ℤ)≤lim.word := by omega
  have hcount : Nat.clog b (4*U+1)≤4*U+1 := Nat.clog_le_of_le_pow (Nat.lt_pow_self hb).le
  have hdata : ((4*U+1 : ℕ) : ℤ)≤lim.word := by unfold word at hword; omega
  have hU : (U : ℤ)≤lim.word := by omega
  have hprod : (4 : ℤ)*U≤lim.word := by omega
  have hJ : (paddedLength b U r : ℤ)≤lim.word := by
    unfold paddedLength digitLength word at *
    push_cast
    omega
  apply Meets.of_body hmain
  unfold body time
  light_set (4*U+1 : ℕ) using clogTime
  light_call (clog_meets (d := d+1) (b := b) (x := 4*U+1) hclog μ hb (by omega) hW)
    using clogTime with J ν ⟨hJval,hmem⟩
  subst ν
  have hJlim : (Nat.clog b (4*U+1) : ℤ)+(r : ℤ)+1≤lim.word := by
    simpa only [paddedLength,digitLength,Nat.cast_add,Nat.cast_one] using hJ
  have hfit : J+(r : ℤ)+1≤lim.word := by rw [hJval]; exact hJlim
  light_set (paddedLength b U r : ℕ) using hJval,paddedLength,digitLength,clogTime
  exact ⟨rfl,rfl⟩

def program : Program := [body 1,clogBody]

theorem program_meets {b U r : ℕ} (μ : ℕ→ℤ) (hb : 1<b) (hd : d<lim.depth)
    (hword : (word b (4*U+1)+r+4 : ℤ)≤lim.word) :
    Meets lim program 0 d [U,b,r] μ (time b U)
      (fun J ν => J=(paddedLength b U r : ℤ) ∧ ν=μ) :=
  meets rfl rfl μ hb hd hword

theorem time_bound {b : ℕ} (hb : 1<b) (U : ℕ) :
    time b U≤20*Nat.log 2 (3*U+1)+120 := by
  have hl := Nat.lt_pow_succ_log_self (by decide : 1<(2 : ℕ)) (3*U+1)
  have hh : 4*U+1≤2^(Nat.log 2 (3*U+1)+2) := by
    rw [show Nat.log 2 (3*U+1)+2=(Nat.log 2 (3*U+1)+1)+1 by omega,pow_succ]
    omega
  have hp := Nat.pow_le_pow_left (show 2≤b by omega) (Nat.log 2 (3*U+1)+2)
  have hc : Nat.clog b (4*U+1)≤Nat.log 2 (3*U+1)+2 := Nat.clog_le_of_le_pow (hh.trans hp)
  unfold time clogTime
  omega

end ThreeSum.LightTernaryDigitLength
