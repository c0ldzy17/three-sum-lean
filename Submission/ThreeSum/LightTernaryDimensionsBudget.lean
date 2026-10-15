import Submission.ThreeSum.LightTernaryDimensions
import Submission.ThreeSum.TernaryExtensionBudget
import Submission.ThreeSumApsp.Lang.Tasks

/-! Pointwise polynomial word needs for the executed dimension initializer. -/
namespace ThreeSum.LightTernaryDimensions
open Light TernarySignedPadding TernaryExtensionEncoding
set_option maxHeartbeats 5000000
set_option maxRecDepth 10000

def coefficientBase (M b p K : ℕ) := M+b+p+8*p^(4*K+1)+10
def coefficient (M b p K : ℕ) := 5000*(coefficientBase M b p K)^2

theorem r_le {M : ℕ} (hM : 1<M) (n : ℕ) : r M n≤n^2 :=
  Nat.clog_le_of_le_pow (Nat.lt_pow_self hM).le

theorem J_le {M b : ℕ} (hM : 1<M) (hb : 1<b) (n U : ℕ) : J M b n U≤n^2+4*U+3 := by
  have hr := r_le hM n
  have hc : Nat.clog b (4*U+1)≤4*U+1 := Nat.clog_le_of_le_pow (Nat.lt_pow_self hb).le
  unfold J paddedLength digitLength
  omega

theorem word_linear_bound {M b p K : ℕ} [Fact p.Prime]
    (hM : 1<M) (hb : 1<b) (n U : ℕ) :
    word M b p K n U≤1000*(coefficientBase M b p K)^2*(n^2+4*U+3) := by
  let C := coefficientBase M b p K
  let D := n^2+4*U+3
  have hC : 1≤C := by dsimp [C,coefficientBase]; omega
  have hD : 1≤D := by dsimp [D]; omega
  have hMle : M≤C := by dsimp [C,coefficientBase]; omega
  have hble : b≤C := by dsimp [C,coefficientBase]; omega
  have hple : p≤C := by dsimp [C,coefficientBase]; omega
  have hnle : n^2≤D := by dsimp [D]; omega
  have hUle : 4*U+1≤D := by dsimp [D]; omega
  have hrle : r M n≤D := (r_le hM n).trans hnle
  have hJle : J M b n U≤D := J_le hM hb n U
  have hq := menu_field_upper (p := p) (J M b n U+2) K
  have hc : 8*p^(4*K+1)≤C := by dsimp [C,coefficientBase]; omega
  have hqle : p^(dim M b p K n U)≤8*C*D := by
    change p^(menuDegree p (J M b n U+2) K)≤_
    have hD3 : J M b n U+2+1≤4*D := by omega
    have hm := Nat.mul_le_mul hc hD3
    exact hq.trans (by nlinarith)
  have hdle : dim M b p K n U≤8*C*D :=
    (degree_le_field_size (p := p) _).trans hqle
  have ht := menu_field_lower (p := p) (J M b n U+2) K
  have htarget : 8*(J M b n U+3)*p^(4*K)≤8*C*D := by
    apply le_trans _ hqle
    simpa only [dim,show J M b n U+2+1=J M b n U+3 by omega] using ht
  have hu : word M b p K n U≤2*(
      LightTernaryDigitLength.word C D+LightTernaryDigitLength.word C D+
      LightTernaryDigitLength.word C (8*C*D)+8*C*D+D+D+8*C*D+100) := by
    unfold word LightTernaryDigitLength.word
    gcongr
  apply hu.trans
  change _≤1000*C^2*D
  have hC2 : C≤C^2 := by nlinarith
  have hCD : C≤C*D := Nat.le_mul_of_pos_right C (by omega)
  have hC2D : C^2≤C^2*D := Nat.le_mul_of_pos_right (C^2) (by omega)
  have hDD : D≤C^2*D := Nat.le_mul_of_pos_left D (by positivity)
  have hCDD : C*D≤C^2*D := Nat.mul_le_mul_right D hC2
  have hone : 1≤C^2*D := Nat.succ_le_of_lt (by positivity)
  unfold LightTernaryDigitLength.word
  ring_nf
  omega

theorem word_polynomial {M b p K : ℕ} [Fact p.Prime]
    (hM : 1<M) (hb : 1<b) (n U : ℕ) :
    word M b p K n U≤coefficient M b p K*(n+1)^2*(U+1) := by
  have hN : n^2≤(n+1)^2 := by gcongr; omega
  have hNmul : (n+1)^2≤(n+1)^2*(U+1) := Nat.le_mul_of_pos_right _ (by omega)
  have hUmul : U+1≤(n+1)^2*(U+1) := Nat.le_mul_of_pos_left _ (by positivity)
  have hD : n^2+4*U+3≤5*((n+1)^2*(U+1)) := by omega
  apply (word_linear_bound hM hb n U).trans
  unfold coefficient
  nlinarith [Nat.mul_le_mul_left (1000*(coefficientBase M b p K)^2) hD]

def need (M b p K n U : ℕ) : Need := ⟨word M b p K n U,4,2⟩

theorem poly_need {M b p K : ℕ} [Fact p.Prime] (hM : 1<M) (hb : 1<b) :
    PolyNeed (need M b p K) := by
  let A := coefficient M b p K
  have hA : 4≤A := by
    have hh : 1≤coefficientBase M b p K := by unfold coefficientBase; omega
    dsimp [A,coefficient]
    nlinarith
  have hAC : A≤2^Nat.size A := (Nat.lt_size_self A).le
  refine ⟨Nat.size A,2,fun n U => ?_⟩
  have hProd : 1≤((n+1)*(U+1))^2 := Nat.succ_le_of_lt (by positivity)
  have hBig : A≤polyBound (Nat.size A) 2 [n,U] := by
    have hh := hAC.trans (Nat.le_mul_of_pos_right (2^Nat.size A) (show 0<((n+1)*(U+1))^2 by positivity))
    simpa [polyBound] using hh
  refine ⟨?_,by change 4≤_; omega,by change 2≤_; omega⟩
  change word M b p K n U≤polyBound (Nat.size A) 2 [n,U]
  apply (word_polynomial hM hb n U).trans
  have hU : U+1≤(U+1)^2 := by nlinarith
  have hscalar := Nat.mul_le_mul hAC (Nat.mul_le_mul_left ((n+1)^2) hU)
  simpa [polyBound,mul_pow,mul_assoc] using hscalar


theorem program_meets_of_ok {lim : Limits} {M b p K n U dst depth : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hM : 1<M) (hb : 1<b) (hn : 0<n)
    (hok : (need M b p K n U).Ok lim dst depth) :
    Meets lim (program M b p K) 0 depth [n,U,dst] μ (time M b p K n U)
      (fun z ν => z=((p^(dim M b p K n U) : ℕ) : ℤ) ∧
        Seg ν dst [(r M n : ℤ),J M b n U,dim M b p K n U,(p^(dim M b p K n U) : ℕ)] ∧
        Kept μ ν dst) := by
  exact program_meets μ hM hb hn hok.space hok.cells
    (by have hh := hok.depth; change depth+2≤lim.depth at hh; omega) hok.word

end ThreeSum.LightTernaryDimensions
