import Submission.ThreeSum.LightExtensionBackendSetupBudget
import Submission.ThreeSum.LightTernaryDimensions
import Submission.ThreeSumApsp.Lang.Tasks

noncomputable section
namespace ThreeSum.LightExtensionBackendSetup
open Light LightExtensionBackendLayout TernaryExtensionEncoding
set_option maxHeartbeats 3000000
set_option maxRecDepth 12000

def need (d p q J : ℕ) : Need := ⟨reserve d p q J,reserve d p q J,15⟩

theorem need_meets {lim : Limits} {base d p q J depth : ℕ} [Fact p.Prime]
    (μ : ℕ → ℤ) (hdim : 0 < d) (hq : p^d=q) (H : (need d p q J).Ok lim base depth) :
    Meets lim program 38 depth [p,d,q,J,base] μ (time base d p q J)
      (fun z ν => ∃ c < q, z=(c+1 : ℕ) ∧ Irreducible (monicOfCode (p := p) d c) ∧
        (∀ s < q*q, ∀ i < J+2, ν (physical base d q J+s*(J+2)+i)=
          (LightExtensionSeedMatrix.value
            (encodedMul (LightExtensionBackend.modulusMonic (factor base d p q J) c)) q p s
            (TernarySignedLayout.offset J i) : ℤ)) ∧ Kept μ ν base) :=
  program_meets μ hdim hq H.space (by have := H.depth; dsimp [need] at this; omega) H.cells

def envelope (p K : ℕ) : ℕ := 6*(16*p^(4*K+1)+p+2)

theorem parameters_polynomial {M b p : ℕ} [Fact p.Prime]
    (hM : 1 < M) (hb : 1 < b) (K n U : ℕ) :
    let J := LightTernaryDimensions.J M b n U
    let d := LightTernaryDimensions.dim M b p K n U
    d+p+p^d+J+2 ≤ envelope p K*(n+1)^2*(U+1) := by
  dsimp only
  let J := LightTernaryDimensions.J M b n U
  let d := LightTernaryDimensions.dim M b p K n U
  have hlogb : Nat.clog b (4*U+1) ≤ 4*U+1 := Nat.clog_le_of_le_pow (Nat.lt_pow_self hb).le
  have hlogM : Nat.clog M (n^2) ≤ n^2 := Nat.clog_le_of_le_pow (Nat.lt_pow_self hM).le
  have hJ : J ≤ 4*U+n^2+3 := by
    dsimp [J,LightTernaryDimensions.J,TernarySignedPadding.paddedLength,TernarySignedPadding.digitLength,
      LightTernaryDimensions.r]
    omega
  have hscale : J+3 ≤ 6*(n+1)^2*(U+1) := by
    have hN : n^2+1 ≤ (n+1)^2 := by
      calc
        _ ≤ n^2+2*n+1 := by omega
        _ = _ := by ring
    have hh := Nat.mul_le_mul_right U (show 1 ≤ (n+1)^2 by omega)
    have hprod : n^2+1+U ≤ (n+1)^2*(U+1) := by nlinarith only [hh,hN]
    nlinarith only [hJ,hprod]
  have hq : p^d ≤ 8*p^(4*K+1)*(J+3) := menu_field_upper (p := p) (J+2) K
  have hd : d ≤ p^d := degree_le_field_size d
  have hparams : d+p+p^d+J+2 ≤ (16*p^(4*K+1)+p+2)*(J+3) := by
    have hh : p ≤ p*(J+3) := Nat.le_mul_of_pos_right _ (by omega)
    nlinarith
  calc
    _ ≤ (16*p^(4*K+1)+p+2)*(J+3) := hparams
    _ ≤ (16*p^(4*K+1)+p+2)*(6*(n+1)^2*(U+1)) := Nat.mul_le_mul_left _ hscale
    _ = _ := by unfold envelope; ring

theorem need_poly {M b p : ℕ} [Fact p.Prime] (hM : 1 < M) (hb : 1 < b) (K : ℕ) :
    PolyNeed (fun n U =>
      let J := LightTernaryDimensions.J M b n U
      let d := LightTernaryDimensions.dim M b p K n U
      need d p (p^d) J) := by
  let C := 100000000*(envelope p K)^6+15
  refine ⟨Nat.size C,12,fun n U => ?_⟩
  let J := LightTernaryDimensions.J M b n U
  let d := LightTernaryDimensions.dim M b p K n U
  have hs := parameters_polynomial (M := M) (b := b) (p := p) hM hb K n U
  have hh := Nat.mul_le_mul_left 100000000 (Nat.pow_le_pow_left hs 6)
  have he : (envelope p K*(n+1)^2*(U+1))^6=(envelope p K)^6*(n+1)^12*(U+1)^6 := by ring
  rw [he] at hh
  have hU : (U+1)^6 ≤ (U+1)^12 := Nat.pow_le_pow_right (by omega) (by decide)
  have hbig : reserve d p (p^d) J ≤ C*((n+1)*(U+1))^12 := by
    have hcoef : 100000000*(envelope p K)^6 ≤ C := by dsimp [C]; omega
    have hmul := Nat.mul_le_mul (Nat.mul_le_mul_right ((n+1)^12) hcoef) hU
    have hh' : reserve d p (p^d) J ≤ 100000000*((envelope p K)^6*(n+1)^12*(U+1)^6) := hh
    apply hh'.trans
    simpa only [mul_pow,Nat.mul_assoc] using hmul
  have hC : C ≤ 2^Nat.size C := (Nat.lt_size_self C).le
  have hneed : reserve d p (p^d) J ≤ polyBound (Nat.size C) 12 [n,U] := by
    apply hbig.trans
    simpa only [polyBound,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,Nat.mul_one] using
      Nat.mul_le_mul_right (((n+1)*(U+1))^12) hC
  have hdepth : 15 ≤ polyBound (Nat.size C) 12 [n,U] := by
    have h1 : 1 ≤ ((n+1)*(U+1))^12 := Nat.one_le_pow _ _ (by exact Nat.mul_pos (by omega) (by omega))
    have h15 : 15 ≤ C := by dsimp [C]; omega
    have hm := Nat.mul_le_mul_left (2^Nat.size C) h1
    have hmono := h15.trans hC
    simp only [polyBound,List.map_cons,List.map_nil,List.prod_cons,List.prod_nil,mul_one]
    omega
  exact ⟨hneed,hneed,hdepth⟩

end ThreeSum.LightExtensionBackendSetup
