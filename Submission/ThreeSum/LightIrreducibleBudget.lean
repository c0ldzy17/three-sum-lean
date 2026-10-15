import Submission.ThreeSum.LightIrreducibleFinder

namespace ThreeSum.LightIrreducibleFinder
open Light
set_option maxHeartbeats 3000000

def uniformFactorTime (d p q : ℕ) : ℕ :=
  q*q*(2*LightCoefficientDecode.time (2*d) (2*q)+
    LightPolynomialProductCheck.time (d+1) p (2*d)+700)+100

def uniformFactorWord (d p q : ℕ) : ℕ :=
  2*LightCoefficientDecode.word (2*d) p (2*q) 0 1+
    20*((d+2)*(p+1)^2+3*d+11)+200

theorem factorTime_le_uniform (C : LightExtensionFactorPredicate.Layout) (q e : ℕ)
    (hp : 1 ≤ C.p) (he : e ≤ C.dim) (hq : C.p^C.dim=q) :
    factorTime C q e ≤ uniformFactorTime C.dim C.p q := by
  have hpe : C.p^e ≤ q := by rw [←hq]; exact Nat.pow_le_pow_right hp he
  have hpr : C.p^(C.dim-e) ≤ q := by rw [←hq]; exact Nat.pow_le_pow_right hp (Nat.sub_le _ _)
  have hA : LightCoefficientDecode.time (2*C.dim) (q+C.p^e) ≤
      LightCoefficientDecode.time (2*C.dim) (2*q) := by
    unfold LightCoefficientDecode.time LightRadixDigit.time
    gcongr <;> omega
  have hR : LightCoefficientDecode.time (2*C.dim) (q+C.p^(C.dim-e)) ≤
      LightCoefficientDecode.time (2*C.dim) (2*q) := by
    unfold LightCoefficientDecode.time LightRadixDigit.time
    gcongr <;> omega
  have hCheck : LightPolynomialProductCheck.time (e+1) C.p (2*C.dim) ≤
      LightPolynomialProductCheck.time (C.dim+1) C.p (2*C.dim) := by
    unfold LightPolynomialProductCheck.time LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time
    gcongr
  unfold factorTime uniformFactorTime LightExtensionFactorPredicate.time LightExtensionFactorCheck.time atDegree
  dsimp only
  apply Nat.add_le_add_right
  apply Nat.mul_le_mul_left
  omega

theorem factorWord_le_uniform (C : LightExtensionFactorPredicate.Layout) (q e : ℕ)
    (hp : 1 ≤ C.p) (he : e ≤ C.dim) (hq : C.p^C.dim=q) :
    LightExtensionFactorPredicate.word (atDegree C e) q q ≤ uniformFactorWord C.dim C.p q := by
  have hpe : C.p^e ≤ q := by rw [←hq]; exact Nat.pow_le_pow_right hp he
  have hpr : C.p^(C.dim-e) ≤ q := by rw [←hq]; exact Nat.pow_le_pow_right hp (Nat.sub_le _ _)
  have hm := Nat.mul_le_mul_right ((C.p+1)^2) (show e+2 ≤ C.dim+2 by omega)
  unfold LightExtensionFactorPredicate.word LightExtensionFactorCheck.word
    uniformFactorWord LightCoefficientDecode.word atDegree
  dsimp only
  omega

theorem setupTime_polynomial (C : LightExtensionFactorPredicate.Layout) (q : ℕ) :
    setupTime C q (uniformFactorTime C.dim C.p q) ≤ 1000000000*(C.dim+C.p+q+2)^10 := by
  let B := C.dim+C.p+q+2
  let D : LightExtensionFactorPredicate.Layout := {C with dim := B,p := B}
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : C.dim ≤ B := by dsimp [B]; omega
  have hp : C.p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hm : setupTime C q (uniformFactorTime C.dim C.p q) ≤ setupTime D B (uniformFactorTime B B B) := by
    unfold setupTime searchTime candidateTime degreeTime uniformFactorTime powTableTime
      LightCoefficientDecode.time LightPolynomialProductCheck.time
      LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time LightRadixDigit.time
    dsimp only [D]
    gcongr
  apply hm.trans
  change setupTime D B (uniformFactorTime B B B) ≤ 1000000000*B^10
  have h0 : 1 ≤ B^10 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^10 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 10 by decide)
  have h2 : B^2 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h4 : B^4 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h5 : B^5 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h6 : B^6 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h7 : B^7 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h8 : B^8 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have h9 : B^9 ≤ B^10 := Nat.pow_le_pow_right hB (by decide)
  have hupper : setupTime D B (uniformFactorTime B B B) ≤
      17*(2*B+1)+8+
      (B*(LightCoefficientDecode.time (2*B) (2*B)+
        (B*(uniformFactorTime B B B+200)+100)+200+200)+100)+
      LightCoefficientDecode.time (2*B) (2*B)+300 := by
    unfold setupTime searchTime candidateTime degreeTime powTableTime
    dsimp only [D]
    gcongr
    exact Nat.sub_le _ _
  apply hupper.trans
  unfold uniformFactorTime LightCoefficientDecode.time LightPolynomialProductCheck.time
    LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time LightRadixDigit.time
  ring_nf
  omega


theorem uniformFactorWord_polynomial (d p q : ℕ) (hsize : p^d=q) :
    uniformFactorWord d p q ≤ 1000000*(d+p+q+2)^4 := by
  let B := d+p+q+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : d ≤ B := by dsimp [B]; omega
  have hp : p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hpow : p^(2*d+1)=q*q*p := by
    rw [show 2*d+1=d+d+1 by omega,pow_succ,pow_add,hsize]
  let E := fun d p q : ℕ => 8*(2*q+q*q*p+p+2*d+3)+20*((d+2)*(p+1)^2+3*d+11)+200
  have he : uniformFactorWord d p q=E d p q := by
    unfold uniformFactorWord LightCoefficientDecode.word E
    rw [hpow]
    ring
  rw [he]
  have hm : E d p q ≤ E B B B := by unfold E; gcongr
  apply hm.trans
  change E B B B ≤ 1000000*B^4
  have h0 : 1 ≤ B^4 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^4 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 4 by decide)
  have h2 : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  unfold E
  ring_nf
  omega

end ThreeSum.LightIrreducibleFinder
