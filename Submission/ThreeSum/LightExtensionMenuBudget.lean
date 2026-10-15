import Submission.ThreeSum.LightExtensionMenuMatrix

namespace ThreeSum.LightExtensionMenuMatrix
set_option maxHeartbeats 3000000

/-- The actual decoder, exhaustive quotient checks, table writes, seed recurrence,
and physical row permutations have one fixed polynomial cost. -/
theorem time_polynomial (C : LightExtensionQuotientPredicate.Layout) (q J : ℕ) :
    time C q J ≤ 1000000000*(C.dim+C.p+q+J+2)^8 := by
  let B := C.dim+C.p+q+J+2
  let D : LightExtensionQuotientPredicate.Layout := { C with p := B, dim := B }
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : C.dim ≤ B := by dsimp [B]; omega
  have hp : C.p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hJ : J ≤ B := by dsimp [B]; omega
  have hm : time C q J ≤ time D B B := by
    unfold time LightExtensionMultiplyTable.time LightExtensionMultiplyCell.time
      LightExtensionMultiplyCell.searchTime LightExtensionQuotientPredicate.time
      LightCoefficientDecode.time LightRadixDigit.time LightPolynomialQuotientCheck.time
      LightPolynomialProductArray.time LightPolynomialProductCheck.time
      LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time
      LightPrimeAddArray.time LightPrimeCoefficient.mulAddTime LightExtensionSeedMatrix.time
      LightExtensionSeedRow.time LightSignedCoefficientMatrix.time LightSignedCoefficientLayout.time LightRadixDigit.time
    dsimp only [D]
    gcongr
  apply hm.trans
  change time D B B ≤ 1000000000*B^8
  have h0 : 1 ≤ B^8 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^8 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 8 by decide)
  have h2 : B^2 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h4 : B^4 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h5 : B^5 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h6 : B^6 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  have h7 : B^7 ≤ B^8 := Nat.pow_le_pow_right hB (by decide)
  unfold time LightExtensionMultiplyTable.time LightExtensionMultiplyCell.time
    LightExtensionMultiplyCell.searchTime LightExtensionQuotientPredicate.time
    LightCoefficientDecode.time LightRadixDigit.time LightPolynomialQuotientCheck.time
    LightPolynomialProductArray.time LightPolynomialProductCheck.time
    LightPolynomialCoefficient.reducedTime LightPolynomialCoefficient.time
    LightPrimeAddArray.time LightPrimeCoefficient.mulAddTime LightExtensionSeedMatrix.time
    LightExtensionSeedRow.time LightSignedCoefficientMatrix.time LightSignedCoefficientLayout.time LightRadixDigit.time
  dsimp only [D]
  ring_nf
  omega


/-- Powers used by the literal coefficient decoder are polynomial in the actual field size. -/
theorem cell_word_polynomial (C : LightExtensionQuotientPredicate.Layout) (q ctx : ℕ)
    (hsize : C.p^C.dim=q) :
    LightExtensionMultiplyCell.word C q ctx ≤ 1000000*(C.dim+C.p+q+ctx+2)^4 := by
  let B := C.dim+C.p+q+ctx+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hd : C.dim ≤ B := by dsimp [B]; omega
  have hp : C.p ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hctx : ctx ≤ B := by dsimp [B]; omega
  have hpow1 : C.p^(C.dim+1)=q*C.p := by rw [pow_succ,hsize]
  have hpow2 : C.p^(2*C.dim+1)=q*q*C.p := by
    rw [show 2*C.dim+1=C.dim+C.dim+1 by omega,pow_succ,pow_add,hsize]
  let E := fun d p q ctx : ℕ =>
    8*(q+q*p+p+d+3)+4*(q+q*q*p+p+2*d+3)+
    100*((d+2)*(p+1)^2+4*d+p+20)+100+4*(q*q+q+3)+q*q+q+ctx+100
  have he : LightExtensionMultiplyCell.word C q ctx=E C.dim C.p q ctx := by
    unfold LightExtensionMultiplyCell.word LightExtensionQuotientPredicate.word
      LightCoefficientDecode.word LightPolynomialQuotientCheck.word LightRadixDigit.word E
    rw [hpow1,hpow2]
    ring
  rw [he]
  have hm : E C.dim C.p q ctx ≤ E B B B B := by unfold E; gcongr
  apply hm.trans
  change E B B B B ≤ 1000000*B^4
  have h0 : 1 ≤ B^4 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^4 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 4 by decide)
  have h2 : B^2 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  have h3 : B^3 ≤ B^4 := Nat.pow_le_pow_right hB (by decide)
  unfold E
  ring_nf
  omega


theorem seed_word_polynomial (q p J : ℕ) :
    LightExtensionSeedMatrix.word (J+2) q p ≤ 100000*(q+p+J+2)^3 := by
  let B := q+p+J+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hp : p ≤ B := by dsimp [B]; omega
  have hJ : J ≤ B := by dsimp [B]; omega
  have hm : LightExtensionSeedMatrix.word (J+2) q p ≤ LightExtensionSeedMatrix.word (B+2) B B := by
    unfold LightExtensionSeedMatrix.word
    gcongr
  apply hm.trans
  change LightExtensionSeedMatrix.word (B+2) B B ≤ 100000*B^3
  have h0 : 1 ≤ B^3 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^3 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 3 by decide)
  have h2 : B^2 ≤ B^3 := Nat.pow_le_pow_right hB (by decide)
  unfold LightExtensionSeedMatrix.word
  ring_nf
  omega

theorem table_word_polynomial (q ctx p dim powers a b : ℕ) :
    LightExtensionMultiplyTable.word q ctx p dim powers a b ≤
      100000*(q+ctx+p+dim+powers+a+b+2)^2 := by
  let B := q+ctx+p+dim+powers+a+b+2
  have hB : 1 ≤ B := by dsimp [B]; omega
  have hq : q ≤ B := by dsimp [B]; omega
  have hctx : ctx ≤ B := by dsimp [B]; omega
  have hp : p ≤ B := by dsimp [B]; omega
  have hd : dim ≤ B := by dsimp [B]; omega
  have hpw : powers ≤ B := by dsimp [B]; omega
  have ha : a ≤ B := by dsimp [B]; omega
  have hb : b ≤ B := by dsimp [B]; omega
  have hm : LightExtensionMultiplyTable.word q ctx p dim powers a b ≤
      LightExtensionMultiplyTable.word B B B B B B B := by
    unfold LightExtensionMultiplyTable.word
    gcongr
  apply hm.trans
  change LightExtensionMultiplyTable.word B B B B B B B ≤ 100000*B^2
  have h0 : 1 ≤ B^2 := Nat.one_le_pow _ _ hB
  have h1 : B ≤ B^2 := by simpa using Nat.pow_le_pow_right hB (show 1 ≤ 2 by decide)
  unfold LightExtensionMultiplyTable.word
  ring_nf
  omega


theorem cell_word_affine_ctx (C : LightExtensionQuotientPredicate.Layout) (q ctx : ℕ) :
    LightExtensionMultiplyCell.word C q ctx=ctx+LightExtensionMultiplyCell.word C q 0 := by
  unfold LightExtensionMultiplyCell.word
  omega

theorem cell_word_after_ctx (C : LightExtensionQuotientPredicate.Layout) (q ctx : ℕ)
    (hsize : C.p^C.dim=q) :
    LightExtensionMultiplyCell.word C q ctx ≤ ctx+1000000*(C.dim+C.p+q+2)^4 := by
  rw [cell_word_affine_ctx]
  apply Nat.add_le_add_left
  simpa using cell_word_polynomial C q 0 hsize

end ThreeSum.LightExtensionMenuMatrix
