import Submission.ThreeSum.TernaryColoredLoopAllocation

noncomputable section
namespace ThreeSum.TernaryColoredLoopAllocationScalars
open Light TernaryConcreteProfile TernaryColoredLoopSetup TernaryColoredLoopAllocation
open TernaryArenaPrefixFootprints TernaryLocalParameters TernaryArenaLayout
set_option maxHeartbeats 200000
set_option maxRecDepth 24000
variable {κ : ℕ}

def values (P : Profile κ) (n : ℕ) : List ℕ :=
  [P.m,P.F,P.p,fixedAlpha P.m 2,TernaryArenaSourceSetup.alphaRank P.m,
    TernaryCodeSemantics.address P.output.val,4^fixedLength P.m,P.p^(2*P.K),
    9*TernaryArenaBudgetExistence.pairFactor P.m P.F P.K,P.scale,J P n,rounds P n]

/-- All constants and dimensions passed to the actual loop call are paid by
the initialized header/budget footprints, without independent scalar advice. -/
theorem sum_word {lim : Limits} {depth : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hok : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ((values P n).sum : ℤ)≤lim.word := by
  let Z:=numbers P.maps P.threshold P.cap P.M P.radix P.K P.H P.drift P.scale n (n^κ) 0
  let T:=cells P n
  have HF : Fits T Z := P.allocation.fits n (n^κ) 0 (Nat.zero_le _)
  have hhead:=HF.prefixHeader
  have hprefix:=HF.prefixCells
  have hbudget:=HF.budgets
  have hJ : rounds P n≤J P n := by
    unfold rounds J LightTernaryDimensions.J TernarySignedPadding.paddedLength
    omega
  have haddress:=(TernaryCodeSemantics.address_lt P.output.val).le
  have hbasic : P.m+P.p+fixedAlpha P.m 2+TernaryArenaSourceSetup.alphaRank P.m+
      4^fixedLength P.m+J P n≤T := by
    dsimp only [Z,numbers] at hhead
    simp only [pow_zero,Nat.zero_mul,Nat.mul_zero,Nat.add_zero,one_mul] at hhead
    change _+LightTernaryDimensions.J P.M P.radix n (n^κ)≤T
    have hR : (0 : ℤ)≤((4 : ℕ):ℤ)^fixedLength P.m := by positivity
    omega
  have hF : P.F≤T := by
    dsimp only [Z,numbers] at hprefix
    simp only [pow_zero,Nat.zero_mul,Nat.mul_zero,one_mul,mul_one] at hprefix
    omega
  have hfixed : P.p^(2*P.K)+P.drift+P.scale≤T := by
    dsimp only [Z,numbers] at hbudget
    simp only [pow_zero,one_mul] at hbudget
    unfold LightTernaryInitialBudgets.word at hbudget
    omega
  have hsum : (values P n).sum≤12*T := by
    have hv : ∀z∈values P n,z≤T := by
      intro z hz
      simp only [values,List.mem_cons,List.not_mem_nil,or_false] at hz
      rw [beta_eq_drift] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals omega
    have hh:=List.sum_le_card_nsmul (values P n) T hv
    have hlen : (values P n).length=12 := rfl
    rw [hlen] at hh
    norm_num only [nsmul_eq_mul,Nat.cast_ofNat] at hh
    exact hh
  have hC : 12*T≤1000*T := by omega
  have hw:=hok.word
  change (1000*T : ℕ)≤lim.word at hw
  exact (Int.ofNat_le.mpr (hsum.trans hC)).trans hw

theorem member_word {lim : Limits} {depth : ℕ} (P : Profile κ) (n free : ℕ) (A B C : List ℤ)
    (hok : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ∀z∈values P n, |(z : ℤ)|≤lim.word := by
  intro z hz
  have hh:=List.le_sum_of_mem hz
  have hw:=sum_word P n free A B C hok
  rw [abs_of_nonneg (by positivity)]
  exact (Int.ofNat_le.mpr hh).trans hw

private theorem sum12 (a b c d e f g h i j k l : ℕ) :
    ([a,b,c,d,e,f,g,h,i,j,k,l] : List ℕ).sum =
      a+b+c+d+e+f+g+h+i+j+k+l := by
  simp only [List.sum_cons,List.sum_nil,Nat.add_zero,←Nat.add_assoc]

/-- Exact scalar sum used by the actual initialized-loop call. Keeping
this arithmetic statement independent of the extension avoids re-elaborating
its field instances merely to bound twelve integer constants. -/
theorem scalar_expression_word {lim : Limits} {depth : ℕ} (P : Profile κ)
    (n free : ℕ) (A B C : List ℤ)
    (hok : (TernaryArenaAllocationResources.need P.allocation n (n^κ)).Ok lim
      (input P n free A B C).free depth) :
    ((P.m+P.F+P.p+fixedAlpha P.m 2+TernaryArenaSourceSetup.alphaRank P.m+
      TernaryCodeSemantics.address P.output.val+4^fixedLength P.m+P.p^(2*P.K)+
      9*TernaryArenaBudgetExistence.pairFactor P.m P.F P.K+P.scale+J P n+rounds P n : ℕ):ℤ)≤lim.word := by
  rw [←sum12]
  exact sum_word P n free A B C hok

end ThreeSum.TernaryColoredLoopAllocationScalars
