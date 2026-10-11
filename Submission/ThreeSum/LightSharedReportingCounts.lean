import Submission.ThreeSum.SharedReportingBankLayout

/-! # Compute the two local combinatorial counts from an actual Pascal table -/

namespace ThreeSum.LightSharedReportingCounts

open Light LightPascal LightSubsetAddress SubsetAddress SharedReportingBankLayout

set_option maxHeartbeats 1700000
set_option maxRecDepth 9000

/-- h, two-cell count destination, Pascal scratch. -/
def body (pBuild : ℕ) : Stmt :=
  .set 3 (k 512 *' v 0) ;;
  .call pBuild [v 2,v 3] 4 ;;
  .set 5 (M (v 2 +' v 3 *' (v 3 +' k 1) +' v 0)) ;;
  .set 6 (M (v 2 +' v 3 *' (v 3 +' k 1) +' k 2 *' v 0)) ;;
  .set 7 (M (v 2 +' k 2 *' v 0 *' (v 3 +' k 1) +' v 0)) ;;
  .set 8 (v 6 *' v 7) ;;
  .store (v 1) (v 5) ;;
  .store (v 1 +' k 1) (v 8) ;;
  .set 0 (v 8)

def program : Program := [body 1,buildBody 2 3,fillBody,rowBody 4,LightArray.linearBody]
def time (h : ℕ) : ℕ := buildTime (512*h)+300

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {h dst work d : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (horder : dst+2 ≤ work)
    (hconstants : (512 : ℤ) ≤ lim.word)
    (hspace : work+tableSize (512*h) ≤ lim.space)
    (hpowWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hcountWord : (localPairs h : ℤ) ≤ lim.word) (hd : d+512*h+3 ≤ lim.depth) :
    Meets lim program 0 d [h,dst,work] μ (time h)
      (fun r ν => r=(localPairs h : ℤ) ∧ SegN ν dst [localChoose h,localPairs h] ∧ Kept μ ν dst) := by
  have hh : h ≤ 512*h := by omega
  have h2h : 2*h ≤ 512*h := by omega
  have hstride : 512*h+1 ≤ tableSize (512*h) := by unfold tableSize; nlinarith
  have hL : 512*h ≤ lim.space := by omega
  have hlocal : localChoose h ≤ 2^(512*h+1) :=
    (Nat.choose_le_two_pow (512*h) h).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hchoose2 : (512*h).choose (2*h) ≤ 2^(512*h+1) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  have hsplit : (2*h).choose h ≤ 2^(512*h+1) :=
    (Nat.choose_le_two_pow _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))
  apply Meets.of_body (p := 0) (by rfl : program[0]?=some (body 1))
  unfold body time
  light_set (512*h : ℕ)
  light_call (build_meets (P := program) (pBuild := 1) (pFill := 2) (pRow := 3) (pLinear := 4)
    (d := d+1) (dst := work) (L := 512*h) rfl rfl rfl rfl hw (by omega) hspace hpowWord)
    using buildTime,rowTime,LightArray.linearTime with result ν₁ ⟨htable,hkeepBuild⟩
  have hreadH := htable (512*h) le_rfl h hh
  have hreadE₁ := htable (512*h) le_rfl (2*h) h2h
  have hreadE₂ := htable (2*h) h2h h (by omega)
  have hcellH := cell_offset_lt (show 512*h ≤ 512*h from le_rfl) hh
  have hcellE₁ := cell_offset_lt (show 512*h ≤ 512*h from le_rfl) h2h
  have hcellE₂ := cell_offset_lt h2h hh
  have hrowNZ : (0 : ℤ) ≤ 512*(h : ℤ)*(512*(h : ℤ)+1) := by positivity
  have hrowAddr : (work : ℤ)+512*(h : ℤ)*(512*(h : ℤ)+1)+2*(h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work+512*h*(512*h+1)+2*h < lim.space by omega)
  have hgroupNZ : (0 : ℤ) ≤ 2*(h : ℤ)*(512*(h : ℤ)+1) := by positivity
  have hgroupAddr : (work : ℤ)+2*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast (show work+2*h*(512*h+1)+h < lim.space by omega)
  have hprod : ((512*h).choose (2*h) : ℤ)*((2*h).choose h : ℤ)=(localPairs h : ℤ) := by
    simp only [localPairs,localWidth,LightReportingPrefixArrays.localCount,Nat.cast_mul]
  have hprodNZ : (0 : ℤ) ≤ ((512*h).choose (2*h) : ℤ)*((2*h).choose h : ℤ) := by positivity
  have haH : ((work : ℤ)+(512*(h : ℤ))*(512*(h : ℤ)+1)+(h : ℤ)).toNat=
      work+(512*h)*(512*h+1)+h := by
    have he : (work : ℤ)+(512*(h : ℤ))*(512*(h : ℤ)+1)+(h : ℤ)=
        ((work+(512*h)*(512*h+1)+h : ℕ) : ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  have haE₁ : ((work : ℤ)+(512*(h : ℤ))*(512*(h : ℤ)+1)+2*(h : ℤ)).toNat=
      work+(512*h)*(512*h+1)+2*h := by
    have he : (work : ℤ)+(512*(h : ℤ))*(512*(h : ℤ)+1)+2*(h : ℤ)=
        ((work+(512*h)*(512*h+1)+2*h : ℕ) : ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  have haE₂ : ((work : ℤ)+2*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ)).toNat=
      work+2*h*(512*h+1)+h := by
    have he : (work : ℤ)+2*(h : ℤ)*(512*(h : ℤ)+1)+(h : ℤ)=
        ((work+2*h*(512*h+1)+h : ℕ) : ℤ) := by push_cast; ring
    rw [he,Int.toNat_natCast]
  light_set (localChoose h : ℕ) using hreadH,haH,localChoose,localWidth,
    buildTime,rowTime,LightArray.linearTime
  light_set ((512*h).choose (2*h) : ℕ) using hreadE₁,haE₁,
    buildTime,rowTime,LightArray.linearTime
  light_set ((2*h).choose h : ℕ) using hreadE₂,haE₂,
    buildTime,rowTime,LightArray.linearTime
  light_set (localPairs h : ℕ) using localPairs,localWidth,LightReportingPrefixArrays.localCount,
    buildTime,rowTime,LightArray.linearTime
  light_store dst (localChoose h : ℕ) using buildTime,rowTime,LightArray.linearTime
  light_store (dst+1) (localPairs h : ℕ) using buildTime,rowTime,LightArray.linearTime
  light_set (localPairs h : ℕ) using buildTime,rowTime,LightArray.linearTime
  refine ⟨by simp,?_,?_⟩
  · intro i hi
    have hi' : i < 2 := by simpa using hi
    interval_cases i <;> simp [SegN]
  · intro a ha
    change Function.update (Function.update ν₁ dst (localChoose h : ℤ)) (dst+1) (localPairs h : ℤ) a=μ a
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkeepBuild a (Or.inl (by omega))

theorem time_bound (h : ℕ) : time h ≤ 1500*(512*h+1)^2 := by
  have hb := buildTime_bound (512*h)
  unfold time
  nlinarith [Nat.one_le_pow' 2 (512*h)]

end ThreeSum.LightSharedReportingCounts
