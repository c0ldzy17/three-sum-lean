import Submission.ThreeSum.LightTernaryNearDigits
import Submission.ThreeSum.LightTernaryNearEnumerationMain
import Submission.ThreeSum.TernaryNearCanonical

/-! Actual per-query power table, canonical digits, active mask, and pruned near array. -/
namespace ThreeSum.LightTernaryNearSetup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.TernaryJointType ThreeSum.TernaryBankEnumeration ThreeSum.TernaryCodeSemantics

set_option maxHeartbeats 4000000
set_option maxRecDepth 12000

def body (pPowers pDigits pEnum : ℕ) : Stmt :=
  .call pPowers [v 4,k 2 *' v 0 +' k 1,k 2] 7 ;;
  .call pDigits [v 0,v 2,v 4,v 5,v 6] 7 ;;
  .call pEnum [v 0,v 1,k 0,v 3,v 4,v 5] 0

def time {N : ℕ} (Q : TritWord N) (D : ℕ) : ℕ := powTableTime (2*N+1)+
  LightTernaryNearDigits.time N+LightTernaryNearEnumeration.time (wordList Q) D+300

variable {lim : Limits} {P : Program}

theorem meets {pMain pPowers pDigits pDigit pErase pEnum pBranch N D dst powers caps active d : ℕ}
    (hmain : P[pMain]?=some (body pPowers pDigits pEnum))
    (hpowers : P[pPowers]?=some powTableBody)
    (hdigits : P[pDigits]?=some (LightTernaryNearDigits.body pDigit))
    (hdigit : P[pDigit]?=some (LightTernaryCodes.digitBody pErase))
    (herase : P[pErase]?=some (LightMaskErase.body pErase))
    (henum : P[pEnum]?=some (LightTernaryNearEnumeration.body pBranch))
    (hbranch : P[pBranch]?=some (LightTernaryNearEnumeration.branchBody pEnum))
    (μ : ℕ → ℤ) (Q : TritWord N)
    (hw : (lim.space : ℤ)≤lim.word) (hspace : powers+(2*N+1)≤lim.space)
    (hword : ((4^(N+1) : ℕ) : ℤ)≤lim.word)
    (hD : D≤2*N)
    (hdst : dst+(TernaryNearEnumeration.codes (wordList Q) D).length≤caps)
    (hcaps : caps+N≤active) (hactive : active+N≤powers)
    (hd : d+2*N+3≤lim.depth) :
    Meets lim P pMain d [N,D,address Q,dst,powers,caps,active] μ (time Q D)
      (fun r ν => r=((TernaryNearEnumeration.codes (wordList Q) D).length : ℤ) ∧
        Seg ν dst ((TernaryNearEnumeration.codes (wordList Q) D).map (fun c => (c : ℤ))) ∧
        Powers ν powers (2*N) ∧ (∀ i<N, ν (active+i)=1) ∧ Kept μ ν dst) := by
  have hbase : (2 : ℤ)≤lim.word := by
    have hp : 0<(4 : ℕ)^N := by positivity
    have hb : (2 : ℕ)≤4^(N+1) := by rw [pow_succ]; omega
    exact (Int.ofNat_le.mpr hb).trans hword
  have hRows : (TernaryNearEnumeration.codes (wordList Q) D).length=
      (TernaryNearEnumeration.words (wordList Q) D).length := TernaryNearEnumeration.codes_length _ _
  have hpowBound : ∀ j≤2*N+1, ((2^j : ℕ) : ℤ)≤lim.word := by
    intro j hj
    have hle : 2^j≤4^(N+1) := by
      rw [←LightTernaryEnumeration.pow_two_even]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Int.ofNat_le.mpr hle).trans hword
  have hpow := powTable_meets (d := d+1) (μ := μ) (dst := powers) (L := 2*N+1) (b := 2)
    hpowers hw hspace hpowBound
  apply Meets.of_body hmain
  unfold body time
  light_call hpow using powTableTime,LightTernaryNearDigits.time,LightTernaryNearEnumeration.time
    with rp ν ⟨hPowSeg,hPowOutside⟩
  have hPowers := powers_of_segment hPowSeg
  have hdCall := LightTernaryNearDigits.meets (d := d+1) hdigits hdigit herase ν hw hspace (hpowBound _ le_rfl)
    (address_lt_pow_two Q) hcaps hactive hPowers (by omega)
  light_call hdCall using powTableTime,LightTernaryNearDigits.time,LightTernaryNearEnumeration.time
    with rd ξ ⟨hCaps,hActive,hDigitsOutside⟩
  have hSpan : caps+(active+N-caps)=active+N := Nat.add_sub_of_le (by omega)
  have hPowers' : Powers ξ powers (2*N) := by
    intro i hi
    rw [hDigitsOutside _ (Or.inr (by omega))]
    exact hPowers i hi
  have hCapsSeg : Seg ξ caps ((wordList Q).map (fun q => (q : ℤ))) := by
    intro i hi
    have hin : i<N := by simpa only [List.bind_eq_flatMap,List.pure_def,←List.map_eq_flatMap,List.length_map,wordList_length] using hi
    have he : LightTernaryRank.digitAt N (address Q) i=(Q ⟨i,hin⟩).val := digit_eq Q ⟨i,hin⟩
    simpa [List.bind_eq_flatMap,List.pure_def,←List.map_eq_flatMap,wordList,List.getElem_map,he] using hCaps i hin
  have hEnumCall := LightTernaryNearEnumerationMain.meets henum hbranch hw hspace hword
    (wordList Q) D 0 dst caps ξ (wordList_digits Q) (by simp) hD (by simp)
    (by omega) (by omega) (by simp; omega) hPowers' hCapsSeg (d+1) (by simp only [wordList_length]; omega)
  light_call hEnumCall using powTableTime,LightTernaryNearDigits.time,LightTernaryNearEnumeration.time,wordList_length
    with result η ⟨hCount,hSeg,hEnumOutside⟩
  refine ⟨?_,?_,?_,?_,?_⟩
  · change result=((TernaryNearEnumeration.codes (wordList Q) D).length : ℤ)
    simpa only [←hRows] using hCount
  · simpa [LightTernaryNearEnumeration.output,TernaryNearEnumeration.codes_eq_map,List.bind_eq_flatMap,List.pure_def,←List.map_eq_flatMap,List.map_map,Function.comp_def] using hSeg
  · intro i hi
    change η (powers+i)=_
    rw [hEnumOutside _ (Or.inr (by omega))]
    exact hPowers' i hi
  · intro i hi
    change η (active+i)=1
    rw [hEnumOutside _ (Or.inr (by omega))]
    exact hActive i hi
  · intro x hx
    change η x=μ x
    rw [hEnumOutside _ (Or.inl hx),hDigitsOutside _ (Or.inl (by omega)),hPowOutside _ (Or.inl (by omega))]

theorem time_bound {N : ℕ} (Q : TritWord N) (D : ℕ) :
    time Q D≤3000*(N+1)^2*((TernaryNearEnumeration.codes (wordList Q) D).length+1) := by
  have he := LightTernaryNearEnumerationMain.time_bank_bound Q D
  rw [←TernaryNearBankEnumeration.codes_length_eq_nearWords_card Q D] at he
  unfold time LightTernaryNearDigits.time LightTernaryCodes.digitTime LightMaskErase.time powTableTime
  nlinarith only [he, Nat.zero_le (TernaryNearEnumeration.codes (wordList Q) D).length]

/-- Seven procedures, including the power-table and exact digit extraction. -/
def program : Program := [body 1 2 5,powTableBody,LightTernaryNearDigits.body 3,
  LightTernaryCodes.digitBody 4,LightMaskErase.body 4,
  LightTernaryNearEnumeration.body 6,LightTernaryNearEnumeration.branchBody 5]

@[simp] theorem program_length : program.length=7 := rfl

def program_meets {lim : Limits} {N D dst powers caps active d : ℕ} :=
  meets (lim := lim) (N := N) (D := D) (dst := dst) (powers := powers) (caps := caps) (active := active) (d := d)
    (P := program) (pMain := 0) (pPowers := 1) (pDigits := 2) (pDigit := 3) (pErase := 4)
    (pEnum := 5) (pBranch := 6) rfl rfl rfl rfl rfl rfl rfl

end ThreeSum.LightTernaryNearSetup
