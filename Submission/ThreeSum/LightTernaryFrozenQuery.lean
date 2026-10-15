import Submission.ThreeSum.LightTernaryQueryLookup
import Submission.ThreeSum.LightTernaryCodes
import Submission.ThreeSum.TernaryReconstruction

/-!
# Recursive frozen-coordinate query program

The program performs physical bank/memo lookups and uses the checked bit
deletion and digit routines. A coordinate branches only to digits actually
read by its inverse formula. The full recursive execution and global tree
cost contract is not asserted by this module; those are the remaining
integration obligation.
-/

namespace ThreeSum.LightTernaryFrozenQuery

open Light

/-- Child arguments preserve the physical bank/memo layout and freeze the
current coordinate by decrementing the remaining coordinate count. -/
def childArgs (code rankDrop : Expr) : List Expr :=
  [v 0,v 16,v 2 -' rankDrop,v 3,code,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12]

/-- Arguments: total trits, remaining coordinates, current rank, bank cutoff,
current code, bank code/count/value bases, near code/count/product bases,
powers base, lookup width. Bank values contain every suffix inverse stage.
-/
def body (pSelf pLookup pDigit pZero pErase : ℕ) : Stmt :=
  .ite (v 2 ≤' v 3)
    (.call pLookup [v 5,v 6,v 4,v 7,v 11,v 12,v 1] 0)
    (.ite (v 1 =' k 0)
      (.call pLookup [v 8,v 9,v 4,v 10,v 11,v 12,k 0] 0)
      (.set 16 (v 1 -' k 1) ;;
        .call pDigit [k 2 *' v 0,k 2 *' (v 0 -' v 1),
          k 2 *' (v 0 -' v 1) +' k 1,v 4,v 11] 13 ;;
        .call pZero [k 2 *' v 0,k 2 *' (v 0 -' v 1),
          k 2 *' (v 0 -' v 1) +' k 1,v 4,v 11] 14 ;;
        .call pErase [k 2 *' v 0,k 2 *' (v 0 -' v 1) +' k 1,
          v 4,k 2 *' v 0,v 11] 15 ;;
        .ite (v 13 =' k 0)
          (.call pSelf (childArgs (v 14) (k 0)) 0)
          (.ite (v 13 =' k 1)
            (.call pSelf (childArgs (v 14) (k 1)) 18 ;;
              .call pSelf (childArgs (v 15) (k 0)) 19 ;;
              .set 0 (v 19 -' v 18))
            (.call pSelf (childArgs (v 14) (k 2)) 18 ;;
              .call pSelf (childArgs (v 15) (k 1)) 19 ;;
              .call pSelf (childArgs (v 4) (k 0)) 20 ;;
              .set 0 (v 20 -' k 2 *' v 19 +' v 18)))))

def program : Program :=
  [body 0 1 3 4 5,LightTernaryQueryLookup.body 2,
    LightBandLookup.searchBody 2,LightTernaryCodes.digitBody 5,
    LightTernaryCodes.zeroBody 5,LightMaskErase.body 5]

theorem program_main : program[0]? = some (body 0 1 3 4 5) := rfl
theorem program_lookup : program[1]? = some (LightTernaryQueryLookup.body 2) := rfl
theorem program_search : program[2]? = some (LightBandLookup.searchBody 2) := rfl
theorem program_digit : program[3]? = some (LightTernaryCodes.digitBody 5) := rfl
theorem program_zero : program[4]? = some (LightTernaryCodes.zeroBody 5) := rfl
theorem program_erase : program[5]? = some (LightMaskErase.body 5) := rfl

def inputs (N K rank cut : ℕ) (code : ℤ)
    (bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ) : List ℤ :=
  [N,K,rank,cut,code,bankCodes,bankCount,bankValues,nearCodes,nearCount,nearValues,powers,L]

variable {lim : Limits} {P : Program}

/-- The bank exit is an actual procedure call to the checked physical lookup.
This closes the first base case of the recursive query execution contract.
-/
theorem bank_exit_meets {pMain pLookup pSelf pDigit pZero pErase d t : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (N K rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (code value : ℤ) (μ : ℕ → ℤ) (hbank : rank ≤ cut)
    (hone : 1 ≤ lim.word)
    (hcutWord : (cut : ℤ)+1 ≤ lim.word)
    (hargs : ∀ x ∈ inputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L, |x| ≤ lim.word)
    (hd : d+1 ≤ lim.depth)
    (hlookup : Meets lim P pLookup (d+1)
      [bankCodes,bankCount,code,bankValues,powers,L,K] μ t
      (fun r μ' => r=value ∧ μ'=μ)) :
    Meets lim P pMain d (inputs N K rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L) μ (t+80)
      (fun r μ' => r=value ∧ μ'=μ) := by
  have hr := abs_le.mp (hargs rank (by simp [inputs]))
  have ht := abs_le.mp (hargs cut (by simp [inputs]))
  have hb := abs_le.mp (hargs bankCodes (by simp [inputs]))
  have hn := abs_le.mp (hargs bankCount (by simp [inputs]))
  have hc := abs_le.mp (hargs code (by simp [inputs]))
  have hv := abs_le.mp (hargs bankValues (by simp [inputs]))
  have hp := abs_le.mp (hargs powers (by simp [inputs]))
  have hL := abs_le.mp (hargs L (by simp [inputs]))
  have hK := abs_le.mp (hargs K (by simp [inputs]))
  apply Meets.of_body hmain
  unfold body inputs
  refine Ends.iteLast (fun hyes => ?_) (fun hno => ?_) (by light_side)
  · light_call hlookup with r μ' hout
    exact hout
  · exfalso
    apply hno
    simpa using (show (rank : ℤ) ≤ (cut : ℤ) by exact_mod_cast hbank)

/-- The outside-bank terminal exit loads the full product from the near memo. -/
theorem memo_exit_meets {pMain pLookup pSelf pDigit pZero pErase d t : ℕ}
    (hmain : P[pMain]? = some (body pSelf pLookup pDigit pZero pErase))
    (N rank cut bankCodes bankCount bankValues nearCodes nearCount nearValues powers L : ℕ)
    (code value : ℤ) (μ : ℕ → ℤ) (hbank : cut < rank)
    (hone : 1 ≤ lim.word)
    (hcutWord : (cut : ℤ)+1 ≤ lim.word)
    (hargs : ∀ x ∈ inputs N 0 rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L, |x| ≤ lim.word)
    (hd : d+1 ≤ lim.depth)
    (hlookup : Meets lim P pLookup (d+1)
      [nearCodes,nearCount,code,nearValues,powers,L,0] μ t
      (fun r μ' => r=value ∧ μ'=μ)) :
    Meets lim P pMain d (inputs N 0 rank cut code bankCodes bankCount bankValues
      nearCodes nearCount nearValues powers L) μ (t+100)
      (fun r μ' => r=value ∧ μ'=μ) := by
  have hr := abs_le.mp (hargs rank (by simp [inputs]))
  have ht := abs_le.mp (hargs cut (by simp [inputs]))
  have hb := abs_le.mp (hargs nearCodes (by simp [inputs]))
  have hn := abs_le.mp (hargs nearCount (by simp [inputs]))
  have hc := abs_le.mp (hargs code (by simp [inputs]))
  have hv := abs_le.mp (hargs nearValues (by simp [inputs]))
  have hp := abs_le.mp (hargs powers (by simp [inputs]))
  have hL := abs_le.mp (hargs L (by simp [inputs]))
  have hzero := abs_le.mp (hargs 0 (by simp [inputs]))
  apply Meets.of_body hmain
  unfold body inputs
  light_if hyes hno : (rank : ℤ) ≤ (cut : ℤ)
  · exfalso
    omega
  · light_if hyes hno : (0 : ℤ) = 0
    · light_call hlookup with r μ' hout
      exact hout
    · exfalso
      exact hno rfl

end ThreeSum.LightTernaryFrozenQuery
