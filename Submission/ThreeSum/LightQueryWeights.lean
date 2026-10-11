import Submission.ThreeSum.QueryCoordinates
import Submission.ThreeSum.LightMaskErase

/-!
# Constructing the compact coordinate-weight table of a query mask

A width-sized scan tests each bit using the checked deletion routine and
appends the corresponding power of two. The output has one cell per set
bit, while the available buffer and scratch are only linear in the width.
-/

namespace ThreeSum.LightQueryWeights

open Light ThreeSum.SubsetAddress ThreeSum.MaskErase ThreeSum.LightSubsetAddress
open QueryCoordinates

variable {lim : Limits} {P : Program}

def roundBody (pErase : ℕ) : Stmt :=
  .call pErase [v 0,v 6,v 1,v 0,v 3] 7 ;;
  .ite (v 7 <' v 1)
    (.store (v 2 +' v 5) (M (v 3 +' v 6)) ;; .set 5 (v 5 +' k 1))
    .skip

/-- Arguments: ambient width, query mask, output base, power scratch base. -/
def body (pPowers pErase : ℕ) : Stmt :=
  .call pPowers [v 3,v 0 +' k 1,k 2] 4 ;;
  .set 5 (k 0) ;;
  .for 6 (v 0) (roundBody pErase) ;;
  .set 0 (v 5)

def time (W : ℕ) : ℕ := powTableTime (W+1)+W*(LightMaskErase.time W+100)+100

def Inv {W : ℕ} (μ : ℕ → ℤ) (Q : Finset (Fin W))
    (dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (μ' : ℕ → ℤ),
    σ = ⟨frame [W,subsetMask Q,dst,work,powRet,(positions Q j).length,j,r],μ'⟩ ∧
    SegN μ' dst (selectedPowers Q j) ∧ Powers μ' work W ∧
    KeptBut μ μ' work dst W

theorem meets {pMain pPowers pErase : ℕ}
    (hmain : P[pMain]? = some (body pPowers pErase))
    (hPowers : P[pPowers]? = some powTableBody)
    (hErase : P[pErase]? = some (LightMaskErase.body pErase))
    {μ : ℕ → ℤ} {W dst work d : ℕ} (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+W ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim P pMain d [W,subsetMask Q,dst,work] μ (time W)
      (fun r μ' => r = (Q.card : ℤ) ∧
        SegN μ' dst (selectedPowers Q W) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst W) := by
  have hbase : (2 : ℤ) ≤ lim.word := by
    have hh : (2^1 : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (d := d+1) (μ := μ) (dst := work)
    (L := W+1) (b := 2) hPowers hw hspace (by
      intro i hi
      have hh : (2^i : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) hi
      exact (by exact_mod_cast hh : ((2^i : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword)
  light_call hp using powTableTime,LightMaskErase.time with powRet μ₁ ⟨hpow,hkept⟩
  have hpowers := powers_of_segment hpow
  light_set (0 : ℕ) using powTableTime,LightMaskErase.time
  refine Ends.pieceThen (Ends.for
    (T := W*(LightMaskErase.time W+80)+20)
    (Q := Inv μ Q dst work powRet W)
    (Inv μ Q dst work powRet) W (LightMaskErase.time W+60)
    ?start ?round ?done ?bound (hT := by light_time)) ?after
  case start =>
    refine ⟨0,μ₁,?_,by simp [SegN],hpowers,?_⟩
    · simp [update_frame_setLocal]
      change frame [(W : ℤ),subsetMask Q,dst,work,powRet,0,0] =
        frame ([(W : ℤ),subsetMask Q,dst,work,powRet,0,0] ++ [0])
      exact (frame_append_zeros _ 1).symm
    · intro i hi
      exact hkept i (Or.inl hi.1)
  case round =>
    rintro j _ hj _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
    have hcBound := positions_length_le Q j
    have hc := LightMaskErase.meets hErase μ' hw hspace hword hpowers'
      W j (subsetMask Q) le_rfl (Nat.le_of_lt hj) (subsetMask_isMask Q).1
      (d+1) (by omega)
    unfold roundBody
    light_call hc using LightMaskErase.time with erased μ₂ ⟨herased,hmem⟩
    subst μ₂
    light_if hbit hnbit : (eraseMask W j (subsetMask Q) : ℤ) < (subsetMask Q : ℤ)
      using herased,LightMaskErase.time
    · have ha : (⟨j,hj⟩ : Fin W) ∈ Q :=
        (eraseMask_lt_iff Q ⟨j,hj⟩).mp (by exact_mod_cast hbit)
      have hnat : j ∈ natPositions Q := Finset.mem_map.mpr ⟨⟨j,hj⟩,ha,rfl⟩
      have hnext := selectedPowers_succ Q j
      rw [if_pos hnat] at hnext
      have hlen : (positions Q (j+1)).length = (positions Q j).length+1 := by
        rw [positions_succ,if_pos hnat]
        simp
      have hread := hpowers' j (Nat.le_of_lt hj)
      have hvalWord : ((2^j : ℕ) : ℤ) ≤ lim.word := by
        have hh : (2^j : ℕ) ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
        exact (by exact_mod_cast hh : ((2^j : ℕ) : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
      light_store (dst+(positions Q j).length) (2^j : ℕ) using LightMaskErase.time,hread
      light_set ((positions Q j).length+1 : ℕ) using LightMaskErase.time
      refine ⟨by simp,erased,
        Function.update μ' (dst+(positions Q j).length) ((2^j : ℕ) : ℤ),?_,?_,?_,?_⟩
      · simp [update_frame_setLocal,hlen]
      · rw [hnext]
        simpa only [selectedPowers_length] using SegN.snoc hseg (2^j)
      · intro i hi
        change Function.update μ' (dst+(positions Q j).length) ((2^j : ℕ) : ℤ) (work+i) = _
        rw [Function.update_of_ne (by omega)]
        exact hpowers' i hi
      · intro i hi
        change Function.update μ' (dst+(positions Q j).length) ((2^j : ℕ) : ℤ) i = _
        rw [Function.update_of_ne (by omega)]
        exact hkeep i hi
    · have ha : (⟨j,hj⟩ : Fin W) ∉ Q := by
        intro hh
        exact hnbit (by exact_mod_cast (eraseMask_lt_iff Q ⟨j,hj⟩).mpr hh)
      have hnat : j ∉ natPositions Q := by
        intro hh
        obtain ⟨i,hi,hij⟩ := Finset.mem_map.mp hh
        exact ha ((Fin.ext hij : i = ⟨j,hj⟩) ▸ hi)
      have hpos : positions Q (j+1) = positions Q j := by
        rw [positions_succ,if_neg hnat,List.append_nil]
      have hnext : selectedPowers Q (j+1) = selectedPowers Q j := by
        rw [selectedPowers_succ,if_neg hnat,List.append_nil]
      apply Ends.skip
      refine ⟨by simp,erased,μ',?_,?_,hpowers',hkeep⟩
      · simp [update_frame_setLocal,hpos]
      · rwa [hnext]
  case done =>
    intro σ _ h
    exact h
  case bound =>
    rintro j _ hj _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
    light_side
  case after =>
    rintro _ ⟨r,μ',rfl,hseg,hpowers',hkeep⟩
    have hc := positions_length_le Q W
    light_set (Q.card : ℕ) using positions_length
    exact ⟨by simp,hseg,hpowers',hkeep⟩

def program : Program := [body 1 2,powTableBody,LightMaskErase.body 2]

theorem program_meets {μ : ℕ → ℤ} {W dst work d : ℕ}
    (Q : Finset (Fin W))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdst : dst+W ≤ work)
    (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hd : d+W+1 ≤ lim.depth) :
    Meets lim program 0 d [W,subsetMask Q,dst,work] μ (time W)
      (fun r μ' => r = (Q.card : ℤ) ∧
        SegN μ' dst (selectedPowers Q W) ∧ Powers μ' work W ∧
        KeptBut μ μ' work dst W) :=
  meets rfl rfl rfl Q hw hdst hspace hword hd

theorem weights_of_segment {μ : ℕ → ℤ} {W dst : ℕ} {Q : Finset (Fin W)}
    (hseg : SegN μ dst (selectedPowers Q W)) :
    LightWeightedEnumeration.Weights μ dst Q.card (weights Q) := by
  intro i hi
  have hi' : i < (selectedPowers Q W).length := by simpa using hi
  simpa only [weights,List.getD_eq_getElem _ _ hi',List.getElem?_eq_getElem hi',Option.getD_some]
    using hseg.read hi'

theorem time_bound (W : ℕ) : time W ≤ 500*(W+1)^2 := by
  unfold time powTableTime LightMaskErase.time
  nlinarith

end ThreeSum.LightQueryWeights
