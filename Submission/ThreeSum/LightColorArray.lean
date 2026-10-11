import Submission.ThreeSum.LightColorIndex
import Submission.ThreeSum.LightSubsetAddress

/-!
# Building the color of every original array position

The program constructs its own binary-power table and evaluates one selected
two-coordinate coloring on every index. No index-bit or coloring oracle is
part of the input. Memory outside the output colors and scratch is preserved.
-/

namespace ThreeSum.LightColorArray

open Light LightSubsetAddress

set_option maxHeartbeats 1200000

def body (pPowers pColor : ℕ) : Stmt :=
  .call pPowers [v 9,v 0 +' k 1,k 2] 10 ;;
  .for 11 (v 1) (
    .call pColor [v 0,v 11,v 2,v 3,v 4,v 5,v 6,v 7,v 9] 12 ;;
    .store (v 8 +' v 11) (v 12))

def time (W n : ℕ) : ℕ := powTableTime (W+1)+n*(LightColorIndex.time W+100)+100

def Inv {W : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (n dst work : ℕ) (powRet : ℤ) (j : ℕ) (σ : State) : Prop :=
  ∃ (r : ℤ) (ν : ℕ → ℤ),
    σ = ⟨frame [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,
      dst,work,powRet,j,r],ν⟩ ∧
    (∀ i < j, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
    Powers ν work W ∧ KeptBut μ ν work dst n

variable {lim : Limits} {P : Program} {d : ℕ}

theorem meets {pMain pPowers pColor pErase W n dst work : ℕ}
    (hmain : P[pMain]? = some (body pPowers pColor))
    (hpowers : P[pPowers]? = some powTableBody)
    (hcolor : P[pColor]? = some (LightColorIndex.body pErase))
    (herase : P[pErase]? = some (LightMaskErase.body pErase))
    (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hdst : dst+n ≤ work) (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hd : d+W+2 ≤ lim.depth) :
    Meets lim P pMain d [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,dst,work]
      μ (time W n) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
        Powers ν work W ∧ KeptBut μ ν work dst n) := by
  have htwo : (2 : ℤ) ≤ lim.word := by
    have hh : 2^1 ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    exact (by exact_mod_cast hh : (2 : ℤ) ≤ ((2^(W+1) : ℕ) : ℤ)).trans hword
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (d := d+1) (μ := μ) (dst := work) (L := W+1) (b := 2)
    hpowers hw hspace (by
      intro i hi
      exact (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) hi)).trans hword)
  light_call hp using LightColorIndex.time,LightMaskErase.time with powRet ν₀ ⟨pow,keep₀⟩
  have pow₀ : Powers ν₀ work W := powers_of_segment pow
  refine Ends.for (Inv μ p n dst work powRet) n (LightColorIndex.time W+90)
    ?start ?round ?done ?bound (hT := by light_time [LightColorIndex.time,LightMaskErase.time])
  case start =>
    refine ⟨0,ν₀,?_,?_,pow₀,?_⟩
    · simp [update_frame_setLocal]
      exact (frame_append_zeros _ 1).symm
    · intro i hi
      omega
    · intro a ha
      exact keep₀ a (Or.inl ha.1)
  case round =>
    rintro j _ hj _ ⟨r,ν,rfl,written,pows,kept⟩
    have hc := LightColorIndex.meets (d := d+1) (m := j) (powers := work)
      hcolor herase ν p hw hspace hword pows (by omega) (by omega)
    light_call hc using LightColorIndex.time,LightMaskErase.time with r' ν' ⟨hr,hmem⟩
    subst ν'
    have hcLt := LightColorIndex.color_lt p j
    have hcWord : (LightColorIndex.color p j : ℤ) ≤ lim.word := by omega
    light_store (dst+j) (LightColorIndex.color p j : ℕ) using hr,LightColorIndex.time,LightMaskErase.time
    refine ⟨by simp,r',Function.update ν (dst+j) (LightColorIndex.color p j : ℤ),
      by simp [update_frame_setLocal],?_,?_,?_⟩
    · intro i hi
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi | rfl
      · rw [Function.update_of_ne (by omega)]
        exact written i hi
      · simp
    · intro i hi
      rw [Function.update_of_ne (by omega)]
      exact pows i hi
    · intro a ha
      rw [Function.update_of_ne (by omega)]
      exact kept a ha
  case done =>
    rintro _ _ ⟨r,ν,rfl,written,pows,kept⟩
    exact ⟨written,pows,kept⟩
  case bound =>
    rintro j _ hj _ ⟨r,ν,rfl,_,_,_⟩
    light_side

def program : Program :=
  [body 1 2,powTableBody,LightColorIndex.body 3,LightMaskErase.body 3]

theorem program_meets {W n dst work : ℕ} (μ : ℕ → ℤ) (p : Coloring.Parameter W)
    (hw : (lim.space : ℤ) ≤ lim.word) (hn : n ≤ 2^W)
    (hdst : dst+n ≤ work) (hspace : work+(W+1) ≤ lim.space)
    (hword : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word) (hd : d+W+2 ≤ lim.depth) :
    Meets lim program 0 d [W,n,p.1.1.val,p.1.2.val,(p.2 (false,false)).val,
      (p.2 (false,true)).val,(p.2 (true,false)).val,(p.2 (true,true)).val,dst,work]
      μ (time W n) (fun _ ν =>
        (∀ i < n, ν (dst+i) = (LightColorIndex.color p i : ℤ)) ∧
        Powers ν work W ∧ KeptBut μ ν work dst n) :=
  meets rfl rfl rfl rfl μ p hw hn hdst hspace hword hd

theorem time_bound (W n : ℕ) : time W n ≤ 600*(W+1)*(n+1) := by
  unfold time powTableTime LightColorIndex.time LightMaskErase.time
  nlinarith

end ThreeSum.LightColorArray
