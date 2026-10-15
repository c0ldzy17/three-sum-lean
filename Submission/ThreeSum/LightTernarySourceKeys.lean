import Submission.ThreeSum.LightTernaryLookup
import Submission.ThreeSum.LightHistogram

/-!
# Compact histogram keys from the actual source join

Each join record consists of an original position and a dictionary index.
The dictionary index selects its canonical word code. The actual binary
search converts that code to the compact bank ordinal. Every join record
is visited, including records with equal values or equal word codes.
-/

namespace ThreeSum.LightTernarySourceKeys

open Light ThreeSum.LightSubsetAddress

set_option maxHeartbeats 2000000

variable {lim : Limits} {P : Program}

def roundBody (pSearch : ℕ) : Stmt :=
  .call pSearch [v 0,v 1,M (v 6 +' M (v 4 +' k 2 *' v 9 +' k 1)),
    v 2,v 3,k 0] 10 ;;
  .store (v 8 +' v 9) (v 10 -' k 1)

/-- Arguments: bank codes/count, powers, search width, interleaved join
records/count, dictionary word codes/count, destination compact keys. -/
def body (pSearch : ℕ) : Stmt := .for 9 (v 5) (roundBody pSearch)

def time (L count : ℕ) : ℕ := count*(LightBandLookup.searchTime L+200)+20

def Inv (μ : ℕ → ℤ) (a bank powers L pairs count words wordCount dst : ℕ)
    (key : ℕ → ℕ) (j : ℕ) (σ : State) : Prop :=
  ∃ r : ℤ, σ = ⟨frame [a,bank,powers,L,pairs,count,words,wordCount,dst,j,r],
    wrote μ dst (fun i => (key i : ℤ)) j⟩

theorem meets {pMain pSearch a bank powers W L pairs count words wordCount dst d : ℕ}
    (hmain : P[pMain]? = some (body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (position key : ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+bank ≤ dst) (hpair : pairs+2*count ≤ dst)
    (hwords : words+wordCount ≤ dst) (hpows : powers+(W+1) ≤ dst)
    (hdst : dst+count ≤ lim.space)
    (hword : ((bank+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hcodes : ∀ i < bank, μ (a+i) = (codes i : ℤ))
    (hpairRead : ∀ i < count, μ (pairs+2*i+1) = (position i : ℤ))
    (hposition : ∀ i < count, position i < wordCount)
    (hwordRead : ∀ i < count, μ (words+position i) = (codes (key i) : ℤ))
    (hkey : ∀ i < count, key i < bank)
    (hcodeBound : ∀ i < bank, codes i < 2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k)
    (hL : L ≤ W) (hn : bank < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,bank,powers,L,pairs,count,words,wordCount,dst] μ
      (time L count) (fun _ μ' =>
        (∀ i < count, μ' (dst+i) = (key i : ℤ)) ∧ SameOutside μ μ' dst count) := by
  apply Meets.of_body hmain
  unfold body time
  refine Ends.for (Inv μ a bank powers L pairs count words wordCount dst key)
    count (LightBandLookup.searchTime L+185) ?start ?round ?done ?bound
    (hT := by light_time)
  case start =>
    refine ⟨0,?_⟩
    simp [Inv,update_frame_setLocal,wrote_zero]
    change frame [(a : ℤ),bank,powers,L,pairs,count,words,wordCount,dst,0] =
      frame ([(a : ℤ),bank,powers,L,pairs,count,words,wordCount,dst,0] ++ [0])
    exact (frame_append_zeros _ 1).symm
  case round =>
    rintro j _ hj _ ⟨r,rfl⟩
    let μj := wrote μ dst (fun i => (key i : ℤ)) j
    have hkeep : ∀ x < dst, μj x = μ x := by
      intro x hx
      exact wrote_rest (Or.inl hx)
    have hcodesj : ∀ i < bank, μj (a+i) = (codes i : ℤ) := by
      intro i hi
      rw [hkeep _ (by omega),hcodes i hi]
    have hpairj : μj (pairs+2*j+1) = (position j : ℤ) := by
      rw [hkeep _ (by omega),hpairRead j hj]
    have hwordj : μj (words+position j) = (codes (key j) : ℤ) := by
      rw [hkeep _ (by have hh := hposition j hj; omega),hwordRead j hj]
    have hp : Powers μj powers W := by
      intro i hi
      rw [hkeep _ (by omega),hpowers i hi]
    have hsort : ∀ i k, i < k → k < bank →
        (codes i : ℤ) < (codes k : ℤ) := by
      intro i k hik hk
      exact_mod_cast hsorted i k hik hk
    have hc := LightTernaryLookup.code_meets (d := d+1) hsearch μj
      (fun i => (codes i : ℤ)) hw (by omega) (by omega) hword hcodesj hp hsort
      (hkey j hj) hL hn (by omega)
    have hpj := hposition j hj
    have hkj := hkey j hj
    have hcb := hcodeBound (key j) hkj
    have hpow : 2^W ≤ 2^(W+1) := Nat.pow_le_pow_right (by decide) (by omega)
    have hcodeWord : (codes (key j) : ℤ) ≤ lim.word := by
      have hh : codes (key j) ≤ bank+2^(W+1)+16 := by omega
      exact (Int.ofNat_le.mpr hh).trans hword
    have hpairAddr : ((pairs : ℤ)+2*(j : ℤ)+1).toNat = pairs+2*j+1 := by
      norm_cast
    have hwordAddr : ((words : ℤ)+(position j : ℤ)).toNat = words+position j := by
      norm_cast
    unfold roundBody
    light_call hc using μj,hpairAddr,hwordAddr,hpairj,hwordj,
      LightBandLookup.searchTime with out μ' ⟨hout,hmem⟩
    subst μ'
    light_store (dst+j) (key j : ℕ) using hout,LightBandLookup.searchTime
    refine ⟨by simp,out,?_⟩
    simp [Inv,update_frame_setLocal,wrote_succ,μj]
  case done =>
    rintro _ _ ⟨r,rfl⟩
    refine ⟨?_,?_⟩
    · intro j hj
      change wrote μ dst (fun i => (key i : ℤ)) count (dst+j) = (key j : ℤ)
      exact wrote_done hj
    · intro x hx
      change wrote μ dst (fun i => (key i : ℤ)) count x = μ x
      exact wrote_rest hx
  case bound =>
    rintro j _ hj _ ⟨r,rfl⟩
    light_side

def program : Program := [body 1,LightBandLookup.searchBody 1]

theorem time_bound (L count : ℕ) : time L count ≤ 500*(L+1)*(count+1) := by
  unfold time LightBandLookup.searchTime
  nlinarith

end ThreeSum.LightTernarySourceKeys
