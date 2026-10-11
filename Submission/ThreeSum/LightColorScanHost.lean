import Submission.ThreeSum.LightColorScan
import Submission.ThreeSum.LightParameterInit

/-! # Load the actual index width and run the entire coloring family -/

namespace ThreeSum.LightColorScanHost

open Light ColorParameters LightColorParametersCosts

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000

def body (pScan : ℕ) : Stmt :=
  .set 4 (M (v 2) +' k 1) ;;
  .set 5 (k 81 *' v 4 *' v 4) ;;
  .call pScan [v 0,v 1,v 2,v 3,v 4,v 5] 0

def time (colorTime n : ℕ) : ℕ :=
  LightColorScan.time colorTime (width n) (count (width n))+100

def word (n : ℕ) : ℕ := n+count (width n)+width n+100

theorem parameters_bits {n params : ℕ} {μ : ℕ → ℤ}
    (H : Seg μ params (LightParameterInit.values n)) : μ params=(Scales.inputBits n : ℤ) := by
  have hh := H 0 (by simp [LightParameterInit.values,LightScales.values])
  simpa [LightParameterInit.values,LightScales.values] using hh

structure Procs (P : Program) (pMain : ℕ) where
  pScan : ℕ
  scan : LightColorScan.Procs P pScan
  main : P[pMain]?=some (body pScan)

variable {lim : Limits} {P : Program}

theorem Procs.meets {pMain src n params free colorTime colorDepth d : ℕ}
    (R : Procs P pMain) (x : Fin n → ℤ) (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : free+6 ≤ lim.space) (hsrc : src ≤ free) (hparams : params < free)
    (hword : (word n : ℤ) ≤ lim.word)
    (hd : d+count (width n)+colorDepth+4 ≤ lim.depth)
    (hread : μ params=(Scales.inputBits n : ℤ))
    (hcolor : ∀ (i : ℕ) (hi : i < count (width n)) (ν : ℕ → ℤ),
      Kept μ ν free → Seg ν free (fields (parameter hi)) →
      ∀ dd : ℕ, dd+colorDepth ≤ lim.depth →
      Meets lim P R.scan.pColor dd [src,n,params,free,free+6] ν colorTime
        (fun r ξ => (r=0 ∨ r=1) ∧
          (r=1 ↔ ColorClassLists.witness (parameter hi) x) ∧ Kept ν ξ free)) :
    Meets lim P pMain d [src,n,params,free] μ (time colorTime n)
      (fun r ξ => (r=0 ∨ r=1) ∧
        (r=1 ↔ Coloring.DistinctZeroSum x) ∧ Kept μ ξ free) := by
  have hWpos : 0 < width n := by unfold width; omega
  have hprod : 81*width n ≤ count (width n) := by
    unfold count
    have hh := Nat.le_mul_of_pos_right (width n) hWpos
    nlinarith
  have hcount : (count (width n) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (by unfold word; omega)).trans hword
  have hprodWord : (81 : ℤ)*(width n : ℤ) ≤ lim.word := by
    exact (by exact_mod_cast hprod : (81 : ℤ)*(width n : ℤ) ≤ (count (width n) : ℤ)).trans hcount
  have hfull : (81 : ℤ)*(width n : ℤ)*(width n : ℤ)=(count (width n) : ℤ) := by
    simp only [count,pow_two,Nat.cast_mul,Nat.cast_ofNat]
    ring
  have hbits : (Scales.inputBits n : ℤ)+1=(width n : ℤ) := by simp [width]
  apply Meets.of_body R.main
  unfold body time
  light_set (width n : ℕ) using hread,hbits,word,LightColorScan.time
  light_set (count (width n) : ℕ) using hfull,hprodWord,word,LightColorScan.time
  have hs := R.scan.meets x μ hw hspace hsrc hparams.le hword hcolor
    (d := d+1) (t := count (width n)) (ν := μ) le_rfl (by omega) SameOn.refl
  light_call hs using LightColorScan.time with result ξ ⟨hbool,hresult,hkeep⟩
  exact ⟨hbool,hresult.trans (ColorScan.hit_complete x (width_sufficient n)),hkeep⟩

end ThreeSum.LightColorScanHost
