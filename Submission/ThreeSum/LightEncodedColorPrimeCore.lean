import Submission.ThreeSum.EncodedColorPrimeData

/-!
# Actual common-prime construction with its reusable metadata retained

The verified depth, prime-pool and common-chain programs each run once.
Six header cells retain their controls before the pool and prefix arrays;
all temporary scoring memory follows the exact returned next-free pointer.
-/

namespace ThreeSum.LightEncodedColorPrimeCore

open Light BandCandidateRows EncodedColorPrimeData

set_option maxHeartbeats 2600000
set_option maxRecDepth 13000

def body (pDepth pPool pChain : ℕ) : Stmt :=
  .call pDepth [v 9,v 10] 12 ;;
  .set 13 (v 11 +' k 6) ;;
  .call pPool [v 10,v 13] 14 ;;
  .set 15 (v 13 +' k 3 *' v 10) ;;
  .call pChain [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 13,v 14,v 12,v 15] 16 ;;
  .set 17 (v 15 +' v 12 +' k 1) ;;
  .store (v 11) (v 16) ;;
  .store (v 11 +' k 1) (v 12) ;;
  .store (v 11 +' k 2) (v 17) ;;
  .store (v 11 +' k 3) (v 13) ;;
  .store (v 11 +' k 4) (v 14) ;;
  .store (v 11 +' k 5) (v 15) ;;
  .set 0 (v 16)

def poolProgram : Program := ReportingHostRelocation.program LightBandPrimeDepth.program LightPrimePool.program
def joinedProgram : Program := ReportingHostRelocation.program poolProgram LightBandPrimeChain.program
def program : Program := joinedProgram ++ [body 0 1 22]

theorem program_length : program.length=24 := rfl

def time (maxMod g count M y U : ℕ) : ℕ :=
  LightBandPrimeDepth.time M y+LightPrimePool.time y+
    LightBandPrimeChain.time maxMod g count (LightPrimePool.size y) U (LightBandPrimeDepth.depth M y)+1000

def space (free maxMod g M y U : ℕ) : ℕ :=
  max (LightPrimePool.space (poolBase free) y)
    (LightBandPrimeChain.space (prefixBase free y) maxMod g U (LightBandPrimeDepth.depth M y))

def word (maxMod nA nB nC g count M y U : ℕ) : ℕ :=
  max (LightBandPrimeDepth.word M y)
    (max (LightPrimePool.word y)
      (LightBandWeightedScore.word maxMod nA nB nC g count (LightPrimePool.size y) U))

variable {lim : Limits} {d : ℕ} {μ : ℕ → ℤ}
    {a b c nA nB nC g recs M y free maxMod U : ℕ}

theorem program_meets (rs : List Record)
    (hw : (lim.space : ℤ) ≤ lim.word) (hy : 0 < y) (hg : 0 < g)
    (ha : a+nA ≤ free) (hb : b+nB ≤ free) (hc : c+nC ≤ free)
    (hrecs : recs+4*rs.length ≤ free)
    (hspace : space free maxMod g M y U ≤ lim.space)
    (hword : (word maxMod nA nB nC g rs.length M y U : ℤ) ≤ lim.word)
    (hd : d+Nat.clog 2 maxMod+9 ≤ lim.depth)
    (hrecords : Seg μ recs (cells rs))
    (hflag : ∀ r ∈ rs, r.flag=0 ∨ r.flag=1)
    (hvalid : ∀ r ∈ rs, r.flag=1 → r.a*g ≤ nA ∧ r.b*g ≤ nB ∧ r.c*g ≤ nC)
    (hA : ∀ i < nA, |μ (a+i)| ≤ (U : ℤ))
    (hB : ∀ i < nB, |μ (b+i)| ≤ (U : ℤ))
    (hC : ∀ i < nC, |μ (c+i)| ≤ (U : ℤ))
    (hmax : (4*y)^(LightBandPrimeDepth.depth M y+1) ≤ maxMod) :
    Meets lim program 23 d [a,b,c,nA,nB,nC,g,recs,rs.length,M,y,free] μ
      (time maxMod g rs.length M y U)
      (fun result ν =>
        result=(LightBandPrimeConstruction.modulus y nA nB nC g
          (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs (LightBandPrimeDepth.depth M y) : ℤ) ∧
        EncodedColorPrimeData.Stored ν free M y
          (LightBandPrimeConstruction.modulus y nA nB nC g
            (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs) ∧
        Kept μ ν free) := by
  let qs := LightBandPrimeConstruction.modulus y nA nB nC g
    (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs
  have hdWord : (LightBandPrimeDepth.word M y : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (le_max_left _ _)).trans hword
  have hpWord : (LightPrimePool.word y : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_left _ _).trans (le_max_right _ _))).trans hword
  have hcWord : (LightBandWeightedScore.word maxMod nA nB nC g rs.length (LightPrimePool.size y) U : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr ((le_max_right _ _).trans (le_max_right _ _))).trans hword
  have hpSpace : LightPrimePool.space (poolBase free) y ≤ lim.space := (le_max_left _ _).trans hspace
  have hcSpace : LightBandPrimeChain.space (prefixBase free y) maxMod g U (LightBandPrimeDepth.depth M y) ≤ lim.space :=
    (le_max_right _ _).trans hspace
  have hpoolEnd : free+6+3*y ≤ lim.space := by unfold LightPrimePool.space poolBase at hpSpace; omega
  have hnext : nextFree free M y ≤ lim.space := by
    have hh := (le_max_right _ _).trans hcSpace
    change prefixBase free y+LightBandPrimeDepth.depth M y+1+(Nat.log 2 (maxMod+1)+2) ≤ lim.space at hh
    exact (Nat.le_add_right _ _).trans hh
  have hnext' : free+6+3*y+LightBandPrimeDepth.depth M y+1 ≤ lim.space := hnext
  have hnextAddress : prefixBase free y+LightBandPrimeDepth.depth M y+1 ≤ lim.space := hnext
  have hsize := LightPrimePool.size_le y
  have hmaxWord : (maxMod : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (LightBandPrimeMinimum.maxMod_le_word maxMod nA nB nC g rs.length (LightPrimePool.size y) U)).trans hcWord
  have hqBound := (LightBandPrimeConstruction.modulus_bounds (nA := nA) (nB := nB) (nC := nC) (g := g)
    (fun j => μ (a+j)) (fun j => μ (b+j)) (fun j => μ (c+j)) rs (LightBandPrimeDepth.depth M y) hy).2
  have hqMax : qs (LightBandPrimeDepth.depth M y) ≤ maxMod := hqBound.trans
    ((Nat.pow_le_pow_right (by omega : 1 ≤ 4*y) (Nat.le_succ _)).trans hmax)
  have hqWord : (qs (LightBandPrimeDepth.depth M y) : ℤ) ≤ lim.word := (Int.ofNat_le.mpr hqMax).trans hmaxWord
  apply Meets.of_body (p := 23) (by rfl : program[23]?=some (body 0 1 22))
  unfold body time
  have hDepth := (((LightBandPrimeDepth.program_meets (d := d+1) (μ := μ) hy hdWord).append
    (LightPrimePool.program.map (ReportingHostRelocation.relocate 1))).append
    (LightBandPrimeChain.program.map (ReportingHostRelocation.relocate 4))).append [body 0 1 22]
  light_call hDepth with levels μ₀ ⟨hlevels,hmem⟩
  subst μ₀
  light_set (poolBase free : ℕ) using poolBase
  have hPool := ((ReportingHostRelocation.meets
    (LightPrimePool.program_meets (d := d+1) (μ := μ) (y := y) (free := poolBase free)
      hw (by omega) hy hpSpace hpWord) LightBandPrimeDepth.program).append
      (LightBandPrimeChain.program.map (ReportingHostRelocation.relocate 4))).append [body 0 1 22]
  light_call hPool with count μ₁ ⟨hcount,hpool,keepPool⟩
  subst count
  light_set (prefixBase free y : ℕ) using prefixBase,poolBase
  have records₁ : Seg μ₁ recs (cells rs) := by
    apply hrecords.congr
    intro i hi
    rw [cells_length] at hi
    exact keepPool _ (by unfold poolBase; omega)
  have valuesA₁ : ∀ i < nA, |μ₁ (a+i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold poolBase; omega)]; exact hA i hi
  have valuesB₁ : ∀ i < nB, |μ₁ (b+i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold poolBase; omega)]; exact hB i hi
  have valuesC₁ : ∀ i < nC, |μ₁ (c+i)| ≤ (U : ℤ) := by
    intro i hi; rw [keepPool _ (by unfold poolBase; omega)]; exact hC i hi
  have hChain := (ReportingHostRelocation.meets
    (LightBandPrimeChain.program_meets (d := d+1) (μ := μ₁) (aux := poolBase free) (free := prefixBase free y)
      (Y := 4*y) (LightPrimePool.prime y) rs hw (LightPrimePool.size_pos hy) hg
      (by unfold prefixBase poolBase; omega) (by unfold prefixBase poolBase; omega)
      (by unfold prefixBase poolBase; omega) (by unfold prefixBase poolBase; omega)
      (by unfold prefixBase; omega) hcSpace hcWord (by omega)
      records₁ hflag hvalid valuesA₁ valuesB₁ valuesC₁
      (fun i hi => hpool.read hi) (fun i hi => (LightPrimePool.prime_spec hi).1)
      (fun i hi j hj heq => LightPrimePool.prime_injective hi hj heq)
      (fun i hi => (LightPrimePool.prime_spec hi).2.2) hmax) poolProgram).append [body 0 1 22]
  light_call hChain using hlevels with result μ₂ ⟨hresult,hprefix,keepChain⟩
  have hmod (i : ℕ) : BandPrimeChoice.modulus (LightPrimePool.prime y) (LightPrimePool.size y)
      nA nB nC g (fun j => μ₁ (a+j)) (fun j => μ₁ (b+j)) (fun j => μ₁ (c+j)) rs i=qs i :=
    BandPrimeChoice.modulus_congr rs (fun j hj => keepPool _ (by unfold poolBase; omega))
      (fun j hj => keepPool _ (by unfold poolBase; omega)) (fun j hj => keepPool _ (by unfold poolBase; omega)) i
  have hresult' : result=(qs (LightBandPrimeDepth.depth M y) : ℤ) := by rw [hresult,hmod]
  light_set (nextFree free M y : ℕ) using nextFree,hlevels
  light_store free (qs (LightBandPrimeDepth.depth M y) : ℕ) using hresult'
  light_store (free+1) (LightBandPrimeDepth.depth M y : ℕ) using hlevels
  light_store (free+2) (nextFree free M y : ℕ)
  light_store (free+3) (poolBase free : ℕ) using poolBase
  light_store (free+4) (LightPrimePool.size y : ℕ)
  light_store (free+5) (prefixBase free y : ℕ) using prefixBase,poolBase
  light_set (qs (LightBandPrimeDepth.depth M y) : ℕ) using hresult'
  refine ⟨rfl,⟨?_,?_,?_⟩,?_⟩
  · intro i hi
    have hi' : i < 6 := by simpa only [values,List.length_cons,List.length_nil] using hi
    interval_cases i <;> simp [values,qs]
  · dsimp only
    apply hpool.congr
    intro i hi
    have hi' : i < LightPrimePool.size y := by simpa only [LightPrimePool.size,List.length_map] using hi
    repeat' rw [Function.update_of_ne (by unfold poolBase; omega)]
    exact keepChain _ (by unfold prefixBase; omega)
  · intro i hi
    dsimp only
    repeat' rw [Function.update_of_ne (by unfold prefixBase poolBase; omega)]
    exact (hprefix i hi).trans (congrArg Int.ofNat (hmod i))
  · intro i hi
    dsimp only
    repeat' rw [Function.update_of_ne (by omega)]
    exact (keepChain i (by unfold prefixBase poolBase; omega)).trans (keepPool i (by unfold poolBase; omega))

end ThreeSum.LightEncodedColorPrimeCore
