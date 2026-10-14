import Submission.ThreeSum.LightBandLookup
import Submission.ThreeSum.LightTernaryCell

/-!
# Actual logarithmic compact-bank address lookup

The bank's word codes occupy a strictly increasing memory segment. The
existing division-free machine search returns the compact ordinal of a
present code using a power-of-two table. The ambient numeric code range is
never scanned.
-/

namespace ThreeSum.LightTernaryLookup

open Light ThreeSum.LightSubsetAddress

theorem code_partition {n j : ℕ} (f : ℕ → ℤ) (hj : j < n)
    (hsorted : ∀ i k, i < k → k < n → f i < f k) :
    ThreeSum.BinarySearch.Partition f (f j) n (j + 1) := by
  refine ⟨by omega, ?_, ?_⟩
  · intro i hi
    by_cases hij : i = j
    · subst i
      rfl
    · exact (hsorted i j (by omega) hj).le
  · intro i hi hin
    exact hsorted j i (by omega) hin

variable {lim : Limits} {P : Program}

theorem code_meets {pSearch a n powers W L j d : ℕ}
    (hprog : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (f : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = f i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → f i < f k)
    (hj : j < n) (hL : L ≤ W) (hn : n < 2^L) (hd : d+L ≤ lim.depth) :
    Meets lim P pSearch d [a,n,f j,powers,L,0] μ (LightBandLookup.searchTime L)
      (fun r μ' => r = ((j+1 : ℕ) : ℤ) ∧ μ' = μ) :=
  LightBandLookup.search_meets hprog μ f (j+1) hw ha hspace hword hread hpowers
    (code_partition f hj hsorted) L 0 hL (by omega) (by omega) d hd

def body (pSearch pCell : ℕ) : Stmt :=
  .call pSearch [v 0,v 1,v 5,v 2,v 3,k 0] 9 ;;
  .call pSearch [v 0,v 1,v 6,v 2,v 3,k 0] 10 ;;
  .call pSearch [v 0,v 1,v 7,v 2,v 3,k 0] 11 ;;
  .call pCell [v 4,v 8 +' v 9 -' k 1,v 8 +' v 10 -' k 1,
    v 8 +' v 11 -' k 1] 0

def time (L : ℕ) : ℕ := 3 * LightBandLookup.searchTime L +
  LightTernaryCell.time + 150

/-- Three lower code lookups followed by the actual ternary value kernel.
For digits zero/one, irrelevant higher addresses can duplicate a lower code.
-/
theorem zeta_meets {pMain pSearch pCell a n powers W L src j0 j1 j2 d U : ℕ}
    (hmain : P[pMain]? = some (body pSearch pCell))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hcell : P[pCell]? = some LightTernaryCell.zetaBody)
    (μ : ℕ → ℤ) (codes : ℕ → ℤ) (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hsrc : src+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = codes i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k)
    (hj0 : j0 < n) (hj1 : j1 < n) (hj2 : j2 < n)
    (hr0 : μ (src+j0) = f 0) (hr1 : μ (src+j1) = f 1)
    (hr2 : μ (src+j2) = f 2)
    (hf : ∀ e, |f e| ≤ U) (hvalue : 4 * (U : ℤ) + 3 ≤ lim.word)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,n,powers,L,q.val,codes j0,codes j1,codes j2,src]
      μ (time L) (fun r μ' => r = ThreeSum.TernaryQuery.zetaDigit f q ∧ μ' = μ) := by
  have hc0 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted
    hj0 hL hn (d := d+1) (by omega)
  have hc1 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted
    hj1 hL hn (d := d+1) (by omega)
  have hc2 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted
    hj2 hL hn (d := d+1) (by omega)
  have hc := LightTernaryCell.zeta_meets (d := d+1) hcell q f hw
    (a0 := src+j0) (a1 := src+j1) (a2 := src+j2)
    (by omega) (by omega) (by omega) hr0 hr1 hr2 hf hvalue
  have ha0 : (src : ℤ)+((j0+1 : ℕ) : ℤ)-1 = ((src+j0 : ℕ) : ℤ) := by omega
  have ha1 : (src : ℤ)+((j1+1 : ℕ) : ℤ)-1 = ((src+j1 : ℕ) : ℤ) := by omega
  have ha2 : (src : ℤ)+((j2+1 : ℕ) : ℤ)-1 = ((src+j2 : ℕ) : ℤ) := by omega
  apply Meets.of_body hmain
  unfold body time
  light_call hc0 using LightBandLookup.searchTime,LightTernaryCell.time
    with r0 μ0 ⟨h0,hm0⟩
  subst μ0
  light_call hc1 using LightBandLookup.searchTime,LightTernaryCell.time
    with r1 μ1 ⟨h1,hm1⟩
  subst μ1
  light_call hc2 using LightBandLookup.searchTime,LightTernaryCell.time
    with r2 μ2 ⟨h2,hm2⟩
  subst μ2
  light_call hc using h0,h1,h2,ha0,ha1,ha2,
    LightBandLookup.searchTime,LightTernaryCell.time with r μ' ⟨hr,hm⟩
  exact ⟨hr,hm⟩

theorem inverse_meets {pMain pSearch pCell a n powers W L src j0 j1 j2 d U : ℕ}
    (hmain : P[pMain]? = some (body pSearch pCell))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hcell : P[pCell]? = some LightTernaryCell.inverseBody)
    (μ : ℕ → ℤ) (codes : ℕ → ℤ) (q : Fin 3) (f : Fin 3 → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+n ≤ lim.space) (hsrc : src+n ≤ lim.space)
    (hspace : powers+(W+1) ≤ lim.space)
    (hword : ((n+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hread : ∀ i < n, μ (a+i) = codes i)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < n → codes i < codes k)
    (hj0 : j0 < n) (hj1 : j1 < n) (hj2 : j2 < n)
    (hr0 : μ (src+j0) = f 0) (hr1 : μ (src+j1) = f 1)
    (hr2 : μ (src+j2) = f 2)
    (hf : ∀ e, |f e| ≤ U) (hvalue : 4 * (U : ℤ) + 3 ≤ lim.word)
    (hL : L ≤ W) (hn : n < 2^L) (hd : d+L+1 ≤ lim.depth) :
    Meets lim P pMain d [a,n,powers,L,q.val,codes j0,codes j1,codes j2,src]
      μ (time L) (fun r μ' => r = ThreeSum.TernaryQuery.inverseDigit f q ∧ μ' = μ) := by
  have hc0 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted
    hj0 hL hn (d := d+1) (by omega)
  have hc1 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted
    hj1 hL hn (d := d+1) (by omega)
  have hc2 := code_meets hsearch μ codes hw ha hspace hword hread hpowers hsorted
    hj2 hL hn (d := d+1) (by omega)
  have hc := LightTernaryCell.inverse_meets (d := d+1) hcell q f hw
    (a0 := src+j0) (a1 := src+j1) (a2 := src+j2)
    (by omega) (by omega) (by omega) hr0 hr1 hr2 hf hvalue
  have ha0 : (src : ℤ)+((j0+1 : ℕ) : ℤ)-1 = ((src+j0 : ℕ) : ℤ) := by omega
  have ha1 : (src : ℤ)+((j1+1 : ℕ) : ℤ)-1 = ((src+j1 : ℕ) : ℤ) := by omega
  have ha2 : (src : ℤ)+((j2+1 : ℕ) : ℤ)-1 = ((src+j2 : ℕ) : ℤ) := by omega
  apply Meets.of_body hmain
  unfold body time
  light_call hc0 using LightBandLookup.searchTime,LightTernaryCell.time
    with r0 μ0 ⟨h0,hm0⟩
  subst μ0
  light_call hc1 using LightBandLookup.searchTime,LightTernaryCell.time
    with r1 μ1 ⟨h1,hm1⟩
  subst μ1
  light_call hc2 using LightBandLookup.searchTime,LightTernaryCell.time
    with r2 μ2 ⟨h2,hm2⟩
  subst μ2
  light_call hc using h0,h1,h2,ha0,ha1,ha2,
    LightBandLookup.searchTime,LightTernaryCell.time with r μ' ⟨hr,hm⟩
  exact ⟨hr,hm⟩


def program : Program := [body 1 2, LightBandLookup.searchBody 1,
  LightTernaryCell.zetaBody]

theorem time_bound (L : ℕ) : time L ≤ 600 * (L+1) := by
  unfold time LightBandLookup.searchTime LightTernaryCell.time
  omega

end ThreeSum.LightTernaryLookup
