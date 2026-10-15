import Submission.ThreeSum.LightTernarySourceKeys

/-!
# Actual compact source-bank histogram

The machine converts every interleaved join record to a compact bank key,
clears and increments the histogram, and multiplies each cell by the
common factorial weight of this fixed source type. It never scans the
ambient canonical-code range.
-/

namespace ThreeSum.LightTernarySourceHistogram

open Light ThreeSum.LightArray ThreeSum.LightSubsetAddress

set_option maxHeartbeats 2000000

variable {lim : Limits} {P : Program} {d : ℕ}

def scaleBody : Stmt :=
  pass 3 (v 1) (v 0) (v 2 *' M (v 0 +' v 3))

def scaleTime (n : ℕ) : ℕ := 20*n+10

theorem scale_meets {p base n U : ℕ} (hp : P[p]? = some scaleBody)
    (μ : ℕ → ℤ) (weight : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base+n ≤ lim.space)
    (hvalues : ∀ j < n, |μ (base+j)| ≤ U)
    (hweight : (weight : ℤ) ≤ lim.word)
    (hword : (weight : ℤ)*(U : ℤ) ≤ lim.word) :
    Meets lim P p d [base,n,weight] μ (scaleTime n) (fun _ μ' =>
      (∀ j < n, μ' (base+j) = (weight : ℤ)*μ (base+j)) ∧
        SameOutside μ μ' base n) := by
  apply Meets.of_body hp
  unfold scaleBody scaleTime
  refine Ends.pass (fun j => (weight : ℤ)*μ (base+j)) (fun j hj => ?_)
    ⟨fun j hj => wrote_done (f := fun j => (weight : ℤ)*μ (base+j)) hj,
      by light_keep⟩ hw hbase rfl rfl (hT := by light_time)
  have hread := source_read (μ := μ) (f := fun j => (weight : ℤ)*μ (base+j))
    (show SourceSafe base base n from Or.inl rfl) hj
  have hprod : |(weight : ℤ)*μ (base+j)| ≤ (weight : ℤ)*(U : ℤ) := by
    rw [abs_mul,abs_of_nonneg (Int.natCast_nonneg weight)]
    exact mul_le_mul_of_nonneg_left (hvalues j hj) (Int.natCast_nonneg weight)
  have hb := abs_le.mp (hprod.trans hword)
  light_side [hread]

def body (pKeys pHist pScale : ℕ) : Stmt :=
  .call pKeys [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8] 11 ;;
  .call pHist [v 8,v 9,v 5,v 1] 11 ;;
  .call pScale [v 9,v 1,v 10] 11

def time (L count bank : ℕ) : ℕ := LightTernarySourceKeys.time L count +
  LightHistogram.histogramTime count bank + scaleTime bank + 200

theorem meets {pMain pKeys pHist pScale pSearch pFill a bank powers W L
    pairs count words wordCount keyBase valueBase : ℕ}
    (hmain : P[pMain]? = some (body pKeys pHist pScale))
    (hkeys : P[pKeys]? = some (LightTernarySourceKeys.body pSearch))
    (hsearch : P[pSearch]? = some (LightBandLookup.searchBody pSearch))
    (hhist : P[pHist]? = some (LightHistogram.histogramBody pFill))
    (hfill : P[pFill]? = some fillBody) (hscale : P[pScale]? = some scaleBody)
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (position key : ℕ → ℕ) (weight : ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (ha : a+bank ≤ keyBase) (hpair : pairs+2*count ≤ keyBase)
    (hwords : words+wordCount ≤ keyBase) (hpows : powers+(W+1) ≤ keyBase)
    (hkeysBefore : keyBase+count ≤ valueBase) (hvalues : valueBase+bank ≤ lim.space)
    (hword : ((bank+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hweight : (weight : ℤ) ≤ lim.word)
    (hweightedCount : (weight : ℤ)*(count : ℤ) ≤ lim.word)
    (hcodes : ∀ i < bank, μ (a+i) = (codes i : ℤ))
    (hpairRead : ∀ i < count, μ (pairs+2*i+1) = (position i : ℤ))
    (hposition : ∀ i < count, position i < wordCount)
    (hwordRead : ∀ i < count, μ (words+position i) = (codes (key i) : ℤ))
    (hkey : ∀ i < count, key i < bank)
    (hcodeBound : ∀ i < bank, codes i < 2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i < k → k < bank → codes i < codes k)
    (hL : L ≤ W) (hn : bank < 2^L) (hd : d+L+2 ≤ lim.depth) :
    Meets lim P pMain d
      [a,bank,powers,L,pairs,count,words,wordCount,keyBase,valueBase,weight] μ
      (time L count bank) (fun _ ν =>
        (∀ r < bank, ν (valueBase+r) =
          (weight : ℤ)*(LightHistogram.count key r count : ℤ)) ∧
        ∀ x, (x < keyBase ∨ keyBase+count ≤ x) →
          (x < valueBase ∨ valueBase+bank ≤ x) → ν x = μ x) := by
  have hk := LightTernarySourceKeys.meets (d := d+1) hkeys hsearch μ codes position key
    hw ha hpair hwords hpows (by omega) hword hcodes hpairRead hposition hwordRead
    hkey hcodeBound hpowers hsorted hL hn (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hk using LightTernarySourceKeys.time,LightHistogram.histogramTime,
    scaleTime with res μ₁ ⟨hkeyArray,hkeepKeys⟩
  have hh := LightHistogram.histogram_meets (d := d+1) hhist hfill key
    hw (by omega) (by omega) hvalues (by unfold Apart; omega) hkeyArray hkey
  light_call hh using LightTernarySourceKeys.time,LightHistogram.histogramTime,
    scaleTime with res μ₂ ⟨hcounts,hkeepHist⟩
  have hcountBound : ∀ j < bank, |μ₂ (valueBase+j)| ≤ count := by
    intro j hj
    rw [hcounts j hj,abs_of_nonneg (Int.natCast_nonneg _)]
    exact_mod_cast LightHistogram.count_le key j count
  have hs := scale_meets (d := d+1) hscale μ₂ weight hw hvalues hcountBound
    hweight hweightedCount
  light_call hs using LightTernarySourceKeys.time,LightHistogram.histogramTime,
    scaleTime with res ν ⟨hweighted,hkeepScale⟩
  refine ⟨?_,?_⟩
  · intro r hr
    change ν (valueBase+r) = (weight : ℤ)*(LightHistogram.count key r count : ℤ)
    rw [hweighted r hr,hcounts r hr]
  · intro x hx hy
    exact (hkeepScale x hy).trans ((hkeepHist x hy).trans (hkeepKeys x hx))

def program : Program := [body 1 3 5,LightTernarySourceKeys.body 2,
  LightBandLookup.searchBody 2,LightHistogram.histogramBody 4,fillBody,scaleBody]

theorem time_bound (L count bank : ℕ) :
    time L count bank ≤ 1000*(L+1)*(count+bank+1) := by
  have h := LightTernarySourceKeys.time_bound L count
  unfold time LightHistogram.histogramTime LightHistogram.countTime fillTime scaleTime
  nlinarith

end ThreeSum.LightTernarySourceHistogram
