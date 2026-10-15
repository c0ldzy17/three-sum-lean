import Submission.ThreeSum.LightTernarySourceHistogram
import Submission.ThreeSum.LightTernaryGroupedSourceKeys
import Submission.ThreeSum.TernaryWeightedPhysicalSources

/-! Actual original-weight gathering and compact factorial source-bank construction. -/

namespace ThreeSum.LightTernaryGroupedSources

open Light ThreeSum.LightSubsetAddress

set_option maxHeartbeats 3000000

variable {lim : Limits} {P : Program} {d : ℕ}

def body (pKeys pHist pScale : ℕ) : Stmt :=
  .call pKeys [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 13,v 14] 15 ;;
  .call pHist [v 8,v 4,v 10,v 5,v 9,v 1 *' v 14,v 11] 15 ;;
  .call pScale [v 9,v 1 *' v 14,v 12] 15

def time (L count bank groups : ℕ) : ℕ := LightTernaryGroupedSourceKeys.time L count+
  LightTernaryWeightedHistogram.time count (groups*bank)+
  LightTernarySourceHistogram.scaleTime (groups*bank)+250

theorem meets {pMain pKeys pHist pScale pSearch pFill a bank powers W L
    pairs count words wordCount keyBase valueBase weightBase originalCount U groupBase groups : ℕ}
    (hmain : P[pMain]?=some (body pKeys pHist pScale))
    (hkeys : P[pKeys]?=some (LightTernaryGroupedSourceKeys.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (hhist : P[pHist]?=some (LightTernaryWeightedHistogram.body pFill))
    (hfill : P[pFill]?=some fillBody)
    (hscale : P[pScale]?=some LightTernarySourceHistogram.scaleBody)
    (μ : ℕ → ℤ) (codes : ℕ → ℕ) (dictionaryPosition originalPosition key group : ℕ → ℕ)
    (weight : ℕ → ℤ) (factor : ℕ)
    (hw : (lim.space : ℤ)≤lim.word)
    (ha : a+bank≤keyBase) (hpair : pairs+2*count≤keyBase)
    (hwords : words+wordCount≤keyBase) (hpows : powers+(W+1)≤keyBase)
    (hweightArray : weightBase+originalCount≤keyBase)
    (hgroupArray : groupBase+wordCount≤keyBase)
    (hgroupRead : ∀ i<count, μ (groupBase+dictionaryPosition i)=(group i : ℤ))
    (hgroupLt : ∀ i<count, group i<groups)
    (hgroupWord : ((groups*bank+1 : ℕ) : ℤ)≤lim.word)
    (hgroupSpace : groups*bank+1≤lim.space)
    (hkeysBefore : keyBase+count≤valueBase) (hvalues : valueBase+groups*bank≤lim.space)
    (hword : ((bank+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hfactor : (factor : ℤ)≤lim.word)
    (hweightedCount : (factor : ℤ)*(count*U : ℕ)≤lim.word)
    (hhistWord : ((count+1 : ℕ) : ℤ)*U≤lim.word)
    (hcodes : ∀ i<bank, μ (a+i)=(codes i : ℤ))
    (hpairRead : ∀ i<count, μ (pairs+2*i+1)=(dictionaryPosition i : ℤ))
    (hdictionaryPosition : ∀ i<count, dictionaryPosition i<wordCount)
    (hwordRead : ∀ i<count, μ (words+dictionaryPosition i)=(codes (key i) : ℤ))
    (hkey : ∀ i<count, key i<bank)
    (hcodeBound : ∀ i<bank, codes i<2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i<k → k<bank → codes i<codes k)
    (hposRead : ∀ i<count, μ (pairs+2*i)=(originalPosition i : ℤ))
    (hposLt : ∀ i<count, originalPosition i<originalCount)
    (hweightRead : ∀ i<count, μ (weightBase+originalPosition i)=weight i)
    (hweightBound : ∀ i<count, |weight i|≤U)
    (hL : L≤W) (hn : bank<2^L) (hd : d+L+2≤lim.depth) :
    Meets lim P pMain d
      [a,bank,powers,L,pairs,count,words,wordCount,keyBase,valueBase,
        weightBase,originalCount,factor,groupBase,groups] μ (time L count bank groups)
      (fun _ ν => (∀ r<groups*bank, ν (valueBase+r)=
        (factor : ℤ)*LightTernaryWeightedHistogram.total (fun i => group i*bank+key i) weight r count) ∧
        ∀ x, (x<keyBase ∨ keyBase+count≤x) →
          (x<valueBase ∨ valueBase+groups*bank≤x) → ν x=μ x) := by
  have hk := LightTernaryGroupedSourceKeys.meets (d := d+1) hkeys hsearch μ codes
    dictionaryPosition key group hw ha hpair hwords hpows hgroupArray hgroupRead
    hgroupLt hgroupWord hgroupSpace (by omega) hword hcodes
    hpairRead hdictionaryPosition hwordRead hkey hcodeBound hpowers hsorted hL hn (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hk using LightTernaryGroupedSourceKeys.time,LightTernaryWeightedHistogram.time,
    LightTernarySourceHistogram.scaleTime with res μ₁ ⟨hkeyArray,hkeepKeys⟩
  have hpos : ∀ i<count, μ₁ (pairs+2*i)=(originalPosition i : ℤ) := by
    intro i hi
    exact (hkeepKeys _ (Or.inl (by omega))).trans (hposRead i hi)
  have hweights : ∀ i<count, μ₁ (weightBase+originalPosition i)=weight i := by
    intro i hi
    exact (hkeepKeys _ (Or.inl (by have hh := hposLt i hi; omega))).trans (hweightRead i hi)
  have hgroupKey : ∀ i<count, group i*bank+key i<groups*bank := by
    intro i hi
    have hg := hgroupLt i hi
    have hk := hkey i hi
    nlinarith
  have hbg : (bank : ℤ)*(groups : ℤ)=((groups*bank : ℕ) : ℤ) := by push_cast; ring
  have hh := LightTernaryWeightedHistogram.meets (d := d+1) hhist hfill μ₁
    (fun i => group i*bank+key i) originalPosition weight hw (by omega) hkeysBefore (by omega) (by omega)
    hvalues hkeyArray hpos hweights hgroupKey hposLt hweightBound hhistWord
  light_call hh using hbg,LightTernaryGroupedSourceKeys.time,LightTernaryWeightedHistogram.time,
    LightTernarySourceHistogram.scaleTime with res μ₂ ⟨hcounts,hkeepHist⟩
  have hbound : ∀ j<groups*bank, |μ₂ (valueBase+j)|≤(count*U : ℕ) := by
    intro j hj
    rw [hcounts j hj]
    simpa only [Nat.cast_mul] using
      LightTernaryWeightedHistogram.total_abs_le (fun i => group i*bank+key i) weight j count U hweightBound
  have hs := LightTernarySourceHistogram.scale_meets (d := d+1) hscale μ₂ factor
    hw hvalues hbound hfactor hweightedCount
  light_call hs using hbg,LightTernaryGroupedSourceKeys.time,LightTernaryWeightedHistogram.time,
    LightTernarySourceHistogram.scaleTime with res ν ⟨hscaled,hkeepScale⟩
  refine ⟨?_,?_⟩
  · intro r hr
    change ν (valueBase+r)=(factor : ℤ)*LightTernaryWeightedHistogram.total (fun i => group i*bank+key i) weight r count
    rw [hscaled r hr,hcounts r hr]
  · intro x hx hy
    exact (hkeepScale x hy).trans ((hkeepHist x hy).trans (hkeepKeys x hx))

def program : Program := [body 1 3 5,LightTernaryGroupedSourceKeys.body 2,
  LightBandLookup.searchBody 2,LightTernaryWeightedHistogram.body 4,
  fillBody,LightTernarySourceHistogram.scaleBody]

theorem time_bound (L count bank groups : ℕ) :
    time L count bank groups≤1000*(L+1)*(count+groups*bank+1) := by
  have hk := LightTernaryGroupedSourceKeys.time_bound L count
  have hh := LightTernaryWeightedHistogram.time_bound count (groups*bank)
  unfold time LightTernarySourceHistogram.scaleTime
  nlinarith [Nat.zero_le (L*(groups*bank))]

end ThreeSum.LightTernaryGroupedSources
