import Submission.ThreeSum.LightReportingSuffixQueryHost
import Submission.ThreeSum.LightReportingSuffixBoxes

/-! # The actual physical-global-mask/local-box query returns the original raw prefix count -/

namespace ThreeSum.LightReportingSuffixQueryIndexed

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataBox : boxBase+(suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (suffixStage J (512*h) k) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J k+1) (hboxCut : boxCut ≤ residualSize h J k)
    (hflags : residualSize h J k-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (LightReportingSuffixBoxes.localLeaf hk pMod shift B C b c w.2.2 pre) (suffixStage J (512*h) k))
    (hd : depth+width h J+10 ≤ lim.depth) :
    Meets lim LightReportingSuffixQueryHost.program 30 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),residualSize h J k,subsetMask (querySet k (outputRows w.2.2)),
        t,baseL,baseR,boxCut,boxBase,maskBase,work]
      μ (LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t)
      (fun r μ' =>
        r = (prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℤ) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems (residualSize h J k) t)) := by
  have hQ : ∀ i, (outputRows w.2.2 i).card = 2*h :=
    fun i => LayerCounts.mem_vertices.mp (w.2.2 i).2.property
  have hu : ∀ i ∈ prefixIndices J k,
      prefixRows (J := J) pre i ⊆ outputRows w.2.2 i ∧ (prefixRows (J := J) pre i).card = h := by
    intro i hi
    exact hp.2 i (mem_prefixIndices.mp hi)
  have hLc := leftPrefix_card hk (prefixRows (J := J) pre) (fun i hi => (hu i hi).2)
  have hRc := rightPrefix_card hk (outputRows w.2.2) (prefixRows (J := J) pre) hQ hu
  have hQc : (localQuery hk (outputRows w.2.2)).card = residualSize h J k := localQuery_card hk _ hQ
  have hlocal := lift_localQuery hk (outputRows w.2.2)
  have hc := LightReportingSuffixQueryHost.program_meets (d := depth) (μ := μ) (cut := sourceCut h J)
    (block_fit hk) (localQuery hk (outputRows w.2.2))
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))
    (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
    hw (sourceCut_le_width h J) (suffixStage_le J (512*h) k) hdataL hdataR hdataBox
    (by simpa only [hQc] using hmasks) hspace hword (by simpa only [hQc, suffixStage] using hvalueWord)
    (by simpa only [hQc] using ht) (by simpa only [hQc] using hboxCut) (by simpa only [hQc] using hflags)
    (by rw [hlocal]; exact leftPrefix_disjoint_query k _ _)
    (by rw [hlocal]; exact rightPrefix_disjoint_query k _ _)
    (by rw [hlocal]; exact left_union_card_le hk _ _ hQ (fun i hi => (hu i hi).2))
    (by rw [hlocal]; exact right_union_card_le hk _ _ hQ hu)
    (fun S _ => leftSource_abs_le pMod B b w.2.2 S)
    (fun S _ => rightSource_abs_le pMod shift C c w.2.2 S)
    hstoredL hstoredR hstoredBox hd
  rw [hLc,hRc,hQc,hlocal] at hc
  exact hc.mono le_rfl (fun r μ' ⟨hr,hkeep⟩ =>
    ⟨hr.trans (queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey),hkeep⟩)

theorem time_bound {h J k t : ℕ} (ht : t ≤ residualSize h J k+1) :
    LightReportingSuffixQueryHost.time (width h J) (suffixStage J (512*h) k) (residualSize h J k) t ≤
      18000*(width h J+1)^3*(LightSparseQuery.queryItems (residualSize h J k) t+1) :=
  LightReportingSuffixQueryHost.time_bound (suffixStage_le J (512*h) k)
    LightReportingSuffixBoxes.residual_le_suffix ht

end ThreeSum.LightReportingSuffixQueryIndexed
