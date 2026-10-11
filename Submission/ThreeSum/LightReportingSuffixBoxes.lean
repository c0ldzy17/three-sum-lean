import Submission.ThreeSum.LightReportingSuffixSetup

/-! # Actual shrinking-suffix box preprocessing for an original valid block prefix -/

namespace ThreeSum.LightReportingSuffixBoxes

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostSuffix

variable {lim : Limits}
variable {β γ : Type*} [Fintype β] [Fintype γ] [DecidableEq β] [DecidableEq γ]

def localLeaf {h J k : ℕ} (hk : k ≤ J) (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) : Finset (Fin (suffixStage J (512*h) k)) → ℤ :=
  leafWeight (block_fit hk) (leftSource pMod B b q) (rightSource pMod shift C c q)
    (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))

theorem residual_le_suffix {h J k : ℕ} : residualSize h J k ≤ suffixStage J (512*h) k := by
  exact Nat.mul_le_mul_left (J-k) (by omega)

theorem program_meets {μ : ℕ → ℤ} {h J k baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (B : Finset β) (C : Finset γ)
    (b : β → ℤ) (c : γ → ℤ) (q : GlobalOutput h J)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix q k pre)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ boxBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ boxBase)
    (hbox : boxBase+(suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap (suffixStage J (512*h) k) boxCut ≤ work)
    (hspace : work+1+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^(suffixStage J (512*h) k)*
      ((2^(suffixStage J (512*h) k)*B.card)*(2^(suffixStage J (512*h) k)*C.card)) : ℕ) : ℤ) ≤ lim.word)
    (hboxCut : boxCut ≤ residualSize h J k)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b q) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c q) (width h J))
    (hd : depth+width h J+11 ≤ lim.depth) :
    Meets lim LightReportingSuffixSetup.program 29 depth
      [width h J,sourceCut h J,boxCut,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows q) (prefixRows (J := J) pre)),
        suffixStage J (512*h) k,k*(512*h),baseL,baseR,boxBase,maskBase,work]
      μ (LightReportingSuffixSetup.time (width h J) (suffixStage J (512*h) k) boxCut (k*(512*h)))
      (fun _ μ' =>
        LightBoxStages.StoredThrough μ' boxBase boxCut (localLeaf hk pMod shift B C b c q pre)
          (suffixStage J (512*h) k) ∧
        LightZetaStages.StoredThrough μ' baseL (sourceCut h J) (leftSource pMod B b q) (width h J) ∧
        LightZetaStages.StoredThrough μ' baseR (sourceCut h J) (rightSource pMod shift C c q) (width h J) ∧
        KeptBut μ μ' maskBase boxBase
          ((suffixStage J (512*h) k+1)*downsetCap (suffixStage J (512*h) k) boxCut)) := by
  have hQ : ∀ i, (outputRows q i).card = 2*h :=
    fun i => LayerCounts.mem_vertices.mp (q i).2.property
  have hu : ∀ i ∈ prefixIndices J k,
      prefixRows (J := J) pre i ⊆ outputRows q i ∧ (prefixRows (J := J) pre i).card = h := by
    intro i hi
    exact hp.2 i (mem_prefixIndices.mp hi)
  have hLc := leftPrefix_card hk (prefixRows (J := J) pre) (fun i hi => (hu i hi).2)
  have hRc := rightPrefix_card hk (outputRows q) (prefixRows (J := J) pre) hQ hu
  have hQc : (querySet k (outputRows q)).card = residualSize h J k := querySet_card hk _ hQ
  have hpreL : (leftPrefix k (prefixRows (J := J) pre)).card+boxCut ≤ sourceCut h J := by
    have hc := left_union_card_le hk (outputRows q) (prefixRows (J := J) pre) hQ (fun i hi => (hu i hi).2)
    rw [Finset.card_union_of_disjoint (leftPrefix_disjoint_query k _ _),hQc] at hc
    exact (Nat.add_le_add_left hboxCut _).trans hc
  have hpreR : (rightPrefix k (outputRows q) (prefixRows (J := J) pre)).card+boxCut ≤ sourceCut h J := by
    have hc := right_union_card_le hk (outputRows q) (prefixRows (J := J) pre) hQ hu
    rw [Finset.card_union_of_disjoint (rightPrefix_disjoint_query k _ _),hQc] at hc
    exact (Nat.add_le_add_left hboxCut _).trans hc
  have hm := LightReportingSuffixSetup.program_meets (d := depth) (μ := μ)
    (sourceCut := sourceCut h J) (block_fit hk)
    (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows q) (prefixRows (J := J) pre))
    (leftSource pMod B b q) (rightSource pMod shift C c q)
    hw (sourceCut_le_width h J) (hboxCut.trans residual_le_suffix) (suffixStage_le J (512*h) k)
    hdataL hdataR hbox hmasks hspace hword hvalueWord hpreL hpreR
    (fun S _ => leftSource_abs_le pMod B b q S)
    (fun S _ => rightSource_abs_le pMod shift C c q S) hstoredL hstoredR hd
  rw [hLc,hRc] at hm
  exact hm

end ThreeSum.LightReportingSuffixBoxes
