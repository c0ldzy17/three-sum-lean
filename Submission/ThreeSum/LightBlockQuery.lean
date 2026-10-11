import Submission.ThreeSum.BlockIndexedQuery
import Submission.ThreeSum.LightSparseQuery
import Submission.ThreeSum.LightSignedBoxSetup

/-!
# The actual sparse-query machine returns the original raw prefix mass

All coordinate transport, prefix sizes, source bounds, and cutoff facts
are discharged for the concrete block histograms. The remaining storage
premises are precisely the arrays produced by source and box preprocessing.
-/

namespace ThreeSum.LightBlockQuery

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts

variable {lim : Limits} {P : Program}

abbrev width (h J : ℕ) : ℕ := J*(512*h)
abbrev sourceCut (h J : ℕ) : ℕ := 2*h*J
abbrev residualSize (h J k : ℕ) : ℕ := (J-k)*(2*h)

theorem sourceCut_le_width (h J : ℕ) : sourceCut h J ≤ width h J := by
  have hh : 2*h ≤ 512*h := by omega
  simpa only [sourceCut,width,Nat.mul_comm] using Nat.mul_le_mul_right J hh

section OriginalIndices

variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem queryValue_eq_prefixQuery {h J k : ℕ} (pMod shift : ℤ)
    (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod + lift w.2.1*pMod + shift)-globalKey w.2.2) :
    queryValue pMod shift B C b c w.2.2 k (prefixRows (J := J) pre) =
      ((prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) : ℤ) := by
  calc
    _ = transformPrefixValue pMod shift B C b c w.2.2 (prefixIndices J k) (prefixRows (J := J) pre) :=
      queryValue_eq_transformPrefixValue pMod shift B C b c w.2.2 (prefixRows (J := J) pre) hk
    _ = storedQueryValue pMod shift A B C a b c w k pre := by
      simp [storedQueryValue,hp,hkey]
    _ = _ := storedQueryValue_eq_prefixQuery pMod shift A B C a b c w pre hk

theorem meets {pMain pExplicit pBoxes pSign pEnum pLeafSum pBoxSum : ℕ}
    (hmain : P[pMain]? = some (LightSparseQuery.body pExplicit pBoxes pSign))
    (hExplicit : P[pExplicit]? = some (LightExplicitSum.body pEnum pLeafSum))
    (hBoxes : P[pBoxes]? = some (LightCanonicalBoxSum.body pEnum pBoxSum))
    (hSign : P[pSign]? = some LightSign.body)
    (CE : LightExplicitSum.Procs P pEnum pLeafSum)
    (CB : LightCanonicalBoxSum.Procs P pEnum pBoxSum)
    {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod + lift w.2.1*pMod + shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataBox : boxBase+(width h J+1)*downsetCap (width h J) boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (width h J) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J k+1) (hboxCut : boxCut ≤ residualSize h J k)
    (hflags : residualSize h J k-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (SignedLeaf.value (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
        (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
        (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))) (width h J))
    (hd : depth+width h J+9 ≤ lim.depth) :
    Meets lim P pMain depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),residualSize h J k,
        subsetMask (querySet k (outputRows w.2.2)),t,baseL,baseR,boxCut,boxBase,maskBase,work]
      μ (LightSparseQuery.time (width h J) (residualSize h J k) t)
      (fun r μ' =>
        r = ((prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) : ℤ) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems (residualSize h J k) t)) := by
  have hQ : ∀ i, (outputRows w.2.2 i).card = 2*h :=
    fun i => LayerCounts.mem_vertices.mp (w.2.2 i).2.property
  have hu : ∀ i ∈ prefixIndices J k,
      prefixRows (J := J) pre i ⊆ outputRows w.2.2 i ∧ (prefixRows (J := J) pre i).card = h := by
    intro i hi
    exact hp.2 i (mem_prefixIndices.mp hi)
  have hLc := leftPrefix_card hk (prefixRows (J := J) pre) (fun i hi => (hu i hi).2)
  have hRc := rightPrefix_card hk (outputRows w.2.2) (prefixRows (J := J) pre) hQ hu
  have hQc : (querySet k (outputRows w.2.2)).card = residualSize h J k := querySet_card hk _ hQ
  have hc := LightSparseQuery.meets hmain hExplicit hBoxes hSign CE CB
    (d := depth) (μ := μ) (cut := sourceCut h J)
    (querySet k (outputRows w.2.2)) (leftPrefix k (prefixRows (J := J) pre))
    (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))
    (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
    hw (sourceCut_le_width h J) (suffixStage_le J (512*h) k) hdataL hdataR hdataBox
    (by simpa only [hQc] using hmasks) hspace hword (by simpa only [hQc] using hvalueWord)
    (by simpa only [hQc] using ht) (by simpa only [hQc] using hboxCut)
    (by simpa only [hQc] using hflags)
    (leftPrefix_disjoint_query k (outputRows w.2.2) (prefixRows (J := J) pre))
    (rightPrefix_disjoint_query k (outputRows w.2.2) (prefixRows (J := J) pre))
    (left_union_card_le hk (outputRows w.2.2) (prefixRows (J := J) pre) hQ (fun i hi => (hu i hi).2))
    (right_union_card_le hk (outputRows w.2.2) (prefixRows (J := J) pre) hQ hu)
    (fun S _ => leftSource_abs_le pMod B b w.2.2 S)
    (fun S _ => rightSource_abs_le pMod shift C c w.2.2 S)
    hstoredL hstoredR hstoredBox hd
  rw [hLc,hRc,hQc] at hc
  exact hc.mono le_rfl (fun r μ' ⟨hr,hkeep⟩ =>
    ⟨hr.trans (queryValue_eq_prefixQuery pMod shift A B C a b c w pre hk hp hkey),hkeep⟩)

theorem program_meets     {μ : ℕ → ℤ} {h J k t baseL baseR boxCut boxBase maskBase work depth : ℕ}
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α → ℤ) (b : β → ℤ) (c : γ → ℤ) (w : Wanted h J α)
    (pre : List (Finset (Fin (512*h)))) (hk : k ≤ J) (hp : ValidPrefix w.2.2 k pre)
    (hkey : w.1 ∈ A ∧ globalModulus h J ∣
      (a w.1 % pMod + lift w.2.1*pMod + shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hdataL : baseL+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataR : baseR+(width h J+1)*downsetCap (width h J) (sourceCut h J) ≤ maskBase)
    (hdataBox : boxBase+(width h J+1)*downsetCap (width h J) boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems (residualSize h J k) t ≤ work)
    (hspace : work+tableSize (width h J)+(width h J+1) ≤ lim.space)
    (hword : (((width h J+1)*2^(width h J+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound (width h J) (suffixStage J (512*h) k)
      (residualSize h J k) t B.card C.card : ℤ) ≤ lim.word)
    (ht : t ≤ residualSize h J k+1) (hboxCut : boxCut ≤ residualSize h J k)
    (hflags : residualSize h J k-t ≤ boxCut)
    (hstoredL : LightZetaStages.StoredThrough μ baseL (sourceCut h J)
      (leftSource pMod B b w.2.2) (width h J))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (sourceCut h J)
      (rightSource pMod shift C c w.2.2) (width h J))
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut
      (SignedLeaf.value (leftSource pMod B b w.2.2) (rightSource pMod shift C c w.2.2)
        (suffixStage J (512*h) k) (leftPrefix k (prefixRows (J := J) pre))
        (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre))) (width h J))
    (hd : depth+width h J+9 ≤ lim.depth) :
    Meets lim LightSparseQuery.program 0 depth
      [width h J,sourceCut h J,suffixStage J (512*h) k,k*h,
        subsetMask (leftPrefix k (prefixRows (J := J) pre)),k*h,
        subsetMask (rightPrefix k (outputRows w.2.2) (prefixRows (J := J) pre)),residualSize h J k,
        subsetMask (querySet k (outputRows w.2.2)),t,baseL,baseR,boxCut,boxBase,maskBase,work]
      μ (LightSparseQuery.time (width h J) (residualSize h J k) t)
      (fun r μ' =>
        r = ((prefixQuery (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k pre : ℕ) : ℤ) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems (residualSize h J k) t)) :=
  meets rfl rfl rfl rfl LightSparseQuery.explicitProcs LightSparseQuery.boxProcs
    pMod shift A B C a b c w pre hk hp hkey hw hdataL hdataR hdataBox hmasks
    hspace hword hvalueWord ht hboxCut hflags hstoredL hstoredR hstoredBox hd

end OriginalIndices

end ThreeSum.LightBlockQuery
