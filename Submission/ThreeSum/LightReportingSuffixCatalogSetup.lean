import Submission.ThreeSum.LightReportingSuffixCatalog

/-! # Suffix catalog construction computes its own physical table stride -/

namespace ThreeSum.LightReportingSuffixCatalogSetup

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix LightReportingSuffixCatalog

variable {lim : Limits}

def body (pSize pCatalog : ℕ) : Stmt :=
  .call pSize [v 6,v 2,v 16] 17 ;;
  .set 18 ((v 6 +' k 1) *' v 17) ;;
  .call pCatalog [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,
    v 13,v 14,v 18,v 15,v 16] 0

def program : Program := LightReportingSuffixCatalog.program ++ [body 9 30]

def time (W V cut offset n : ℕ) : ℕ :=
  LightDownsetSize.time V+LightReportingSuffixCatalog.time W V cut offset n+100

theorem program_meets
    {μ : ℕ → ℤ} {W V offset cut boxCut stage cL cR baseL baseR inL inR n ptrBase boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (preL preR : ℕ → Finset (Fin W)) (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hboxCut : boxCut ≤ V) (hstage : stage ≤ W)
    (hn : 0 < n)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ ptrBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ ptrBase)
    (hinL : inL+n ≤ ptrBase) (hinR : inR+n ≤ ptrBase)
    (hptr : ptrBase+n ≤ boxBase) (hbox : boxBase+n*stride V boxCut ≤ maskBase)
    (hmasks : maskBase+downsetCap V boxCut ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : ((2^V*((2^stage*B)*(2^stage*D)) : ℕ) : ℤ) ≤ lim.word)
    (hcardL : ∀ i < n, (preL i).card = cL) (hcardR : ∀ i < n, (preR i).card = cR)
    (hpreL : cL+boxCut ≤ cut) (hpreR : cR+boxCut ≤ cut)
    (hf : ∀ S, S.card ≤ cut → |f S| ≤ B) (hg : ∀ S, S.card ≤ cut → |g S| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hreadL : ∀ i < n, μ (inL+i) = (subsetMask (preL i) : ℤ))
    (hreadR : ∀ i < n, μ (inR+i) = (subsetMask (preR i) : ℤ))
    (hd : d+W+13 ≤ lim.depth) :
    Meets lim program 31 d
      [W,cut,boxCut,stage,cL,cR,V,offset,baseL,baseR,inL,inR,n,ptrBase,boxBase,maskBase,work]
      μ (time W V boxCut offset n)
      (fun _ μ' =>
        SegN μ' ptrBase (List.ofFn fun i : Fin n => boxBase+i.val*stride V boxCut) ∧
        (∀ i < n, LightBoxStages.StoredThrough μ' (boxBase+i*stride V boxCut) boxCut
          (leafWeight hfit f g stage (preL i) (preR i)) V) ∧
        LightZetaStages.StoredThrough μ' baseL cut f W ∧
        LightZetaStages.StoredThrough μ' baseR cut g W ∧
        Kept μ μ' ptrBase) := by
  have hV : V ≤ W := by omega
  have hstride : stride V boxCut ≤ lim.space :=
    (Nat.le_mul_of_pos_left _ hn).trans (by omega)
  have hstrideWord : (((V+1)*downsetCap V boxCut : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hstride).trans hw
  have hstrideWordZ : ((V : ℤ)+1)*(downsetCap V boxCut : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_one] using hstrideWord
  have hstrideNonneg : 0 ≤ ((V : ℤ)+1)*(downsetCap V boxCut : ℤ) := by positivity
  apply Meets.of_body (p := 31) (by rfl : program[31]? = some (body 9 30))
  unfold body time
  have hc := (LightDownsetSize.meets (P := LightReportingSuffixSetup.program) (pMain := 9)
    (d := d+1) (μ := μ) (L := V) (cut := boxCut) (work := work)
    LightReportingSuffixSetup.procs.size LightReportingSuffixSetup.procs.setup
    LightReportingSuffixSetup.procs.offset hw
    (LightReportingSuffixCell.small_space hV hspace)
    (LightReportingSuffixCell.small_word hV hword) hboxCut (by omega)).append
      [LightReportingSuffixCatalog.body 29,body 9 30]
  light_call hc using LightDownsetSize.time,LightReportingSuffixCatalog.time
    with sizeRet μ₁ ⟨hsize,hkeepSize⟩
  light_set (stride V boxCut : ℕ) using hsize,stride,hstrideWord,hstrideWordZ,hstrideNonneg,
    LightDownsetSize.time,LightReportingSuffixCatalog.time
  have hstoredL₁ := LightSignedLeafBatch.storedThrough_of_on hstoredL
    (by intro i _ hi; exact hkeepSize i (by omega))
  have hstoredR₁ := LightSignedLeafBatch.storedThrough_of_on hstoredR
    (by intro i _ hi; exact hkeepSize i (by omega))
  have hreadL₁ : ∀ i < n, μ₁ (inL+i) = (subsetMask (preL i) : ℤ) := by
    intro i hi
    exact (hkeepSize _ (by omega)).trans (hreadL i hi)
  have hreadR₁ : ∀ i < n, μ₁ (inR+i) = (subsetMask (preR i) : ℤ) := by
    intro i hi
    exact (hkeepSize _ (by omega)).trans (hreadR i hi)
  have hcat := (LightReportingSuffixCatalog.program_meets (d := d+1) (μ := μ₁)
    hfit preL preR f g hw hcut hboxCut hstage hdataL hdataR hinL hinR hptr hbox hmasks
    hspace hword hvalueWord hcardL hcardR hpreL hpreR hf hg hstoredL₁ hstoredR₁ hreadL₁ hreadR₁
    (by omega)).append [body 9 30]
  light_call hcat using LightDownsetSize.time,LightReportingSuffixCatalog.time
    with result μ₂ ⟨hptrs,hboxes,hL,hR,hkeepCat⟩
  refine ⟨hptrs,hboxes,hL,hR,?_⟩
  intro i hi
  exact (hkeepCat i hi).trans (hkeepSize i (by omega))

theorem time_bound {W V cut offset n : ℕ} (hfit : offset+V ≤ W) (hcut : cut ≤ V) :
    time W V cut offset n ≤ 23000*(W+1)^4*(downsetCap V cut+1)*(n+1) := by
  have hc := LightReportingSuffixCatalog.time_bound (n := n) hfit hcut
  have hs := LightDownsetSize.time_bound V
  have hV : V ≤ W := by omega
  have hp : (V+1)^2 ≤ (W+1)^4 :=
    (Nat.pow_le_pow_left (Nat.succ_le_succ hV) 2).trans
      (Nat.pow_le_pow_right (by omega) (by decide))
  have hpos : 1 ≤ (W+1)^4*(downsetCap V cut+1)*(n+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  have hm : (W+1)^4 ≤ (W+1)^4*(downsetCap V cut+1)*(n+1) :=
    (Nat.le_mul_of_pos_right _ (by omega)).trans (Nat.le_mul_of_pos_right _ (by omega))
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixCatalogSetup
