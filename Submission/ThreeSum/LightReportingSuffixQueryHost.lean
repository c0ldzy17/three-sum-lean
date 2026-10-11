import Submission.ThreeSum.LightReportingSuffixQuery
import Submission.ThreeSum.LightReportingSuffixLower

/-!
# Complete suffix-local querying from the physical global query mask

The host computes the local query mask by a bounded bit scan, reads the
lifting factor from its own power table, and executes the complete local-box
sparse query. No local-mask conversion or power table is supplied by a caller.
-/

namespace ThreeSum.LightReportingSuffixQueryHost

open Light ThreeSum.SubsetAddress ThreeSum.LightPascal ThreeSum.LightSubsetAddress
open ReportingHostSuffix

variable {lim : Limits}

def body (pLower pQuery : ℕ) : Stmt :=
  .call pLower [v 0,v 7,v 8,v 10,v 17] 18 ;;
  .set 19 (M (v 17 +' v 8)) ;;
  .call pQuery [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 19,v 9,v 18,v 11,v 12,v 13,v 14,v 15,v 16,v 17] 0

def suffix : Program := [LightReportingSuffixLower.body 17 20,body 29 28]
def program : Program := LightReportingSuffixQuery.program ++ suffix
def time (W V c t : ℕ) : ℕ := LightReportingSuffixLower.time W V+LightReportingSuffixQuery.time W V c t+100

theorem program_meets
    {μ : ℕ → ℤ} {W V offset cut stage t baseL baseR boxCut boxBase maskBase work B D d : ℕ}
    (hfit : offset+V ≤ W) (Q : Finset (Fin V)) (preL preR : Finset (Fin W))
    (f g : Finset (Fin W) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hcut : cut ≤ W) (hstage : stage ≤ W)
    (hdataL : baseL+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataR : baseR+(W+1)*downsetCap W cut ≤ maskBase)
    (hdataBox : boxBase+(V+1)*downsetCap V boxCut ≤ maskBase)
    (hmasks : maskBase+LightSparseQuery.queryItems Q.card t ≤ work)
    (hspace : work+1+tableSize W+(W+1) ≤ lim.space)
    (hword : (((W+1)*2^(W+1) : ℕ) : ℤ) ≤ lim.word)
    (hvalueWord : (LightSparseQuery.magnitudeBound V stage Q.card t B D : ℤ) ≤ lim.word)
    (ht : t ≤ Q.card+1) (hboxCut : boxCut ≤ Q.card) (hflags : Q.card-t ≤ boxCut)
    (hdisjL : Disjoint preL (liftSet hfit Q)) (hdisjR : Disjoint preR (liftSet hfit Q))
    (hcardL : (preL ∪ liftSet hfit Q).card ≤ cut)
    (hcardR : (preR ∪ liftSet hfit Q).card ≤ cut)
    (hf : ∀ T, T.card ≤ cut → |f T| ≤ B)
    (hg : ∀ T, T.card ≤ cut → |g T| ≤ D)
    (hstoredL : LightZetaStages.StoredThrough μ baseL cut f W)
    (hstoredR : LightZetaStages.StoredThrough μ baseR cut g W)
    (hstoredBox : LightBoxStages.StoredThrough μ boxBase boxCut (leafWeight hfit f g stage preL preR) V)
    (hd : d+W+10 ≤ lim.depth) :
    Meets lim program 30 d
      [W,cut,stage,preL.card,subsetMask preL,preR.card,subsetMask preR,V,offset,
        Q.card,subsetMask (liftSet hfit Q),t,baseL,baseR,boxCut,boxBase,maskBase,work]
      μ (time W V Q.card t)
      (fun r μ' =>
        r = Subset.mobius (fun S => SubsetStages.stageValue f stage (preL ∪ S)*
          SubsetStages.stageValue g stage (preR ∪ S)) (liftSet hfit Q) ∧
        KeptBut μ μ' work maskBase (LightSparseQuery.queryItems Q.card t)) := by
  have hpowWord : ((2^(W+1) : ℕ) : ℤ) ≤ lim.word := by
    have hn : 2^(W+1) ≤ (W+1)*2^(W+1) := Nat.le_mul_of_pos_left _ (by omega)
    exact (by exact_mod_cast hn : ((2^(W+1) : ℕ) : ℤ) ≤
      (((W+1)*2^(W+1) : ℕ) : ℤ)).trans hword
  have hfactorWord : ((2^offset : ℕ) : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr (Nat.pow_le_pow_right (by decide) (by omega))).trans hpowWord
  apply Meets.of_body (p := 30) (by rfl : program[30]? = some (body 29 28))
  unfold body time
  have hl := LightReportingSuffixLower.meets (P := program) (pMain := 29) (pPowers := 17) (pErase := 20)
    (d := d+1) (μ := μ) (powers := work) rfl rfl rfl hfit Q hw (by omega) hpowWord (by omega)
  light_call hl using LightReportingSuffixLower.time,LightReportingSuffixQuery.time
    with localMask μ₁ ⟨hlocal,hpowers,hkeepLower⟩
  have hread : μ₁ (work+offset) = ((2^offset : ℕ) : ℤ) := hpowers offset (by omega)
  have hreadInt : μ₁ (work+offset) = (2 : ℤ)^offset := by simpa using hread
  light_set (2^offset : ℕ) using hread,hreadInt,LightReportingSuffixLower.time,LightReportingSuffixQuery.time
  have hstoredL₁ := LightSignedLeafBatch.storedThrough_of_on hstoredL (by
    intro i _ hi
    exact hkeepLower i ((hi.trans_le hdataL).trans_le (by omega)))
  have hstoredR₁ := LightSignedLeafBatch.storedThrough_of_on hstoredR (by
    intro i _ hi
    exact hkeepLower i ((hi.trans_le hdataR).trans_le (by omega)))
  have hstoredBox₁ := ReportingHostQueryBounds.boxStored_of_on hstoredBox (by
    intro i _ hi
    exact hkeepLower i ((hi.trans_le hdataBox).trans_le (by omega)))
  have hq := (LightReportingSuffixQuery.program_meets (d := d+1) (μ := μ₁)
    hfit Q preL preR f g hw hcut hstage hdataL hdataR hdataBox hmasks hspace hword hvalueWord
    ht hboxCut hflags hdisjL hdisjR hcardL hcardR hf hg hstoredL₁ hstoredR₁ hstoredBox₁ (by omega)).append suffix
  light_call hq using hlocal,LightReportingSuffixLower.time,LightReportingSuffixQuery.time
    with res μ₂ ⟨hres,hkeepQuery⟩
  refine ⟨hres,?_⟩
  intro i hi
  exact (hkeepQuery i hi).trans (hkeepLower i hi.1)

theorem time_bound {W V c t : ℕ} (hV : V ≤ W) (hc : c ≤ V) (ht : t ≤ c+1) :
    time W V c t ≤ 18000*(W+1)^3*(LightSparseQuery.queryItems c t+1) := by
  have hl := LightReportingSuffixLower.time_bound hV
  have hq := LightReportingSuffixQuery.time_bound hV hc ht
  have hp : (W+1)^2 ≤ (W+1)^3 := Nat.pow_le_pow_right (by omega) (by omega)
  have hm : (W+1)^3 ≤ (W+1)^3*(LightSparseQuery.queryItems c t+1) :=
    Nat.le_mul_of_pos_right _ (by omega)
  have hpos : 1 ≤ (W+1)^3*(LightSparseQuery.queryItems c t+1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
  unfold time
  nlinarith

end ThreeSum.LightReportingSuffixQueryHost
