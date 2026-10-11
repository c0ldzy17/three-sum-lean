import Submission.ThreeSum.ReportingHostLevelData
import Submission.ThreeSum.ReportingHostFrontierLayout

/-!
# One actual reporting level from persistent physical headers

The host reads the previously computed capacity and frontier count, the
packed next output row, and the shared five-cell catalog record. It invokes
the complete multi-parent expansion and writes the new physical header.
-/

namespace ThreeSum.LightReportingStoredStep

open Light Finset ThreeSum.SubsetAddress ThreeSum.LightPascal
open BlockRows BlockIndex BlockMaskLayout BlockForced BlockEncoding BlockIndexedQuery StoredReporting
open GlobalEncoding LocalCoverBounds RawIncidences RawReporting RawPrefixCounts LightBlockQuery
open ReportingHostSuffix ReportingHostPrefixOrder LightReportingPrefixCatalog LightReportingSuffixCatalog
open ReportingHostLevelData ReportingHostFrontierLayout ReportingHostMasks

set_option maxHeartbeats 3500000
set_option maxRecDepth 10000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

def body (pStep : ℕ) : Stmt :=
  .set 19 (M (v 8 +' k 3)) ;;
  .set 20 (k 4 +' k 2 *' v 19) ;;
  .set 21 (v 8 +' (v 3 -' k 1) *' v 20) ;;
  .set 22 (v 8 +' v 3 *' v 20) ;;
  .set 23 (M (v 7 +' v 3 -' k 1)) ;;
  .set 24 (M (v 21 +' k 1)) ;;
  .set 25 (v 6 +' k 5 *' v 3) ;;
  .set 26 (M (v 25)) ;;
  .set 27 (M (v 25 +' k 1)) ;;
  .set 28 (M (v 25 +' k 2)) ;;
  .set 29 (M (v 25 +' k 3)) ;;
  .set 30 (M (v 25 +' k 4)) ;;
  .set 31 ((v 2 -' v 3) *' v 18) ;;
  .set 32 (v 3 *' v 1) ;;
  .set 33 ((v 2 -' v 3) *' (k 2 *' v 1)) ;;
  .set 34 (v 3 *' v 18) ;;
  .set 35 (M (v 21)) ;;
  .call pStep [v 0,v 1,v 23,v 24,v 9,v 10,v 11,v 15,v 17,v 31,v 32,v 33,v 26,
    v 4,v 5,v 27,v 28,v 29,v 30,v 16,v 12,v 13,v 14,v 34,
    v 21 +' k 4,v 21 +' k 4 +' v 19,v 35,v 22 +' k 4,v 22 +' k 4 +' v 19] 36 ;;
  .set 37 (v 24 -' v 23) ;;
  .store (v 22) (v 36) ;;
  .store (v 22 +' k 1) (v 37) ;;
  .set 0 (v 36)

def program : Program := LightReportingFrontierStep.program ++ [body 50]
def time (h J k t n : ℕ) : ℕ := LightReportingFrontierStep.time h J k t n+1000

variable {lim : Limits}
variable {α β γ : Type*} [Fintype α] [Fintype β] [Fintype γ]
  [DecidableEq α] [DecidableEq β] [DecidableEq γ]

theorem program_meets {μ : ℕ→ℤ}
    {h J k baseL baseR catalogs rows root masks childL childR counts selected maskBase work depth : ℕ}
    {D : Catalog} (hk : k<J)
    (pMod shift : ℤ) (A : Finset α) (B : Finset β) (C : Finset γ)
    (a : α→ℤ) (b : β→ℤ) (c : γ→ℤ) (w : Wanted h J α)
    (hkey : w.1∈A ∧ globalModulus h J ∣ (a w.1%pMod+lift w.2.1*pMod+shift)-globalKey w.2.2)
    (hw : (lim.space : ℤ)≤lim.word)
    (HS : Sources μ pMod shift B C b c w.2.2 baseL baseR)
    (HC : Stored μ D (Nat.succ_le_of_lt hk) pMod shift B C b c w.2.2)
    (HB : Bounds h J (k+1) D baseL baseR root)
    (HW : Scratch lim h J (k+1) D B.card C.card maskBase work)
    (hmeta : SegN μ (catalogs+5*(k+1)) (D.record h (k+1)))
    (hmetaEnd : catalogs+5*(k+1)+5≤root)
    (hrows : rows+J≤root)
    (hrow : μ (rows+k)=(rowMask (outputRows w.2.2) ⟨k,hk⟩ : ℤ))
    (hcap : μ (root+3)=(capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w : ℤ))
    (HA : At μ (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w root
      (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) k)
    (hout : slot root (capacity (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w) (k+2)≤masks)
    (hmasks : masks+groupSize h≤childL) (hchildL : childL+groupSize h≤childR)
    (hchildR : childR+groupSize h≤counts) (hcounts : counts+groupSize h≤selected)
    (hselected : selected+groupSize h≤maskBase)
    (hparams : J+512*h+groupSize h+sourceCut h J≤lim.space)
    (hd : depth+2*width h J+18≤lim.depth) :
    Meets lim program 51 depth
      [width h J,h,J,k+1,baseL,baseR,catalogs,rows,root,masks,childL,childR,counts,selected,maskBase,work,
        groupSize h,sourceCut h J,512*h]
      μ (time h J k D.t (ReportingHostFrontier.frontier (rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c) w k).length)
      (fun r ν =>
        let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
        r=((ReportingHostFrontier.frontier I w (k+1)).length : ℤ) ∧
        At ν I w root (capacity I w) (k+1) ∧ Kept μ ν (slot root (capacity I w) (k+1))) := by
  let I := rawOn h J pMod shift (A ×ˢ (B ×ˢ C)) a b c
  let cap := capacity I w
  let pres := ReportingHostFrontier.frontier I w k
  let old := slot root cap k
  let dest := slot root cap (k+1)
  let catalogRow := catalogs+5*(k+1)
  let prefixCardNext := (k+1)*h
  let offsetNext := (k+1)*(512*h)
  let stageNext := suffixStage J (512*h) (k+1)
  let residualNext := residualSize h J (k+1)
  change At μ I w root cap k at HA
  change μ (root+3)=(cap : ℤ) at hcap
  change slot root cap (k+2)≤masks at hout
  change Meets lim program 51 depth _ μ (time h J k D.t pres.length)
    (fun r ν => r=((ReportingHostFrontier.frontier I w (k+1)).length : ℤ) ∧
      At ν I w root cap (k+1) ∧ Kept μ ν dest)
  have hcapPos : 0<cap := capacity_pos I w
  have hprevCount : pres.length≤cap := frontier_capacity I w hk.le
  have hnextCount : (ReportingHostFrontier.frontier I w (k+1)).length≤cap := frontier_capacity I w (by omega)
  have hchildren : pres.length*groupSize h≤cap := expansion_capacity I w hk.le
  have hrootOld : root≤old := by simpa only [slot_zero] using (slot_mono (base := root) (cap := cap) (Nat.zero_le k))
  have hold : old+4+2*cap=dest := (slot_succ root cap k).symm
  have hdest : dest+4+2*cap≤masks := by
    have hh := slot_succ root cap (k+1)
    change slot root cap (k+2)=dest+4+2*cap at hh
    rwa [hh] at hout
  have hwork := HW.masks
  have hspace := HW.space
  have hpow := HW.powers
  have hmetaT := hmeta.getElem (i := 0) (by simp [Catalog.record])
  have hmetaCut := hmeta.getElem (i := 1) (by simp [Catalog.record])
  have hmetaIndex := hmeta.getElem (i := 2) (by simp [Catalog.record])
  have hmetaPtr := hmeta.getElem (i := 3) (by simp [Catalog.record])
  have hmetaN := hmeta.getElem (i := 4) (by simp [Catalog.record])
  simp only [Catalog.record,List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at hmetaT hmetaCut hmetaIndex hmetaPtr hmetaN
  change μ catalogRow=(D.t : ℤ) at hmetaT
  change μ (catalogRow+1)=(D.boxCut : ℤ) at hmetaCut
  change μ (catalogRow+2)=(D.indexBase : ℤ) at hmetaIndex
  change μ (catalogRow+3)=(D.ptrBase : ℤ) at hmetaPtr
  change μ (catalogRow+4)=(count h (k+1) : ℤ) at hmetaN
  have hmetaBound : catalogRow+5≤root := hmetaEnd
  have hmetaIndexZ : μ (((catalogRow : ℤ)+2).toNat)=(D.indexBase : ℤ) := by
    rw [show ((catalogRow : ℤ)+2).toNat=catalogRow+2 by omega]
    exact hmetaIndex
  have hmetaPtrZ : μ (((catalogRow : ℤ)+3).toNat)=(D.ptrBase : ℤ) := by
    rw [show ((catalogRow : ℤ)+3).toNat=catalogRow+3 by omega]
    exact hmetaPtr
  have hmetaNZ : μ (((catalogRow : ℤ)+4).toNat)=(count h (k+1) : ℤ) := by
    rw [show ((catalogRow : ℤ)+4).toNat=catalogRow+4 by omega]
    exact hmetaN
  have hDindex := HB.index
  have hDptr := HB.pointers
  have ht := HW.t
  have hcut := HW.cut
  have hwidthSpace : width h J≤lim.space := by omega
  have hresLe : residualSize h J (k+1)≤width h J := by
    exact (LightReportingSuffixBoxes.residual_le_suffix (h := h) (J := J) (k := k+1)).trans
      (suffixStage_le J (512*h) (k+1))
  change residualNext≤width h J at hresLe
  change D.t≤residualNext+1 at ht
  change D.boxCut≤residualNext at hcut
  have hstageLe := suffixStage_le J (512*h) (k+1)
  change stageNext≤width h J at hstageLe
  have hprefixCard : (k+1)*h≤width h J := by
    have hh := Nat.mul_le_mul_right h (Nat.succ_le_of_lt hk)
    unfold width
    nlinarith
  have hoffset : (k+1)*(512*h)≤width h J := Nat.mul_le_mul_right _ (by omega)
  change prefixCardNext≤width h J at hprefixCard
  change offsetNext≤width h J at hoffset
  have hmask (S : Finset (Fin (width h J))) : (subsetMask S : ℤ)≤lim.word := by
    have hp : 2^(width h J)≤(width h J+1)*2^(width h J+1) :=
      (Nat.pow_le_pow_right (by decide) (by omega)).trans (Nat.le_mul_of_pos_left _ (by omega))
    exact (Int.ofNat_le.mpr ((subsetMask_isMask S).1.le.trans hp)).trans HW.word
  have hrowWord : (rowMask (outputRows w.2.2) ⟨k,hk⟩ : ℤ)≤lim.word := by
    have hh := BlockMaskLayout.rowMask_lt (outputRows w.2.2) ⟨k,hk⟩
    have hb := hmask (blockSet ⟨k,hk⟩ (outputRows w.2.2 ⟨k,hk⟩))
    simpa [rowMask] using hb
  have hQ := hmask (querySet k (outputRows w.2.2))
  have hQnext := hmask (querySet (k+1) (outputRows w.2.2))
  have hreadQ : μ (old+1)=(subsetMask (querySet k (outputRows w.2.2)) : ℤ) := HA.query
  have hreadN : μ old=(pres.length : ℤ) := HA.count
  have hcapZ : μ (((root : ℤ)+3).toNat)=(cap : ℤ) := by
    rw [show ((root : ℤ)+3).toNat=root+3 by omega]
    exact hcap
  have hrowZ : μ (((rows : ℤ)+((k : ℤ)+1)).toNat-1)=
      (rowMask (outputRows w.2.2) ⟨k,hk⟩ : ℤ) := by
    rw [show ((rows : ℤ)+((k : ℤ)+1)).toNat-1=rows+k by omega]
    exact hrow
  have readAdd (x y : ℕ) : μ (((x : ℤ)+(y : ℤ)).toNat)=μ (x+y) := by
    congr 1 <;> omega
  have hOldCalc : (root : ℤ)+(k : ℤ)*(4+2*(cap : ℤ))=(old : ℤ) := by
    simp only [old,slot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have hDestCalc : (root : ℤ)+((k : ℤ)+1)*(4+2*(cap : ℤ))=(dest : ℤ) := by
    simp only [dest,slot,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hMetaCalc : (catalogs : ℤ)+5*((k : ℤ)+1)=(catalogRow : ℤ) := by
    simp only [catalogRow,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one]
  have hSubtract : ((J-(k+1) : ℕ) : ℤ)=(J : ℤ)-((k : ℤ)+1) := by omega
  have hStageCalc : ((J : ℤ)-((k : ℤ)+1))*(512*(h : ℤ))=(stageNext : ℤ) := by
    simp only [stageNext,suffixStage,Nat.cast_mul,Nat.cast_sub (show k+1≤J by omega),Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  have hResidualCalc : ((J : ℤ)-((k : ℤ)+1))*(2*(h : ℤ))=(residualNext : ℤ) := by
    simp only [residualNext,residualSize,Nat.cast_mul,Nat.cast_sub (show k+1≤J by omega),Nat.cast_add,Nat.cast_ofNat,Nat.cast_one]
  have hPrefixCalc : ((k : ℤ)+1)*(h : ℤ)=(prefixCardNext : ℤ) := by
    simp only [prefixCardNext,Nat.cast_mul,Nat.cast_add,Nat.cast_one]
  have hOffsetCalc : ((k : ℤ)+1)*(512*(h : ℤ))=(offsetNext : ℤ) := by
    simp only [offsetNext,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  apply Meets.of_body (p := 51) (by rfl : program[51]?=some (body 50))
  unfold body time
  light_set (cap : ℕ) using hcapZ,LightReportingFrontierStep.time
  light_set (4+2*cap : ℕ) using LightReportingFrontierStep.time
  light_set (old : ℕ) using hOldCalc,LightReportingFrontierStep.time
  light_set (dest : ℕ) using hDestCalc,LightReportingFrontierStep.time
  light_set (rowMask (outputRows w.2.2) ⟨k,hk⟩ : ℕ) using hrowZ,LightReportingFrontierStep.time
  light_set (subsetMask (querySet k (outputRows w.2.2)) : ℕ) using readAdd,hreadQ,LightReportingFrontierStep.time
  light_set (catalogRow : ℕ) using hMetaCalc,LightReportingFrontierStep.time
  light_set (D.t : ℕ) using hMetaCalc,readAdd,hmetaT,LightReportingFrontierStep.time
  light_set (D.boxCut : ℕ) using hMetaCalc,readAdd,hmetaCut,LightReportingFrontierStep.time
  light_set (D.indexBase : ℕ) using hMetaCalc,hmetaIndexZ,LightReportingFrontierStep.time
  light_set (D.ptrBase : ℕ) using hMetaCalc,hmetaPtrZ,LightReportingFrontierStep.time
  light_set (count h (k+1) : ℕ) using hMetaCalc,hmetaNZ,LightReportingFrontierStep.time
  light_set (stageNext : ℕ) using hStageCalc,LightReportingFrontierStep.time
  light_set (prefixCardNext : ℕ) using hPrefixCalc,LightReportingFrontierStep.time
  light_set (residualNext : ℕ) using hResidualCalc,LightReportingFrontierStep.time
  light_set (offsetNext : ℕ) using hOffsetCalc,LightReportingFrontierStep.time
  light_set (pres.length : ℕ) using hreadN,LightReportingFrontierStep.time
  have hrun := (LightReportingFrontierStep.program_meets (depth := depth+1) (μ := μ)
    (inL := old+4) (inR := old+4+cap) (outL := dest+4) (outR := dest+4+cap)
    pMod shift A B C a b c w pres hk
    (fun _ hp => ReportingHostPositive.frontier_valid I w hk.le hp) hkey hw
    (HB.left.trans (by omega)) (HB.right.trans (by omega))
    (HB.index.trans (by omega)) (HB.pointers.trans (by omega)) (HB.boxes.trans (by omega))
    (by omega) (by omega) (by omega) (by omega) hmasks hchildL hchildR hcounts hselected
    HW.masks HW.space HW.powers HW.emod HW.word HW.lookup HW.values HW.t HW.cut HW.flags
    HS.left HS.right HC.index HC.pointers HC.boxes HA.left HA.right (by omega)).append [body 50]
  light_call hrun using hSubtract,LightReportingFrontierStep.time with result ν ⟨hresult,hnewL,hnewR,hkept⟩
  have hstep := ReportingHostPositive.frontier_step I w hk
  change result=((pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).length : ℤ) at hresult
  change LightReportingPositiveExpand.KeptOutputs μ ν masks (dest+4) (dest+4+cap)
    (pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).length at hkept
  change SegN ν (dest+4) ((pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).map
    fun pre => subsetMask (leftPrefix (k+1) (prefixRows (J := J) pre))) at hnewL
  change SegN ν (dest+4+cap) ((pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)).map
    fun pre => subsetMask (rightPrefix (k+1) (outputRows w.2.2) (prefixRows (J := J) pre))) at hnewR
  have hpstep : pres.flatMap (fun pre => ReportingHostPositive.positiveChildren I w pre hk)=
    ReportingHostFrontier.frontier I w (k+1) := hstep.symm
  rw [hpstep] at hresult hkept hnewL hnewR
  have hnextWord : ((ReportingHostFrontier.frontier I w (k+1)).length : ℤ)≤lim.word :=
    (Int.ofNat_le.mpr (hnextCount.trans (by omega))).trans hw
  light_set (subsetMask (querySet (k+1) (outputRows w.2.2)) : ℕ)
    using queryMask_step,LightReportingFrontierStep.time
  light_store dest ((ReportingHostFrontier.frontier I w (k+1)).length : ℕ)
    using hresult,LightReportingFrontierStep.time
  light_store (dest+1) (subsetMask (querySet (k+1) (outputRows w.2.2)) : ℕ)
    using LightReportingFrontierStep.time
  light_set ((ReportingHostFrontier.frontier I w (k+1)).length : ℕ)
    using hresult,LightReportingFrontierStep.time
  refine ⟨by simp,?_,?_⟩
  · constructor
    · change Function.update (Function.update ν dest _) (dest+1) _ dest=_
      simp
    · change Function.update (Function.update ν dest _) (dest+1) _ (dest+1)=_
      simp
    · intro i hi
      change Function.update (Function.update ν dest _) (dest+1) _ (dest+4+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hnewL i hi
    · intro i hi
      change Function.update (Function.update ν dest _) (dest+1) _ (dest+4+cap+i)=_
      rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
      exact hnewR i hi
  · intro i hi
    change Function.update (Function.update ν dest _) (dest+1) _ i=μ i
    rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
    exact hkept i ⟨by omega,Or.inl (by omega),Or.inl (by omega)⟩

end ThreeSum.LightReportingStoredStep
