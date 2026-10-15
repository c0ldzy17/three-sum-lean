import Submission.ThreeSum.LightOriginalSurvivors
import Submission.ThreeSum.LightReportingGather

/-! Actual exact cleanup followed by aligned compact original values and keys. -/
noncomputable section
namespace ThreeSum.LightOriginalSurvivorStage
open Light ThreeSum.LightSubsetAddress ThreeSum.LightOriginalBucketFilter
open ThreeSum.LightOriginalCollisionCleanup ThreeSum.LightOriginalSurvivors
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

def body : Stmt :=
  .call 1 [v 0,v 1,v 2,v 3,v 4] 17 ;;
  .call 2 [v 4 +' v 1,v 17,v 5,v 1,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 16 ;;
  .set 18 (v 1 -' v 17) ;;
  .call 6 [v 4,v 5,v 13,v 18,v 1] 19 ;;
  .call 6 [v 4,v 0,v 14,v 18,v 1] 19 ;;
  .store (v 15) (v 18) ;;
  .set 0 (v 16)

def program : Program := LightOriginalCollisionCleanup.program ++ [LightReportingGather.body,body]
def time (keys : ℕ → ℕ) (n scanN L : ℕ) : ℕ :=
  LightOriginalCollisionCleanup.time keys n scanN L +
    2*LightReportingGather.time (indices keys n).length + 300

def Above (μ ν : ℕ → ℤ) (boundary : ℕ) : Prop := ∀ x, boundary < x → ν x = μ x

def Unwritten (out n dstValues dstKeys count lengthCell x : ℕ) : Prop :=
  (x < out ∨ out+2*n ≤ x) ∧ (x < dstValues ∨ dstValues+count ≤ x) ∧
    (x < dstKeys ∨ dstKeys+count ≤ x) ∧ x ≠ lengthCell

def Preserves (μ ν : ℕ → ℤ) (out n dstValues dstKeys count lengthCell : ℕ) : Prop :=
  ∀ x, Unwritten out n dstValues dstKeys count lengthCell x → ν x = μ x

variable {lim : Limits}

theorem program_meets {keyBase n hist q out valuesBase scanBase scanN targetBase targetN powers W L U d
    dstValues dstKeys lengthCell : ℕ} (sign : ℤ)
    (μ : ℕ → ℤ) (keys : ℕ → ℕ) (values scan target : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hkeysSpace : keyBase+n ≤ out) (hhistSpace : hist+q ≤ out)
    (hvaluesSpace : valuesBase+n ≤ out) (hscanSpace : scanBase+scanN ≤ out)
    (htargetSpace : targetBase+targetN ≤ out) (hspace : powers+(W+1) ≤ out)
    (hfirst : out+2*n ≤ dstValues) (hsecond : dstValues+n ≤ dstKeys)
    (hthird : dstKeys+n ≤ lengthCell) (hlast : lengthCell+1 ≤ lim.space)
    (hword : ((targetN+2^(W+1)+16 : ℕ) : ℤ) ≤ lim.word)
    (hkeys : ∀ i < n, keys i < q) (hreadKeys : ∀ i < n, μ (keyBase+i) = (keys i : ℤ))
    (hcounts : ∀ k < q, μ (hist+k) = (counts keys n k : ℤ))
    (hvalues : ∀ i < n, |values i| ≤ U) (hreadValues : ∀ i < n, μ (valuesBase+i) = values i)
    (hscan : ∀ i < scanN, |scan i| ≤ U) (hreadScan : ∀ i < scanN, μ (scanBase+i) = scan i)
    (hreadTarget : ∀ i < targetN, μ (targetBase+i) = target i)
    (hsign : |sign| ≤ 1) (hvalueWord : 2*(U : ℤ)+3 ≤ lim.word)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i < j → j < targetN → target i < target j)
    (hL : L ≤ W) (htargetN : targetN < 2^L) (hd : d+L+4 ≤ lim.depth) :
    Meets lim program 7 d
      [keyBase,n,hist,q,out,valuesBase,scanBase,scanN,targetBase,targetN,powers,L,sign,dstValues,dstKeys,lengthCell]
      μ (time keys n scanN L)
      (fun ret ν =>
        ret = (LightDeletedTwoSum.flag (badIndex keys n) values scan target targetN scanN
          (badIndices keys n).length sign : ℤ) ∧
        ν lengthCell = ((indices keys n).length : ℤ) ∧
        Seg ν out (cells (indices keys n)) ∧
        (∀ i < (indices keys n).length, ν (dstValues+i) = values (index keys n i)) ∧
        (∀ i < (indices keys n).length, ν (dstKeys+i) = (keys (index keys n i) : ℤ)) ∧
        Kept μ ν out ∧ Above μ ν lengthCell ∧
          Preserves μ ν out n dstValues dstKeys (indices keys n).length lengthCell) := by
  have ht := length_le keys n
  have hb := (lengths keys (counts keys n) n).2
  have hpartition := partition_lengths keys (counts keys n) n
  have hpart : (indices keys n).length + (badIndices keys n).length = n := hpartition
  have hnword : (n : ℤ) ≤ lim.word := by omega
  have hcword : ∀ k < q, (counts keys n k : ℤ) ≤ lim.word := by
    intro k hk
    exact (Int.ofNat_le.mpr (LightHistogram.count_le keys k n)).trans hnword
  have hf := LightOriginalBucketFilter.meets (P := program) (d := d+1)
    (pMain := 1) (by rfl) μ keys (counts keys n) hw
    hkeysSpace hhistSpace (by omega) hkeys hreadKeys hcounts hcword (by omega)
  apply Meets.of_body (p := 7) (by rfl : program[7]? = some body)
  unfold body time LightOriginalCollisionCleanup.time
  light_call hf using LightOriginalBucketFilter.time,LightDeletedTwoSum.time,LightReportingGather.time
    with badN ν ⟨hBadN,hGood,hBad,H⟩
  change badN = ((badIndices keys n).length : ℤ) at hBadN
  have hKeep {x : ℕ} (hx : x < out) : ν x = μ x := H x (Or.inl hx)
  have hIdRead : ∀ i < (badIndices keys n).length, ν (out+n+i) = (badIndex keys n i : ℤ) := by
    intro i hi
    have hh := hBad i (by simpa [cells,badIndices] using hi)
    rw [badIndex,dif_pos hi]
    simpa [cells,List.bind_eq_flatMap,List.pure_def,←List.map_eq_flatMap,List.getElem_map,badIndices] using hh
  have hPowers : Powers ν powers W := by
    intro i hi
    rw [hKeep (by omega),hpowers i hi]
  have hc := LightDeletedTwoSum.meets (P := program) (d := d+1) (badBase := out+n)
    (badN := (badIndices keys n).length) (valuesBase := valuesBase) (originalN := n)
    (scanBase := scanBase) (scanN := scanN) (targetBase := targetBase) (targetN := targetN)
    (powers := powers) (W := W) (L := L) (U := U) sign
    (pMain := 2) (pTwoSum := 3) (pLookup := 4) (pSearch := 5) rfl rfl rfl rfl ν
    (badIndex keys n) values scan target hw (by omega)
    (by omega) (by omega) (by omega) (by omega) hword (fun i hi => badIndex_lt hi) hIdRead
    hvalues (fun i hi => by rw [hKeep (by omega),hreadValues i hi]) hscan
    (fun i hi => by rw [hKeep (by omega),hreadScan i hi])
    (fun i hi => by rw [hKeep (by omega),hreadTarget i hi]) hsign hvalueWord hPowers hsorted hL htargetN (by omega)
  light_call hc using hBadN,LightOriginalBucketFilter.time,LightDeletedTwoSum.time,LightReportingGather.time
    with result ξ ⟨hResult,hMem⟩
  subst ξ
  light_set ((indices keys n).length : ℤ) using hBadN,Int.natCast_add
  have hGoodRead : ∀ i < (indices keys n).length, ν (out+i) = (index keys n i : ℤ) := by
    intro i hi
    have hh := hGood i (by simpa [cells,indices] using hi)
    rw [index,dif_pos hi]
    simpa [cells,indices,List.bind_eq_flatMap,List.pure_def,←List.map_eq_flatMap,List.getElem_map] using hh
  have hv := LightReportingGather.meets (P := program) (p := 6) (d := d+1)
    (indices := out) (src := valuesBase) (dst := dstValues) (t := (indices keys n).length)
    (n := n) rfl (index keys n) values hw (by omega) (by omega) (by omega)
    (Or.inl (by omega)) (Or.inl (by omega)) (fun i hi => index_lt hi) hGoodRead
    (fun i hi => by rw [hKeep (by omega),hreadValues i hi])
    (fun i hi => (hvalues i hi).trans (by omega))
  light_call hv using LightOriginalBucketFilter.time,LightDeletedTwoSum.time,LightReportingGather.time
    with ignored ξ ⟨hValues,Hv⟩
  have hGoodRead' : ∀ i < (indices keys n).length, ξ (out+i) = (index keys n i : ℤ) := by
    intro i hi
    exact (Hv _ (Or.inl (by omega))).trans (hGoodRead i hi)
  have hk := LightReportingGather.meets (P := program) (p := 6) (d := d+1)
    (indices := out) (src := keyBase) (dst := dstKeys) (t := (indices keys n).length)
    (n := n) rfl (index keys n) (fun i => (keys i : ℤ)) hw (by omega) (by omega) (by omega)
    (Or.inl (by omega)) (Or.inl (by omega)) (fun i hi => index_lt hi) hGoodRead'
    (fun i hi => by rw [Hv _ (Or.inl (by omega)),hKeep (by omega),hreadKeys i hi])
    (fun i hi => by rw [abs_of_nonneg (Int.natCast_nonneg _)]; have hh := hkeys i hi; omega)
  light_call hk using LightOriginalBucketFilter.time,LightDeletedTwoSum.time,LightReportingGather.time
    with ignored₂ ζ ⟨hKeys,Hk⟩
  light_store lengthCell ((indices keys n).length : ℤ)
  light_set result using hResult
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using hResult
  · simp
  · intro i hi
    have hi' : i < (indices keys n).length := by simpa [cells] using hi
    simpa [indices] using (show (Function.update ζ lengthCell ((indices keys n).length : ℤ)) (out+i) =
        (cells (indices keys n))[i] from by
      rw [Function.update_of_ne (by omega),Hk _ (Or.inl (by omega)),Hv _ (Or.inl (by omega))]
      exact hGood i hi)
  · intro i hi
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) (dstValues+i) = _
    rw [Function.update_of_ne (by omega),Hk _ (Or.inl (by omega))]
    exact hValues i hi
  · intro i hi
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) (dstKeys+i) = _
    rw [Function.update_of_ne (by omega)]
    exact hKeys i hi
  · intro x hx
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) x = _
    rw [Function.update_of_ne (by omega),Hk _ (Or.inl (by omega)),Hv _ (Or.inl (by omega))]
    exact hKeep hx
  · intro x hx
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) x = _
    rw [Function.update_of_ne (by omega),Hk _ (Or.inr (by omega)),Hv _ (Or.inr (by omega))]
    exact H x (Or.inr (by omega))
  · intro x hx
    obtain ⟨hf,hv,hk,hne⟩ := hx
    change (Function.update ζ lengthCell ((indices keys n).length : ℤ)) x = _
    rw [Function.update_of_ne hne,Hk x hk,Hv x hv]
    exact H x hf

end ThreeSum.LightOriginalSurvivorStage
