import Submission.ThreeSum.LightSharedReportingEntry
import Submission.ThreeSum.SharedReportingBankLayout

/-!
# Compute a suffix capacity and every address before constructing a catalog

The local binomial counts and current prefix count/span are scalar state
maintained by the surrounding bank loops. The compact suffix capacity is
computed here by the actual Pascal/downset routine. All remaining addresses
are computed arithmetically, and the existing entry constructor is called
exactly once. The return value is the next free payload address.
-/

namespace ThreeSum.LightSharedReportingCell

open Light SubsetAddress LightPascal ReportingHostPrefixOrder
open LightReportingPrefixCatalog LightReportingSuffixCatalog SharedReportingBankData
open SharedReportingBankLayout

set_option maxHeartbeats 2900000
set_option maxRecDepth 15000

/-- h,J,k,source pointer cells,t,boxCut,local choose/pair counts,current
prefix count/span,record destination,and first free payload cell. -/
def body (pSize pEntry : ℕ) : Stmt :=
  .set 13 (k 512 *' v 0) ;;
  .set 14 (v 1 *' v 13) ;;
  .set 15 ((v 1 -' v 2) *' v 13) ;;
  .call pSize [v 15,v 6,v 12] 16 ;;
  .set 17 (v 12 +' v 7) ;;
  .set 18 (v 17 +' v 8) ;;
  .set 19 (v 18 +' v 8) ;;
  .set 20 (v 19 +' v 10) ;;
  .set 21 (v 20 +' v 10) ;;
  .set 22 (v 21 +' v 9) ;;
  .set 23 ((v 15 +' k 1) *' v 16) ;;
  .set 24 (v 22 +' v 9 *' v 23) ;;
  .set 25 (v 24 +' v 16 +' v 9) ;;
  .set 26 (v 25 +' k 2 *' v 13 +' k 2 +' k 1 +'
    (v 14 +' k 1) *' (v 14 +' k 1) +' (v 14 +' k 1) +' v 9) ;;
  .set 27 (k 2 *' v 0 *' v 1) ;;
  .call pEntry [v 14,v 27,v 6,v 15,v 15,v 2 *' v 13,v 3,v 4,v 13,v 0,v 2,
    v 12,v 17,v 18,v 19,v 20,v 21,v 22,v 24,v 25,v 24,v 5,v 11] 28 ;;
  .set 0 (v 26)

def program : Program :=
  ReportingHostRelocation.program LightSharedReportingEntry.program LightDownsetSize.program ++
    [body 53 52]

def time (h J k boxCut : ℕ) : ℕ :=
  LightDownsetSize.time ((J-k)*(512*h))+LightSharedReportingEntry.time h J k boxCut+1500

theorem program_length : program.length=63 := rfl

theorem program_meets {lim : Limits} {μ : ℕ → ℤ}
    {h J k boxCut baseL baseR cellL cellR free rec B D d t : ℕ}
    (hk : k ≤ J) (f g : Finset (Fin (J*(512*h))) → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hconstants : (512 : ℤ) ≤ lim.word)
    (hJWord : (J : ℤ) ≤ lim.word)
    (hboxCut : boxCut ≤ (J-k)*(512*h))
    (hcellL : cellL < rec) (hcellR : cellR < rec)
    (hdataL : baseL+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ rec)
    (hdataR : baseR+(J*(512*h)+1)*downsetCap (J*(512*h)) (2*h*J) ≤ rec)
    (hrec : rec+5 ≤ free)
    (hspace : finish free h J k boxCut ≤ lim.space)
    (hpowWord : ((2^(512*h+1) : ℕ) : ℤ) ≤ lim.word)
    (hkeysWord : (LightRadixKeys.word (2^(512*h)) (2^(512*h)) k : ℤ) ≤ lim.word)
    (hword : (((J*(512*h)+1)*2^(J*(512*h)+1) : ℕ) : ℤ) ≤ lim.word)
    (hindexWord : (LightReportingSortedCatalog.word (J*(512*h)) (count h k) : ℤ) ≤ lim.word)
    (hvalueWord : (((2^((J-k)*(512*h))*
      ((2^((J-k)*(512*h))*B)*(2^((J-k)*(512*h))*D))) : ℕ) : ℤ) ≤ lim.word)
    (htWord : (t : ℤ) ≤ lim.word)
    (hpre : k*h+boxCut ≤ 2*h*J) (hf : ∀ S, S.card ≤ 2*h*J → |f S| ≤ B)
    (hg : ∀ S, S.card ≤ 2*h*J → |g S| ≤ D)
    (hleftRead : μ cellL=(baseL : ℤ)) (hrightRead : μ cellR=(baseR : ℤ))
    (hstoredL : LightZetaStages.StoredThrough μ baseL (2*h*J) f (J*(512*h)))
    (hstoredR : LightZetaStages.StoredThrough μ baseR (2*h*J) g (J*(512*h)))
    (hdPair : d+512*h+k+8 ≤ lim.depth) (hd : d+J*(512*h)+17 ≤ lim.depth)
    (hdSort : d+Nat.clog 2 (count h k)+5 ≤ lim.depth) :
    Meets lim program 62 d
      [h,J,k,cellL,cellR,t,boxCut,localChoose h,localPairs h,count h k,prefixSpan h k,rec,free]
      μ (time h J k boxCut) (fun r ν =>
        r=(finish free h J k boxCut : ℤ) ∧
        Entry ν rec (catalog free h J k boxCut t) hk f g ∧
        LightZetaStages.StoredThrough ν baseL (2*h*J) f (J*(512*h)) ∧
        LightZetaStages.StoredThrough ν baseR (2*h*J) g (J*(512*h)) ∧
        KeptBut μ ν free rec 5) := by
  have ho := ordered free h J k boxCut
  have hV : (J-k)*(512*h) ≤ J*(512*h) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
  have hcut : 2*h*J ≤ J*(512*h) := by nlinarith
  have hpairSpace := (pair_scratch free h J k boxCut).trans hspace
  have htableSpace := (table_scratch free h J k boxCut).trans hspace
  have hsortSpace := (sort_scratch free h J k boxCut).trans hspace
  have hW : J*(512*h)+1 ≤ lim.space := by omega
  have hL : 512*h ≤ lim.space := by omega
  have hN : count h k ≤ lim.space := by omega
  have hsizeSpace := (downset_scratch hk free boxCut).trans hspace
  have hsizeWord : ((((J-k)*(512*h)+1)*2^((J-k)*(512*h)+1) : ℕ) : ℤ) ≤ lim.word := by
    exact (Int.ofNat_le.mpr (Nat.mul_le_mul (Nat.add_le_add_right hV 1)
      (Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hV 1)))).trans hword
  have hprod : count h k*stride ((J-k)*(512*h)) boxCut ≤ lim.space := by
    have hm := ho.2.2.2.2.2.2.2.1
    unfold masks suffixWidth localWidth at hm
    omega
  have hstride : stride ((J-k)*(512*h)) boxCut ≤ lim.space := by
    have hn := count_pos h k
    exact (Nat.le_mul_of_pos_left _ hn).trans hprod
  have hcap : cap h J k boxCut ≤ lim.space := by
    have hm := ho.2.2.2.2.2.2.2.1
    have hh := cap_end free h J k boxCut
    omega
  have hwork : work free h J k boxCut ≤ lim.space := by omega
  have hsIndex := index_end free h J k boxCut
  have hstageL := stageR_eq free h k
  have hstageR := pointers_eq free h k
  have epairL : pairL free h=free+localChoose h := rfl
  have epairR : pairR free h=pairL free h+localPairs h := rfl
  have estageL : stageL free h=pairR free h+localPairs h := rfl
  have estageR : stageR free h k=stageL free h+prefixSpan h k := rfl
  have epointers : pointers free h k=stageR free h k+prefixSpan h k := rfl
  have eboxes : boxes free h k=pointers free h k+count h k := rfl
  have emasks : masks free h J k boxCut=boxes free h k+
      count h k*stride ((J-k)*(512*h)) boxCut := rfl
  have ework : work free h J k boxCut=masks free h J k boxCut+cap h J k boxCut+count h k := rfl
  have efinish : finish free h J k boxCut=work free h J k boxCut+2*(512*h)+2+1+
      tableSize (J*(512*h))+(J*(512*h)+1)+count h k := rfl
  have ecap : cap h J k boxCut=downsetCap ((J-k)*(512*h)) boxCut := rfl
  have hWWord : (J : ℤ)*(512*(h : ℤ)) ≤ lim.word := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr (show J*(512*h) ≤ lim.space by omega)).trans hw
  have hWNonneg : (0 : ℤ) ≤ (J : ℤ)*(512*(h : ℤ)) := by positivity
  have hWScalar : (J : ℤ)*(512*(h : ℤ))=((J*(512*h) : ℕ) : ℤ) := by push_cast; ring
  have etable : ((J : ℤ)*(512*(h : ℤ))+1)*((J : ℤ)*(512*(h : ℤ))+1)=
      (tableSize (J*(512*h)) : ℤ) := by simp only [tableSize,pow_two,Nat.cast_mul,
        Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  have hVWord : ((J : ℤ)-(k : ℤ))*(512*(h : ℤ)) ≤ lim.word := by
    simpa only [Nat.cast_mul,Nat.cast_sub hk,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr (show (J-k)*(512*h) ≤ lim.space by omega)).trans hw
  have hVNonneg : (0 : ℤ) ≤ ((J : ℤ)-(k : ℤ))*(512*(h : ℤ)) :=
    mul_nonneg (sub_nonneg.mpr (Int.ofNat_le.mpr hk)) (by positivity)
  have hVScalar : ((J-k : ℕ) : ℤ)*(512*(h : ℤ))=
      (((J-k)*(512*h) : ℕ) : ℤ) := by push_cast; ring
  have hcutWord : (2 : ℤ)*(h : ℤ)*(J : ℤ) ≤ lim.word := by
    simpa only [Nat.cast_mul,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr (show 2*h*J ≤ lim.space by omega)).trans hw
  have hcutNonneg : (0 : ℤ) ≤ (2 : ℤ)*(h : ℤ)*(J : ℤ) := by positivity
  have hprefWord : (k : ℤ)*(512*(h : ℤ)) ≤ lim.word :=
    (mul_le_mul_of_nonneg_right (Int.ofNat_le.mpr hk) (by positivity)).trans hWWord
  have hprefNonneg : (0 : ℤ) ≤ (k : ℤ)*(512*(h : ℤ)) := by positivity
  apply Meets.of_body (p := 62) (by rfl : program[62]?=some (body 53 52))
  unfold body time
  light_set (localWidth h : ℕ) using localWidth
  light_set (width h J : ℕ) using width,localWidth
  light_set (suffixWidth h J k : ℕ) using suffixWidth,localWidth,Nat.cast_sub hk
  have hsize := (ReportingHostRelocation.meets
    (LightDownsetSize.program_meets (μ := μ) (d := d+1) hw hsizeSpace hsizeWord hboxCut (by omega))
    LightSharedReportingEntry.program).append [body 53 52]
  light_call hsize using suffixWidth,localWidth with c ν₁ ⟨hc,hkeepSize⟩
  have estride : (((J-k : ℕ) : ℤ)*(512*(h : ℤ))+1)*c=
      (stride ((J-k)*(512*h)) boxCut : ℤ) := by
    rw [hc]
    simp only [stride,Nat.cast_mul,Nat.cast_add,Nat.cast_one,Nat.cast_ofNat]
  rw [hc] at estride
  light_set (pairL free h : ℕ) using pairL
  light_set (pairR free h : ℕ) using pairR
  light_set (stageL free h : ℕ) using stageL
  light_set (stageR free h k : ℕ) using stageR
  light_set (pointers free h k : ℕ) using pointers
  light_set (boxes free h k : ℕ) using boxes
  light_set (stride ((J-k)*(512*h)) boxCut : ℕ) using hc,stride,cap,suffixWidth,localWidth
  light_set (masks free h J k boxCut : ℕ) using masks,suffixWidth,localWidth
  light_set (work free h J k boxCut : ℕ) using hc,work,cap,suffixWidth,localWidth
  light_set (finish free h J k boxCut : ℕ) using finish,width,localWidth,tableSize,pow_two
  light_set (2*h*J : ℕ)
  have hsourceL : LightZetaStages.StoredThrough ν₁ baseL (2*h*J) f (J*(512*h)) :=
    LightSignedLeafBatch.storedThrough_of_on hstoredL
      (by intro a _ ha; exact hkeepSize a (by omega))
  have hsourceR : LightZetaStages.StoredThrough ν₁ baseR (2*h*J) g (J*(512*h)) :=
    LightSignedLeafBatch.storedThrough_of_on hstoredR
      (by intro a _ ha; exact hkeepSize a (by omega))
  have hreadL : ν₁ cellL=(baseL : ℤ) := (hkeepSize cellL (by omega)).trans hleftRead
  have hreadR : ν₁ cellR=(baseR : ℤ) := (hkeepSize cellR (by omega)).trans hrightRead
  have he := ((LightSharedReportingEntry.program_meets (d := d+1) (srcS := free)
    (pairL := pairL free h) (pairR := pairR free h)
    (stageL := stageL free h) (stageR := stageR free h k)
    (ptrBase := pointers free h k) (boxBase := boxes free h k)
    (maskBase := masks free h J k boxCut) (indexBase := index free h J k boxCut)
    (work := work free h J k boxCut) (t := t) hk f g hw hcut hboxCut hcellL hcellR hdataL hdataR hrec
    (by rfl) (by rfl) (by rfl) hstageL.symm.le hstageR.symm.le
    (by rfl) (by rfl) (cap_end free h J k boxCut) (by rfl) hsIndex
    hpairSpace htableSpace hsortSpace hpowWord hkeysWord hword hindexWord hvalueWord htWord hpre hf hg
    hreadL hreadR hsourceL hsourceR (by omega) (by omega) (by omega)).append
      (LightDownsetSize.program.map (ReportingHostRelocation.relocate LightSharedReportingEntry.program.length))).append
        [body 53 52]
  light_call he using width,localWidth,suffixWidth,index
    with result ν₂ ⟨_,hentry,hsourceL',hsourceR',hkeepEntry⟩
  light_set (finish free h J k boxCut : ℕ)
  refine ⟨by simp,hentry,hsourceL',hsourceR',?_⟩
  intro a ⟨ha,houtside⟩
  exact (hkeepEntry a ⟨ha,houtside⟩).trans (hkeepSize a ha)

end ThreeSum.LightSharedReportingCell
