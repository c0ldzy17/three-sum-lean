import Submission.ThreeSum.ReportingHostWantedControls

/-!
# Execute the guarded reporter from the two concrete packed records

This procedure loads the twenty-cell owner/source selection and fourteen
computed scratch pointers, reads the retained prime and trim cap, and
passes exactly the verified guarded reporter's forty-four arguments.
Its compositional law retains the supplied reporter postcondition unchanged.
-/

namespace ThreeSum.LightReportingWantedRecordCall

open Light GlobalEncoding LocalCoverBounds LightBlockQuery ReportingHostWantedLayout
open ReportingHostWantedControls

set_option maxHeartbeats 5500000
set_option maxRecDepth 24000
set_option linter.unusedVariables false

def body (pWanted : ℕ) : Stmt :=
  .set 8 (M (v 0 +' k 0)) ;;
  .set 9 (M (v 0 +' k 1)) ;;
  .set 10 (M (v 0 +' k 2)) ;;
  .set 11 (M (v 0 +' k 3)) ;;
  .set 12 (M (v 0 +' k 4)) ;;
  .set 13 (M (v 0 +' k 5)) ;;
  .set 14 (M (v 0 +' k 6)) ;;
  .set 15 (M (v 0 +' k 7)) ;;
  .set 16 (M (v 0 +' k 8)) ;;
  .set 17 (M (v 0 +' k 9)) ;;
  .set 18 (M (v 0 +' k 10)) ;;
  .set 19 (M (v 0 +' k 11)) ;;
  .set 20 (M (v 0 +' k 12)) ;;
  .set 21 (M (v 0 +' k 13)) ;;
  .set 22 (M (v 0 +' k 14)) ;;
  .set 23 (M (v 0 +' k 15)) ;;
  .set 24 (M (v 0 +' k 16)) ;;
  .set 25 (M (v 0 +' k 17)) ;;
  .set 26 (M (v 0 +' k 18)) ;;
  .set 27 (M (v 0 +' k 19)) ;;
  .set 28 (M (v 1 +' k 0)) ;;
  .set 29 (M (v 1 +' k 1)) ;;
  .set 30 (M (v 1 +' k 2)) ;;
  .set 31 (M (v 1 +' k 3)) ;;
  .set 32 (M (v 1 +' k 4)) ;;
  .set 33 (M (v 1 +' k 5)) ;;
  .set 34 (M (v 1 +' k 6)) ;;
  .set 35 (M (v 1 +' k 7)) ;;
  .set 36 (M (v 1 +' k 8)) ;;
  .set 37 (M (v 1 +' k 9)) ;;
  .set 38 (M (v 1 +' k 10)) ;;
  .set 39 (M (v 1 +' k 11)) ;;
  .set 40 (M (v 1 +' k 12)) ;;
  .set 41 (M (v 1 +' k 13)) ;;
  .set 42 (M (v 6 +' k 6)) ;;
  .set 43 (M (v 6 +' k 7)) ;;
  .set 44 (k 512 *' v 2) ;;
  .set 45 (v 3 *' (k 2 *' v 2)) ;;
  .set 46 (v 1 +' k 18 +' v 3) ;;
  .set 47 (v 1 +' k 38 +' k 2 *' v 3) ;;
  .call pWanted [v 8,v 13,v 14,v 15,v 16,v 17,v 18,v 19,v 20,v 5,v 3,v 44,v 2,v 42,v 43,v 23,v 24,v 25,v 26,v 27,v 4,v 28,v 12,v 47,v 21,v 22,v 29,v 30,v 31,v 32,v 33,v 34,v 41,k 0,v 45,v 35,v 36,v 37,v 38,v 39,v 40,v 46,v 6,v 7] 0

def program : Program := LightReportingWanted.program++[body 137]

def numericExtra (h J K : ℕ) : ℕ :=
  J+512*h+K+BlockSourceEncoding.modulus h J+sourceCut h J+
    localPrime h+localBucketCap h+1024

/-- Separate translated addresses from the size-only scalar envelope. -/
def space (selectionHeader layoutHeader cover counter h J K : ℕ) : ℕ :=
  max (max (selectionHeader+20) (layoutHeader+38+3*J))
    (max (max (cover+8) (counter+2)) (numericExtra h J K))

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {S : Selection} {L : Layout}
    {selectionHeader layoutHeader cover counter h J K d T : ℕ} {Q : ℤ→(ℕ→ℤ)→Prop}
    (H : Seg μ selectionHeader (record S)) (HL : SegN μ layoutHeader (values L))
    (hprime : μ (cover+6)=(localPrime h : ℤ))
    (hcap : μ (cover+7)=(localBucketCap h : ℤ))
    (hw : (lim.space : ℤ)≤lim.word) (hd : d<lim.depth)
    (hs : space selectionHeader layoutHeader cover counter h J K≤lim.space)
    (hselected : ∀ x∈record S, |x|≤lim.word)
    (hlayout : ∀ x∈values L, x≤lim.space)
    (hreport : Meets lim LightReportingWanted.program 137 (d+1)
      (arguments S L layoutHeader cover counter h J K) μ T Q) :
    Meets lim program 138 d
      [selectionHeader,layoutHeader,h,J,K,BlockSourceEncoding.modulus h J,cover,counter]
      μ (T+4000) Q := by
  have hs0 : μ (((selectionHeader : ℤ)+0).toNat)=S.av := by
    rw [show ((selectionHeader : ℤ)+0).toNat=selectionHeader+0 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 0) (by simp [record]) 0
  have hs1 : μ (((selectionHeader : ℤ)+1).toNat)=(S.owner : ℤ) := by
    rw [show ((selectionHeader : ℤ)+1).toNat=selectionHeader+1 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 1) (by simp [record]) 0
  have hs2 : μ (((selectionHeader : ℤ)+2).toNat)=(S.bandB : ℤ) := by
    rw [show ((selectionHeader : ℤ)+2).toNat=selectionHeader+2 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 2) (by simp [record]) 0
  have hs3 : μ (((selectionHeader : ℤ)+3).toNat)=(S.bandC : ℤ) := by
    rw [show ((selectionHeader : ℤ)+3).toNat=selectionHeader+3 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 3) (by simp [record]) 0
  have hs4 : μ (((selectionHeader : ℤ)+4).toNat)=(S.catalog : ℤ) := by
    rw [show ((selectionHeader : ℤ)+4).toNat=selectionHeader+4 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 4) (by simp [record]) 0
  have hs5 : μ (((selectionHeader : ℤ)+5).toNat)=(S.srcL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+5).toNat=selectionHeader+5 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 5) (by simp [record]) 0
  have hs6 : μ (((selectionHeader : ℤ)+6).toNat)=(S.srcR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+6).toNat=selectionHeader+6 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 6) (by simp [record]) 0
  have hs7 : μ (((selectionHeader : ℤ)+7).toNat)=(S.offsetsL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+7).toNat=selectionHeader+7 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 7) (by simp [record]) 0
  have hs8 : μ (((selectionHeader : ℤ)+8).toNat)=(S.flatL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+8).toNat=selectionHeader+8 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 8) (by simp [record]) 0
  have hs9 : μ (((selectionHeader : ℤ)+9).toNat)=(S.offsetsR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+9).toNat=selectionHeader+9 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 9) (by simp [record]) 0
  have hs10 : μ (((selectionHeader : ℤ)+10).toNat)=(S.flatR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+10).toNat=selectionHeader+10 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 10) (by simp [record]) 0
  have hs11 : μ (((selectionHeader : ℤ)+11).toNat)=(S.NL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+11).toNat=selectionHeader+11 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 11) (by simp [record]) 0
  have hs12 : μ (((selectionHeader : ℤ)+12).toNat)=(S.NR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+12).toNat=selectionHeader+12 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 12) (by simp [record]) 0
  have hs13 : μ (((selectionHeader : ℤ)+13).toNat)=(S.baseL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+13).toNat=selectionHeader+13 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 13) (by simp [record]) 0
  have hs14 : μ (((selectionHeader : ℤ)+14).toNat)=(S.baseR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+14).toNat=selectionHeader+14 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 14) (by simp [record]) 0
  have hs15 : μ (((selectionHeader : ℤ)+15).toNat)=(S.occ : ℤ) := by
    rw [show ((selectionHeader : ℤ)+15).toNat=selectionHeader+15 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 15) (by simp [record]) 0
  have hs16 : μ (((selectionHeader : ℤ)+16).toNat)=(S.maps : ℤ) := by
    rw [show ((selectionHeader : ℤ)+16).toNat=selectionHeader+16 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 16) (by simp [record]) 0
  have hs17 : μ (((selectionHeader : ℤ)+17).toNat)=(S.candidates : ℤ) := by
    rw [show ((selectionHeader : ℤ)+17).toNat=selectionHeader+17 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 17) (by simp [record]) 0
  have hs18 : μ (((selectionHeader : ℤ)+18).toNat)=(S.histL : ℤ) := by
    rw [show ((selectionHeader : ℤ)+18).toNat=selectionHeader+18 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 18) (by simp [record]) 0
  have hs19 : μ (((selectionHeader : ℤ)+19).toNat)=(S.histR : ℤ) := by
    rw [show ((selectionHeader : ℤ)+19).toNat=selectionHeader+19 by omega]
    simpa only [record,List.getD_cons_succ,List.getD_cons_zero] using H.getD (i := 19) (by simp [record]) 0
  have hl0 : μ (((layoutHeader : ℤ)+0).toNat)=(L.root : ℤ) := by
    rw [show ((layoutHeader : ℤ)+0).toNat=layoutHeader+0 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 0) (by simp [values]) 0
  have hl1 : μ (((layoutHeader : ℤ)+1).toNat)=(L.masks : ℤ) := by
    rw [show ((layoutHeader : ℤ)+1).toNat=layoutHeader+1 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 1) (by simp [values]) 0
  have hl2 : μ (((layoutHeader : ℤ)+2).toNat)=(L.childL : ℤ) := by
    rw [show ((layoutHeader : ℤ)+2).toNat=layoutHeader+2 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 2) (by simp [values]) 0
  have hl3 : μ (((layoutHeader : ℤ)+3).toNat)=(L.childR : ℤ) := by
    rw [show ((layoutHeader : ℤ)+3).toNat=layoutHeader+3 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 3) (by simp [values]) 0
  have hl4 : μ (((layoutHeader : ℤ)+4).toNat)=(L.counts : ℤ) := by
    rw [show ((layoutHeader : ℤ)+4).toNat=layoutHeader+4 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 4) (by simp [values]) 0
  have hl5 : μ (((layoutHeader : ℤ)+5).toNat)=(L.selected : ℤ) := by
    rw [show ((layoutHeader : ℤ)+5).toNat=layoutHeader+5 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 5) (by simp [values]) 0
  have hl6 : μ (((layoutHeader : ℤ)+6).toNat)=(L.maskBase : ℤ) := by
    rw [show ((layoutHeader : ℤ)+6).toNat=layoutHeader+6 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 6) (by simp [values]) 0
  have hl7 : μ (((layoutHeader : ℤ)+7).toNat)=(L.terminalMasks : ℤ) := by
    rw [show ((layoutHeader : ℤ)+7).toNat=layoutHeader+7 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 7) (by simp [values]) 0
  have hl8 : μ (((layoutHeader : ℤ)+8).toNat)=(L.masksL : ℤ) := by
    rw [show ((layoutHeader : ℤ)+8).toNat=layoutHeader+8 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 8) (by simp [values]) 0
  have hl9 : μ (((layoutHeader : ℤ)+9).toNat)=(L.masksR : ℤ) := by
    rw [show ((layoutHeader : ℤ)+9).toNat=layoutHeader+9 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 9) (by simp [values]) 0
  have hl10 : μ (((layoutHeader : ℤ)+10).toNat)=(L.base : ℤ) := by
    rw [show ((layoutHeader : ℤ)+10).toNat=layoutHeader+10 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 10) (by simp [values]) 0
  have hl11 : μ (((layoutHeader : ℤ)+11).toNat)=(L.bitBase : ℤ) := by
    rw [show ((layoutHeader : ℤ)+11).toNat=layoutHeader+11 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 11) (by simp [values]) 0
  have hl12 : μ (((layoutHeader : ℤ)+12).toNat)=(L.rowOut : ℤ) := by
    rw [show ((layoutHeader : ℤ)+12).toNat=layoutHeader+12 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 12) (by simp [values]) 0
  have hl13 : μ (((layoutHeader : ℤ)+13).toNat)=(L.work : ℤ) := by
    rw [show ((layoutHeader : ℤ)+13).toNat=layoutHeader+13 by omega]
    simpa only [values,List.map_cons,List.map_nil,List.getD_cons_succ,List.getD_cons_zero] using HL.getD (i := 13) (by simp [values]) 0
  have hv0 : |S.av|≤lim.word := hselected _ (by simp [record])
  have hv1 : (S.owner : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.owner : ℤ) (by simp [record])
  have hv2 : (S.bandB : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.bandB : ℤ) (by simp [record])
  have hv3 : (S.bandC : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.bandC : ℤ) (by simp [record])
  have hv4 : (S.catalog : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.catalog : ℤ) (by simp [record])
  have hv5 : (S.srcL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.srcL : ℤ) (by simp [record])
  have hv6 : (S.srcR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.srcR : ℤ) (by simp [record])
  have hv7 : (S.offsetsL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.offsetsL : ℤ) (by simp [record])
  have hv8 : (S.flatL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.flatL : ℤ) (by simp [record])
  have hv9 : (S.offsetsR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.offsetsR : ℤ) (by simp [record])
  have hv10 : (S.flatR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.flatR : ℤ) (by simp [record])
  have hv11 : (S.NL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.NL : ℤ) (by simp [record])
  have hv12 : (S.NR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.NR : ℤ) (by simp [record])
  have hv13 : (S.baseL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.baseL : ℤ) (by simp [record])
  have hv14 : (S.baseR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.baseR : ℤ) (by simp [record])
  have hv15 : (S.occ : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.occ : ℤ) (by simp [record])
  have hv16 : (S.maps : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.maps : ℤ) (by simp [record])
  have hv17 : (S.candidates : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.candidates : ℤ) (by simp [record])
  have hv18 : (S.histL : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.histL : ℤ) (by simp [record])
  have hv19 : (S.histR : ℤ)≤lim.word := by simpa only [Int.natCast_nonneg,abs_of_nonneg] using hselected (S.histR : ℤ) (by simp [record])
  have hw0 : L.root≤lim.space := hlayout _ (by simp [values])
  have hw1 : L.masks≤lim.space := hlayout _ (by simp [values])
  have hw2 : L.childL≤lim.space := hlayout _ (by simp [values])
  have hw3 : L.childR≤lim.space := hlayout _ (by simp [values])
  have hw4 : L.counts≤lim.space := hlayout _ (by simp [values])
  have hw5 : L.selected≤lim.space := hlayout _ (by simp [values])
  have hw6 : L.maskBase≤lim.space := hlayout _ (by simp [values])
  have hw7 : L.terminalMasks≤lim.space := hlayout _ (by simp [values])
  have hw8 : L.masksL≤lim.space := hlayout _ (by simp [values])
  have hw9 : L.masksR≤lim.space := hlayout _ (by simp [values])
  have hw10 : L.base≤lim.space := hlayout _ (by simp [values])
  have hw11 : L.bitBase≤lim.space := hlayout _ (by simp [values])
  have hw12 : L.rowOut≤lim.space := hlayout _ (by simp [values])
  have hw13 : L.work≤lim.space := hlayout _ (by simp [values])
  have hs' := hs
  unfold space numericExtra at hs'
  have hprimeZ : μ (((cover : ℤ)+6).toNat)=(localPrime h : ℤ) := by
    rw [show ((cover : ℤ)+6).toNat=cover+6 by omega]; exact hprime
  have hcapZ : μ (((cover : ℤ)+7).toNat)=(localBucketCap h : ℤ) := by
    rw [show ((cover : ℤ)+7).toNat=cover+7 by omega]; exact hcap
  have hcutZ : (J : ℤ)*(2*(h : ℤ))=(sourceCut h J : ℤ) := by simp [sourceCut]; ring
  have hcutNonneg : (0 : ℤ)≤(J : ℤ)*(2*(h : ℤ)) := by positivity
  have hcutWord : (J : ℤ)*(2*(h : ℤ))≤lim.word := by
    rw [hcutZ]
    exact (Int.ofNat_le.mpr (by omega : sourceCut h J≤lim.space)).trans hw
  have hcutNonneg' : (0 : ℤ)≤2*(h : ℤ)*(J : ℤ) := by positivity
  have hcutWord' : 2*(h : ℤ)*(J : ℤ)≤lim.word := by
    nlinarith only [hcutWord]
  have hrawZ : (layoutHeader : ℤ)+18+(J : ℤ)=(rawRows layoutHeader J : ℤ) := by
    simp [rawRows,decoded]; ring
  have hpackedZ : (layoutHeader : ℤ)+38+2*(J : ℤ)=(packed layoutHeader J : ℤ) := by
    simp [packed,access,decoded]; ring
  have hs0Nat : μ selectionHeader=S.av := by simpa only [add_zero,Int.toNat_natCast] using hs0
  have hl0Nat : μ layoutHeader=(L.root : ℤ) := by simpa only [add_zero,Int.toNat_natCast] using hl0
  have hs1Nat : μ (selectionHeader+1)=(S.owner : ℤ) := by
    rw [show selectionHeader+1=((selectionHeader : ℤ)+1).toNat by omega]; exact hs1
  have hs2Nat : μ (selectionHeader+2)=(S.bandB : ℤ) := by
    rw [show selectionHeader+2=((selectionHeader : ℤ)+2).toNat by omega]; exact hs2
  have hs3Nat : μ (selectionHeader+3)=(S.bandC : ℤ) := by
    rw [show selectionHeader+3=((selectionHeader : ℤ)+3).toNat by omega]; exact hs3
  have hs4Nat : μ (selectionHeader+4)=(S.catalog : ℤ) := by
    rw [show selectionHeader+4=((selectionHeader : ℤ)+4).toNat by omega]; exact hs4
  have hs5Nat : μ (selectionHeader+5)=(S.srcL : ℤ) := by
    rw [show selectionHeader+5=((selectionHeader : ℤ)+5).toNat by omega]; exact hs5
  have hs6Nat : μ (selectionHeader+6)=(S.srcR : ℤ) := by
    rw [show selectionHeader+6=((selectionHeader : ℤ)+6).toNat by omega]; exact hs6
  have hs7Nat : μ (selectionHeader+7)=(S.offsetsL : ℤ) := by
    rw [show selectionHeader+7=((selectionHeader : ℤ)+7).toNat by omega]; exact hs7
  have hs8Nat : μ (selectionHeader+8)=(S.flatL : ℤ) := by
    rw [show selectionHeader+8=((selectionHeader : ℤ)+8).toNat by omega]; exact hs8
  have hs9Nat : μ (selectionHeader+9)=(S.offsetsR : ℤ) := by
    rw [show selectionHeader+9=((selectionHeader : ℤ)+9).toNat by omega]; exact hs9
  have hs10Nat : μ (selectionHeader+10)=(S.flatR : ℤ) := by
    rw [show selectionHeader+10=((selectionHeader : ℤ)+10).toNat by omega]; exact hs10
  have hs11Nat : μ (selectionHeader+11)=(S.NL : ℤ) := by
    rw [show selectionHeader+11=((selectionHeader : ℤ)+11).toNat by omega]; exact hs11
  have hs12Nat : μ (selectionHeader+12)=(S.NR : ℤ) := by
    rw [show selectionHeader+12=((selectionHeader : ℤ)+12).toNat by omega]; exact hs12
  have hs13Nat : μ (selectionHeader+13)=(S.baseL : ℤ) := by
    rw [show selectionHeader+13=((selectionHeader : ℤ)+13).toNat by omega]; exact hs13
  have hs14Nat : μ (selectionHeader+14)=(S.baseR : ℤ) := by
    rw [show selectionHeader+14=((selectionHeader : ℤ)+14).toNat by omega]; exact hs14
  have hs15Nat : μ (selectionHeader+15)=(S.occ : ℤ) := by
    rw [show selectionHeader+15=((selectionHeader : ℤ)+15).toNat by omega]; exact hs15
  have hs16Nat : μ (selectionHeader+16)=(S.maps : ℤ) := by
    rw [show selectionHeader+16=((selectionHeader : ℤ)+16).toNat by omega]; exact hs16
  have hs17Nat : μ (selectionHeader+17)=(S.candidates : ℤ) := by
    rw [show selectionHeader+17=((selectionHeader : ℤ)+17).toNat by omega]; exact hs17
  have hs18Nat : μ (selectionHeader+18)=(S.histL : ℤ) := by
    rw [show selectionHeader+18=((selectionHeader : ℤ)+18).toNat by omega]; exact hs18
  have hs19Nat : μ (selectionHeader+19)=(S.histR : ℤ) := by
    rw [show selectionHeader+19=((selectionHeader : ℤ)+19).toNat by omega]; exact hs19
  have hl1Nat : μ (layoutHeader+1)=(L.masks : ℤ) := by
    rw [show layoutHeader+1=((layoutHeader : ℤ)+1).toNat by omega]; exact hl1
  have hl2Nat : μ (layoutHeader+2)=(L.childL : ℤ) := by
    rw [show layoutHeader+2=((layoutHeader : ℤ)+2).toNat by omega]; exact hl2
  have hl3Nat : μ (layoutHeader+3)=(L.childR : ℤ) := by
    rw [show layoutHeader+3=((layoutHeader : ℤ)+3).toNat by omega]; exact hl3
  have hl4Nat : μ (layoutHeader+4)=(L.counts : ℤ) := by
    rw [show layoutHeader+4=((layoutHeader : ℤ)+4).toNat by omega]; exact hl4
  have hl5Nat : μ (layoutHeader+5)=(L.selected : ℤ) := by
    rw [show layoutHeader+5=((layoutHeader : ℤ)+5).toNat by omega]; exact hl5
  have hl6Nat : μ (layoutHeader+6)=(L.maskBase : ℤ) := by
    rw [show layoutHeader+6=((layoutHeader : ℤ)+6).toNat by omega]; exact hl6
  have hl7Nat : μ (layoutHeader+7)=(L.terminalMasks : ℤ) := by
    rw [show layoutHeader+7=((layoutHeader : ℤ)+7).toNat by omega]; exact hl7
  have hl8Nat : μ (layoutHeader+8)=(L.masksL : ℤ) := by
    rw [show layoutHeader+8=((layoutHeader : ℤ)+8).toNat by omega]; exact hl8
  have hl9Nat : μ (layoutHeader+9)=(L.masksR : ℤ) := by
    rw [show layoutHeader+9=((layoutHeader : ℤ)+9).toNat by omega]; exact hl9
  have hl10Nat : μ (layoutHeader+10)=(L.base : ℤ) := by
    rw [show layoutHeader+10=((layoutHeader : ℤ)+10).toNat by omega]; exact hl10
  have hl11Nat : μ (layoutHeader+11)=(L.bitBase : ℤ) := by
    rw [show layoutHeader+11=((layoutHeader : ℤ)+11).toNat by omega]; exact hl11
  have hl12Nat : μ (layoutHeader+12)=(L.rowOut : ℤ) := by
    rw [show layoutHeader+12=((layoutHeader : ℤ)+12).toNat by omega]; exact hl12
  have hl13Nat : μ (layoutHeader+13)=(L.work : ℤ) := by
    rw [show layoutHeader+13=((layoutHeader : ℤ)+13).toNat by omega]; exact hl13
  apply Meets.of_body (p := 138) (by rfl : program[138]?=some (body 137))
  unfold body
  light_set (S.av : ℤ) using hs0Nat
  light_set (S.owner : ℕ) using hs1,hs1Nat
  light_set (S.bandB : ℕ) using hs2,hs2Nat
  light_set (S.bandC : ℕ) using hs3,hs3Nat
  light_set (S.catalog : ℕ) using hs4,hs4Nat
  light_set (S.srcL : ℕ) using hs5,hs5Nat
  light_set (S.srcR : ℕ) using hs6,hs6Nat
  light_set (S.offsetsL : ℕ) using hs7,hs7Nat
  light_set (S.flatL : ℕ) using hs8,hs8Nat
  light_set (S.offsetsR : ℕ) using hs9,hs9Nat
  light_set (S.flatR : ℕ) using hs10,hs10Nat
  light_set (S.NL : ℕ) using hs11,hs11Nat
  light_set (S.NR : ℕ) using hs12,hs12Nat
  light_set (S.baseL : ℕ) using hs13,hs13Nat
  light_set (S.baseR : ℕ) using hs14,hs14Nat
  light_set (S.occ : ℕ) using hs15,hs15Nat
  light_set (S.maps : ℕ) using hs16,hs16Nat
  light_set (S.candidates : ℕ) using hs17,hs17Nat
  light_set (S.histL : ℕ) using hs18,hs18Nat
  light_set (S.histR : ℕ) using hs19,hs19Nat
  light_set (L.root : ℕ) using hl0Nat
  light_set (L.masks : ℕ) using hl1,hl1Nat
  light_set (L.childL : ℕ) using hl2,hl2Nat
  light_set (L.childR : ℕ) using hl3,hl3Nat
  light_set (L.counts : ℕ) using hl4,hl4Nat
  light_set (L.selected : ℕ) using hl5,hl5Nat
  light_set (L.maskBase : ℕ) using hl6,hl6Nat
  light_set (L.terminalMasks : ℕ) using hl7,hl7Nat
  light_set (L.masksL : ℕ) using hl8,hl8Nat
  light_set (L.masksR : ℕ) using hl9,hl9Nat
  light_set (L.base : ℕ) using hl10,hl10Nat
  light_set (L.bitBase : ℕ) using hl11,hl11Nat
  light_set (L.rowOut : ℕ) using hl12,hl12Nat
  light_set (L.work : ℕ) using hl13,hl13Nat
  light_set (localPrime h : ℕ) using hprimeZ
  light_set (localBucketCap h : ℕ) using hcapZ
  light_set (512*h : ℕ)
  light_set (sourceCut h J : ℕ) using hcutZ
  light_set (rawRows layoutHeader J : ℕ) using hrawZ,rawRows,decoded
  light_set (packed layoutHeader J : ℕ) using hpackedZ,packed,access,decoded
  have hreportRun := hreport.append [body 137]
  change Meets lim program 137 (d+1) _ μ T Q at hreportRun
  light_call hreportRun using arguments with result ν hpost
  exact hpost

end ThreeSum.LightReportingWantedRecordCall

