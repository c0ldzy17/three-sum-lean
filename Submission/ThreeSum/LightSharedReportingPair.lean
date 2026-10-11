import Submission.ThreeSum.LightSharedReportingLevels
import Submission.ThreeSum.SharedReportingBankSourceBounds

/-! # Load the two independent source-band pointer cells for one shared pair -/

namespace ThreeSum.LightSharedReportingPair

open Light GlobalEncoding BlockIndexedQuery BlockSourceOccurrenceOrder
open SharedReportingBankLayout SharedReportingBankLevels SharedReportingBankSources

set_option maxHeartbeats 2400000
set_option maxRecDepth 11000

/-- h,J,level count,first source bank,source-bank span,occurrence,B band,C
band,local choose/pair counts,metadata row,and first free payload. -/
def body (pLevels : ℕ) : Stmt :=
  .set 12 (v 3 +' v 6 *' v 4 +' k 2 *' v 5) ;;
  .set 13 (v 3 +' v 7 *' v 4 +' k 2 *' v 5 +' k 1) ;;
  .call pLevels [v 0,v 1,v 2,v 12,v 13,v 8,v 9,v 10,v 11] 14 ;;
  .set 0 (v 14)

def time (h J K : ℕ) : ℕ := LightSharedReportingLevels.time h J K+500
def program : Program := LightSharedReportingLevels.program ++ [body 64]
theorem program_length : program.length=66 := rfl

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {header NB NC g h J occ s i j K record base d : ℕ} {p shift : ℤ}
    (H : SourceBandBankData.Stored μ fB fC header NB NC g h J (2*h*J) occ p shift)
    (hs : s < LightBlockSourceCatalog.count h J)
    (hi : i < SourceBandPairSlices.count NB NC g)
    (hj : j < SourceBandPairSlices.count NB NC g)
    (hw : (lim.space : ℤ) ≤ lim.word) (hK : K ≤ LightSwitchDepth.depth J+1)
    (hsource : SourceBandBankData.finish header NB NC g h J (2*h*J) ≤ record)
    (hrecords : record+5*K ≤ base)
    (R : LightSharedReportingLevels.Resources lim base h J K g g (d+1)) :
    Meets lim program 65 d
      [h,J,K,SourceBandBankData.first header,SourceBandBankLayout.span h J (2*h*J),s,i,j,
        localChoose h,localPairs h,record,base] μ (time h J K)
      (fun result ν => result=(baseAt base h J K : ℤ) ∧
        Built ν record base h J K
          (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
          (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s)) ∧
        Kept μ ν record ∧ KeptBut μ ν base record (5*K)) := by
  have hleft := source_bounds (base := header) (cut := 2*h*J) hi hs
  have hright := source_bounds (base := header) (cut := 2*h*J) hj hs
  have hdata := source_pair H hi hj hs
  have hspace := R.space
  have hdepth := R.widthDepth
  have hstate := R.state
  have hbase : base ≤ lim.space := (Nat.le_add_right _ _).trans hspace
  have hleftAddr : leftCell header h J (2*h*J) i s < record := hleft.1.trans_le hsource
  have hrightAddr : rightCell header h J (2*h*J) j s < record := hright.2.1.trans_le hsource
  have hlNat : SourceBandBankData.first header+i*SourceBandBankLayout.span h J (2*h*J)+2*s < lim.space :=
    hleftAddr.trans_le (by omega)
  have hrNat : SourceBandBankData.first header+j*SourceBandBankLayout.span h J (2*h*J)+2*s+1 < lim.space :=
    hrightAddr.trans_le (by omega)
  have hlZ : (SourceBandBankData.first header : ℤ)+(i : ℤ)*(SourceBandBankLayout.span h J (2*h*J) : ℤ)+2*(s : ℤ) < (lim.space : ℤ) := by
    exact_mod_cast hlNat
  have hrZ : (SourceBandBankData.first header : ℤ)+(j : ℤ)*(SourceBandBankLayout.span h J (2*h*J) : ℤ)+2*(s : ℤ)+1 < (lim.space : ℤ) := by
    exact_mod_cast hrNat
  have hiNZ : (0 : ℤ) ≤ (i : ℤ)*(SourceBandBankLayout.span h J (2*h*J) : ℤ) := by positivity
  have hjNZ : (0 : ℤ) ≤ (j : ℤ)*(SourceBandBankLayout.span h J (2*h*J) : ℤ) := by positivity
  apply Meets.of_body (p := 65) (by rfl : program[65]?=some (body 64))
  unfold body time
  light_set (leftCell header h J (2*h*J) i s : ℕ) using leftCell,bankBase,SourceBandBankLayout.baseAt
  light_set (rightCell header h J (2*h*J) j s : ℕ) using rightCell,bankBase,SourceBandBankLayout.baseAt
  have hc := (LightSharedReportingLevels.program_meets (d := d+1)
    (record := record) (base := base)
    (leftSource p (SourceBandPartition.source NB g i) (fun t : Fin NB => fB t.val) (representative h J s))
    (rightSource p shift (SourceBandPartition.source NC g j) (fun t : Fin NC => fC t.val) (representative h J s))
    hw hK hrecords hleftAddr hrightAddr (hleft.2.2.1.trans hsource) (hright.2.2.2.trans hsource) R
    (fun S _ => left_abs_le p NB g i h J s fB S)
    (fun S _ => right_abs_le p shift NC g j h J s fC S)
    hdata.1 hdata.2.1 hdata.2.2.1 hdata.2.2.2).append [body 64]
  light_call hc with result ν ⟨hresult,hbuilt,hkeep,hkeepBlock⟩
  light_set (baseAt base h J K : ℕ) using hresult
  exact ⟨rfl,hbuilt,hkeep,hkeepBlock⟩

end ThreeSum.LightSharedReportingPair
