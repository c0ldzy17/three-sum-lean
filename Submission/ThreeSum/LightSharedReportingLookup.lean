import Submission.ThreeSum.SharedReportingBankAccess

/-! # Actual constant-time lookup of one retained shared catalog row -/

namespace ThreeSum.LightSharedReportingLookup

open Light SharedReportingBankRows SharedReportingBankHeader SharedReportingBankAccess

set_option maxHeartbeats 1900000
set_option maxRecDepth 10000

/-- Bank header, decoded occurrence code, B band, C band. -/
def body : Stmt :=
  .set 4 (M (v 0)) ;;
  .set 5 (M (v 0 +' k 2)) ;;
  .set 6 (M (v 0 +' k 4)) ;;
  .set 7 (M (v 0 +' k 5)) ;;
  .set 8 (v 1 *' v 6 +' v 2) ;;
  .set 9 (v 8 *' v 7 +' v 3) ;;
  .set 0 (v 4 +' k 5 *' v 5 *' v 9)

def program : Program := [body]

theorem program_meets {lim : Limits} {μ : ℕ → ℤ} {fB fC : ℕ → ℤ}
    {free h J NB NC g s i j d : ℕ} {p shift : ℤ}
    (H : Stored μ free h J NB NC g fB fC p shift)
    (hs : s < LightBlockSourceCatalog.count h J) (hi : i < BandPartition.size NB g)
    (hj : j < BandPartition.size NC g) (hw : (lim.space : ℤ) ≤ lim.word)
    (hspace : finish free h J NB NC g ≤ lim.space) :
    Meets lim program 0 d [free,s,i,j] μ 500
      (fun result ν => result=(recordAt free J NB NC g s i j : ℤ) ∧ ν=μ) := by
  have hspos : 0 < LightBlockSourceCatalog.count h J := by omega
  have hbpos : 0 < BandPartition.size NB g := by omega
  have hcpos : 0 < BandPartition.size NC g := by omega
  have hPpos : 0 < total h J NB NC g := Nat.mul_pos (Nat.mul_pos hspos hbpos) hcpos
  have hKpos := levels_pos J
  have hmeta := (payload_le_finish free h J NB NC g).trans hspace
  have hfree : free+9 ≤ lim.space := (records_le_payload free h J NB NC g).trans hmeta
  have hP : total h J NB NC g ≤ lim.space := by
    have hh := Nat.le_mul_of_pos_left (total h J NB NC g) (show 0 < 5*levels J by omega)
    unfold payload at hmeta
    omega
  have hK : 5*levels J ≤ lim.space := by
    have hh := Nat.le_mul_of_pos_right (5*levels J) hPpos
    unfold payload at hmeta
    omega
  have hSnb : LightBlockSourceCatalog.count h J*BandPartition.size NB g ≤ total h J NB NC g :=
    Nat.le_mul_of_pos_right _ hcpos
  have hS : LightBlockSourceCatalog.count h J ≤ lim.space :=
    ((Nat.le_mul_of_pos_right _ hbpos).trans hSnb).trans hP
  have hnb : BandPartition.size NB g ≤ lim.space :=
    ((Nat.le_mul_of_pos_left _ hspos).trans hSnb).trans hP
  have hnc : BandPartition.size NC g ≤ lim.space :=
    (Nat.le_mul_of_pos_left _ (Nat.mul_pos hspos hbpos)).trans hP
  have hx : s*BandPartition.size NB g+i < LightBlockSourceCatalog.count h J*BandPartition.size NB g := calc
    _ < s*BandPartition.size NB g+BandPartition.size NB g := Nat.add_lt_add_left hi _
    _ = (s+1)*BandPartition.size NB g := by ring
    _ ≤ LightBlockSourceCatalog.count h J*BandPartition.size NB g := Nat.mul_le_mul_right _ hs
  have hxSpace := (hx.trans_le hSnb).trans_le hP
  have hq : slot NB NC g s i j < total h J NB NC g := rank_lt hs hi hj
  have hqSpace := hq.trans_le hP
  have hrecord := (record_end (free := free) (J := J) hs hi hj).trans hmeta
  have hprod1NZ : (0 : ℤ) ≤ (s : ℤ)*(BandPartition.size NB g : ℤ) := by positivity
  have hprod1Word : (s : ℤ)*(BandPartition.size NB g : ℤ)+(i : ℤ) ≤ lim.word := by
    exact_mod_cast (Int.ofNat_le.mpr hxSpace.le).trans hw
  have hprod2NZ : (0 : ℤ) ≤ ((s : ℤ)*(BandPartition.size NB g : ℤ)+(i : ℤ))*(BandPartition.size NC g : ℤ) := by positivity
  have hprod2Word : ((s : ℤ)*(BandPartition.size NB g : ℤ)+(i : ℤ))*(BandPartition.size NC g : ℤ)+(j : ℤ) ≤ lim.word := by
    simpa only [slot,rank,Nat.cast_add,Nat.cast_mul] using (Int.ofNat_le.mpr hqSpace.le).trans hw
  have hrecordNZ : (0 : ℤ) ≤ 5*(levels J : ℤ)*(slot NB NC g s i j : ℤ) := by positivity
  have hrecordWord : (records free : ℤ)+5*(levels J : ℤ)*(slot NB NC g s i j : ℤ) ≤ lim.word := by
    simpa only [recordAt,rowRecord,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using
      (Int.ofNat_le.mpr (show recordAt free J NB NC g s i j ≤ lim.space by omega)).trans hw
  obtain ⟨hreadRecords,_,hreadK,_,hreadB,hreadC,_⟩ := header_reads H
  have haK : ((free : ℤ)+2).toNat=free+2 := by omega
  have haB : ((free : ℤ)+4).toNat=free+4 := by omega
  have haC : ((free : ℤ)+5).toNat=free+5 := by omega
  apply Meets.of_body (p := 0) (by rfl : program[0]?=some body)
  unfold body
  light_set (records free : ℕ) using hreadRecords,records
  light_set (levels J : ℕ) using hreadK,haK
  light_set (BandPartition.size NB g : ℕ) using hreadB,haB
  light_set (BandPartition.size NC g : ℕ) using hreadC,haC
  light_set (s*BandPartition.size NB g+i : ℕ)
  light_set (slot NB NC g s i j : ℕ) using slot,rank
  light_set (recordAt free J NB NC g s i j : ℕ) using recordAt,rowRecord
  exact ⟨rfl,rfl⟩

end ThreeSum.LightSharedReportingLookup
