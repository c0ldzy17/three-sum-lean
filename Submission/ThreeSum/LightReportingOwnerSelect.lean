import Submission.ThreeSum.BandRawAIndex

/-!
# Actual owner and original A-value selection by physical incidence index

Four retained cells give the exact original A value, physical owner slot,
and its independent B/C bands. Equal values and repeated owner-domain
incidences retain their separate physical indices.
-/

namespace ThreeSum.LightReportingOwnerSelect

open Light BandRawA BandCandidateRows

set_option maxHeartbeats 1800000
set_option maxRecDepth 10000
set_option linter.unusedVariables false

/-- Packed A values, owner labels, owner records, decoded incidence, output. -/
def body : Stmt :=
  .set 5 (M (v 0 +' v 3)) ;;
  .set 6 (M (v 1 +' v 3)) ;;
  .set 7 (M (v 2 +' k 4 *' v 6 +' k 2)) ;;
  .set 8 (M (v 2 +' k 4 *' v 6 +' k 3)) ;;
  .store (v 4) (v 5) ;;
  .store (v 4 +' k 1) (v 6) ;;
  .store (v 4 +' k 2) (v 7) ;;
  .store (v 4 +' k 3) (v 8) ;;
  .set 0 (v 4)

def program : Program := [body]

def row (f : ℕ→ℤ) (n g : ℕ) (rs : List Record) (i : ℕ) : List ℤ :=
  [f (labelAt n g rs i).position,(labelAt n g rs i).owner,
    (ownerRecord n g rs i).b,(ownerRecord n g rs i).c]

theorem program_meets {lim : Limits} {μ : ℕ→ℤ} {f : ℕ→ℤ}
    {n g vals owners positions records i dst d : ℕ} {rs : List Record}
    (H : Stored μ vals owners positions f (items n g rs))
    (HR : Seg μ records (cells rs)) (hi : i<(items n g rs).length)
    (hw : (lim.space : ℤ)≤lim.word)
    (hvals : vals+(items n g rs).length≤lim.space)
    (howners : owners+(items n g rs).length≤lim.space)
    (hrecords : records+4*rs.length≤lim.space)
    (hout : dst+4≤lim.space)
    (hvalue : |f (labelAt n g rs i).position|≤lim.word)
    (hB : (ownerRecord n g rs i).b≤lim.space) (hC : (ownerRecord n g rs i).c≤lim.space) :
    Meets lim program 0 d [vals,owners,records,i,dst] μ 700
      (fun result ν => result=(dst : ℤ) ∧ Seg ν dst (row f n g rs i) ∧ SameOutside μ ν dst 4) := by
  obtain ⟨hreadVal,hreadOwner,_⟩ := H.read hi
  have howner := (at_bounds hi).1
  have hfields := record_fields (seg_record HR howner)
  have hreadB : μ (records+4*(labelAt n g rs i).owner+2)=((ownerRecord n g rs i).b : ℤ) := hfields.2.2.1
  have hreadC : μ (records+4*(labelAt n g rs i).owner+3)=((ownerRecord n g rs i).c : ℤ) := hfields.2.2.2
  have haddrB : ((records : ℤ)+4*((labelAt n g rs i).owner : ℤ)+2).toNat=
      records+4*(labelAt n g rs i).owner+2 := by omega
  have haddrC : ((records : ℤ)+4*((labelAt n g rs i).owner : ℤ)+3).toNat=
      records+4*(labelAt n g rs i).owner+3 := by omega
  apply Meets.of_body (p := 0) (by rfl : program[0]?=some body)
  unfold body
  light_set (f (labelAt n g rs i).position) using hreadVal
  light_set ((labelAt n g rs i).owner : ℕ) using hreadOwner
  light_set ((ownerRecord n g rs i).b : ℕ) using hreadB,haddrB
  light_set ((ownerRecord n g rs i).c : ℕ) using hreadC,haddrC
  light_store dst (f (labelAt n g rs i).position)
  light_store (dst+1) ((labelAt n g rs i).owner : ℕ)
  light_store (dst+2) ((ownerRecord n g rs i).b : ℕ)
  light_store (dst+3) ((ownerRecord n g rs i).c : ℕ)
  light_set (dst : ℕ)
  refine ⟨rfl,?_,?_⟩
  · intro t ht
    have ht' : t<4 := by simpa only [row,List.length_cons,List.length_nil] using ht
    interval_cases t <;> simp [row]
  · intro a ha
    dsimp only
    repeat rw [Function.update_of_ne (by omega)]

end ThreeSum.LightReportingOwnerSelect
