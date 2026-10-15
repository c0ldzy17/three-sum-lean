import Submission.ThreeSum.LightSignedFiniteTable
import Submission.ThreeSum.LightRadixKeys

/-! A fixed signed local dictionary followed by runtime radix product generation. -/
namespace ThreeSum.LightFixedRadixDictionary
open Light RadixKeyLists
variable {lim : Limits}
set_option maxHeartbeats 1400000

def body (pTable pKeys : ℕ) : Stmt :=
  .call pTable [v 0] 4 ;;
  .call pKeys [v 0,v 4,v 2,v 3,v 1] 5 ;;
  .set 0 (v 5)

def program (xs : List ℤ) : Program :=
  [LightSignedFiniteTable.body xs,LightRadixKeys.body 1 2,
    LightRadixRows.body 3,LightReportingAffine.body,body 0 1]

def time (xs : List ℤ) (J : ℕ) : ℕ := 7*xs.length+2+LightRadixKeys.time xs.length J+50

theorem program_meets (xs : List ℤ) {base dst p U J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base+xs.length ≤ dst)
    (hm : 0 < xs.length) (hbound : ∀ x ∈ xs, |x| ≤ (U : ℤ))
    (hspace : LightRadixKeys.space dst xs.length J ≤ lim.space)
    (hword : (LightRadixKeys.word p U J : ℤ) ≤ lim.word) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program xs) 4 d [base,dst,J,p] μ (time xs J)
      (fun r ν => r=((dst+LightRadixKeys.offset xs.length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset xs.length J)=((xs.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset xs.length J+1) (values (p : ℤ) xs J) ∧
        Kept μ ν base) := by
  have hdst : dst ≤ lim.space := by unfold LightRadixKeys.space at hspace; omega
  have hU : (U : ℤ) ≤ lim.word := by
    have h : U ≤ LightRadixKeys.word p U J := by unfold LightRadixKeys.word LightRadixRows.word; omega
    exact (Int.ofNat_le.mpr h).trans hword
  have hv : ∀ x ∈ xs, |x| ≤ lim.word := fun x hx => (hbound x hx).trans hU
  have ht := LightSignedFiniteTable.meets (P := program xs) (d := d+1)
    (by rfl : (program xs)[0]? = some (LightSignedFiniteTable.body xs))
    base μ hw (by omega) hv
  apply Meets.of_body (by rfl : (program xs)[4]? = some (body 0 1))
  unfold body time
  light_call ht using LightRadixKeys.time with size μ₁ ⟨hsize,hlocal,hkeepTable⟩
  have hk := LightRadixKeys.meets (P := program xs) (pMain := 1) (pRows := 2) (pAffine := 3)
    (src := base) (dst := dst) (p := p) (U := U) rfl rfl rfl
    xs hw hbase hm hbound J (d+1) μ₁ hspace hword (by omega) hlocal
  light_call hk using hsize,LightRadixKeys.time with result ν ⟨hresult,hheader,hkeys,hkeepKeys⟩
  light_set (dst+LightRadixKeys.offset xs.length J : ℕ) using hresult,LightRadixKeys.time
  refine ⟨rfl,hheader,hkeys,?_⟩
  intro a ha
  exact (hkeepKeys a (by omega)).trans (hkeepTable a (Or.inl ha))

/-- The array's records remain in literal tuple order even when keys agree. -/
theorem program_meets_records {R : Type*} (records : List R) (raw : R → ℤ)
    {base dst p U J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hbase : base+records.length ≤ dst)
    (hm : 0 < records.length) (hbound : ∀ x ∈ records, |raw x| ≤ (U : ℤ))
    (hspace : LightRadixKeys.space dst records.length J ≤ lim.space)
    (hword : (LightRadixKeys.word p U J : ℤ) ≤ lim.word) (hd : d+J+3 ≤ lim.depth) :
    Meets lim (program (records.map raw)) 4 d [base,dst,J,p] μ (time (records.map raw) J)
      (fun r ν => r=((dst+LightRadixKeys.offset records.length J : ℕ) : ℤ) ∧
        ν (dst+LightRadixKeys.offset records.length J)=((records.length^J : ℕ) : ℤ) ∧
        Seg ν (dst+LightRadixKeys.offset records.length J+1)
          ((tuples records J).map (Radix.positionalHash (p : ℤ) raw)) ∧ Kept μ ν base) := by
  have h := program_meets (records.map raw) μ hw (by simpa using hbase) (by simpa using hm)
    (by intro z hz; obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz; exact hbound x hx)
    (by simpa using hspace) hword hd
  simpa only [List.length_map,values_eq_map] using h
end ThreeSum.LightFixedRadixDictionary
