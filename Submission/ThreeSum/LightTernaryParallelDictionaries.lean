import Submission.ThreeSum.LightFixedRadixDictionary
import Submission.ThreeSum.ReportingHostRelocation

namespace ThreeSum.LightTernaryParallelDictionaries
open Light RadixKeyLists
set_option maxHeartbeats 3000000
set_option maxRecDepth 16000
variable {lim : Limits}

def libraries (xs ys zs : List ℤ) : Program := ReportingHostRelocation.program
  (ReportingHostRelocation.program (LightFixedRadixDictionary.program xs)
    (LightFixedRadixDictionary.program ys)) (LightFixedRadixDictionary.program zs)

def body : Stmt :=
  .call 4 [v 0,v 1,v 6,v 7] 10 ;;
  .call 9 [v 2,v 3,v 6,v 8] 11 ;;
  .call 14 [v 4,v 5,v 6,v 9] 12 ;;
  .set 0 (v 12)

def program (xs ys zs : List ℤ) : Program := libraries xs ys zs++[body]

def time (xs ys zs : List ℤ) (J : ℕ) : ℕ :=
  LightFixedRadixDictionary.time xs J+LightFixedRadixDictionary.time ys J+
    LightFixedRadixDictionary.time zs J+100

def output (μ : ℕ → ℤ) (dst : ℕ) (xs : List ℤ) (p J : ℕ) : Prop :=
  μ (dst+LightRadixKeys.offset xs.length J)=((xs.length^J : ℕ) : ℤ) ∧
  Seg μ (dst+LightRadixKeys.offset xs.length J+1) (values (p : ℤ) xs J)

theorem program_meets (xs ys zs : List ℤ)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+xs.length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 xs.length J ≤ base1)
    (hbase1 : base1+ys.length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 ys.length J ≤ base2)
    (hbase2 : base2+zs.length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 zs.length J ≤ lim.space)
    (hm0 : 0 < xs.length) (hm1 : 0 < ys.length) (hm2 : 0 < zs.length)
    (hb0 : ∀ x ∈ xs, |x| ≤ (U0 : ℤ))
    (hb1 : ∀ x ∈ ys, |x| ≤ (U1 : ℤ))
    (hb2 : ∀ x ∈ zs, |x| ≤ (U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    Meets lim (program xs ys zs) 15 d [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2] μ
      (time xs ys zs J)
      (fun r ν => r=((dst2+LightRadixKeys.offset zs.length J : ℕ) : ℤ) ∧
        output ν dst0 xs p0 J ∧ output ν dst1 ys p1 J ∧ output ν dst2 zs p2 J ∧
        Kept μ ν base0) := by
  have hdst2 : dst2 ≤ lim.space := by unfold LightRadixKeys.space at hspace2; omega
  have hspace1 : LightRadixKeys.space dst1 ys.length J ≤ lim.space := by omega
  have hdst1 : dst1 ≤ lim.space := by unfold LightRadixKeys.space at hspace1; omega
  have hspace0 : LightRadixKeys.space dst0 xs.length J ≤ lim.space := by omega
  have h0 := ((LightFixedRadixDictionary.program_meets xs (d := d+1) μ hw hbase0 hm0 hb0 hspace0 hw0 (by omega)).append
    (LightFixedRadixDictionary.program ys |>.map (ReportingHostRelocation.relocate 5))).append
      ((LightFixedRadixDictionary.program zs |>.map (ReportingHostRelocation.relocate 10))++[body])
  have h0' : Meets lim (program xs ys zs) 4 (d+1) [base0,dst0,J,p0] μ
      (LightFixedRadixDictionary.time xs J)
      (fun r ν => r=((dst0+LightRadixKeys.offset xs.length J : ℕ) : ℤ) ∧
        output ν dst0 xs p0 J ∧ Kept μ ν base0) := by
    simpa only [program,libraries,ReportingHostRelocation.program,List.length_cons,List.length_nil,
      LightFixedRadixDictionary.program,List.length_append,List.length_map,Nat.reduceAdd,List.append_assoc,output,and_assoc] using h0
  apply Meets.of_body (by rfl : (program xs ys zs)[15]?=some body)
  unfold body time
  light_call h0' using LightFixedRadixDictionary.time with head0 μ0 ⟨hhead0,hout0,hkeep0⟩
  have h1 := (ReportingHostRelocation.meets
    (LightFixedRadixDictionary.program_meets ys (d := d+1) μ0 hw hbase1 hm1 hb1 hspace1 hw1 (by omega))
    (LightFixedRadixDictionary.program xs)).append
      ((LightFixedRadixDictionary.program zs |>.map (ReportingHostRelocation.relocate 10))++[body])
  have h1' : Meets lim (program xs ys zs) 9 (d+1) [base1,dst1,J,p1] μ0
      (LightFixedRadixDictionary.time ys J)
      (fun r ν => r=((dst1+LightRadixKeys.offset ys.length J : ℕ) : ℤ) ∧
        output ν dst1 ys p1 J ∧ Kept μ0 ν base1) := by
    simpa only [program,libraries,ReportingHostRelocation.program,List.length_cons,List.length_nil,
      LightFixedRadixDictionary.program,List.length_append,List.length_map,Nat.reduceAdd,List.append_assoc,output,and_assoc] using h1
  light_call h1' using LightFixedRadixDictionary.time with head1 μ1 ⟨hhead1,hout1,hkeep1⟩
  have h2 := (ReportingHostRelocation.meets
    (LightFixedRadixDictionary.program_meets zs (d := d+1) μ1 hw hbase2 hm2 hb2 hspace2 hw2 (by omega))
    (ReportingHostRelocation.program (LightFixedRadixDictionary.program xs)
      (LightFixedRadixDictionary.program ys))).append [body]
  have h2' : Meets lim (program xs ys zs) 14 (d+1) [base2,dst2,J,p2] μ1
      (LightFixedRadixDictionary.time zs J)
      (fun r ν => r=((dst2+LightRadixKeys.offset zs.length J : ℕ) : ℤ) ∧
        output ν dst2 zs p2 J ∧ Kept μ1 ν base2) := by
    simpa only [program,libraries,ReportingHostRelocation.program,List.length_cons,List.length_nil,
      LightFixedRadixDictionary.program,List.length_append,List.length_map,Nat.reduceAdd,List.append_assoc,output,and_assoc] using h2
  light_call h2' using LightFixedRadixDictionary.time with head2 ν ⟨hhead2,hout2,hkeep2⟩
  light_set (dst2+LightRadixKeys.offset zs.length J : ℕ) using hhead2,LightFixedRadixDictionary.time
  change ((dst2+LightRadixKeys.offset zs.length J : ℕ) : ℤ)=_ ∧
    output ν dst0 xs p0 J ∧ output ν dst1 ys p1 J ∧ output ν dst2 zs p2 J ∧ Kept μ ν base0
  refine ⟨rfl,?_,?_,hout2,?_⟩
  · rcases hout0 with ⟨hheader,hseg⟩
    constructor
    · rw [hkeep2 _ (by unfold LightRadixKeys.space at hnext0 hnext1; omega),
        hkeep1 _ (by unfold LightRadixKeys.space at hnext0; omega)]
      exact hheader
    · intro a ha
      rw [hkeep2 _ (by rw [values_length] at ha; unfold LightRadixKeys.space at hnext0 hnext1; omega),
        hkeep1 _ (by rw [values_length] at ha; unfold LightRadixKeys.space at hnext0; omega)]
      exact hseg a ha
  · rcases hout1 with ⟨hheader,hseg⟩
    constructor
    · rw [hkeep2 _ (by unfold LightRadixKeys.space at hnext1; omega)]
      exact hheader
    · intro a ha
      rw [hkeep2 _ (by rw [values_length] at ha; unfold LightRadixKeys.space at hnext1; omega)]
      exact hseg a ha
  · intro a ha
    rw [hkeep2 a (by unfold LightRadixKeys.space at hnext0 hnext1; omega),
      hkeep1 a (by unfold LightRadixKeys.space at hnext0; omega),hkeep0 a ha]

def recordOutput {R : Type*} (μ : ℕ → ℤ) (dst : ℕ) (records : List R)
    (raw : R → ℤ) (p J : ℕ) : Prop :=
  μ (dst+LightRadixKeys.offset records.length J)=((records.length^J : ℕ) : ℤ) ∧
  Seg μ (dst+LightRadixKeys.offset records.length J+1)
    ((tuples records J).map (Radix.positionalHash (p : ℤ) raw))

/-- Three arrays share exactly the same literal record tuple order. Equal
keys or equal map labels retain separate physical tuple occurrences. -/
theorem program_meets_records {R : Type*} (records : List R) (raw0 raw1 raw2 : R → ℤ)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d : ℕ} (μ : ℕ → ℤ)
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hbase0 : base0+records.length ≤ dst0)
    (hnext0 : LightRadixKeys.space dst0 records.length J ≤ base1)
    (hbase1 : base1+records.length ≤ dst1)
    (hnext1 : LightRadixKeys.space dst1 records.length J ≤ base2)
    (hbase2 : base2+records.length ≤ dst2)
    (hspace2 : LightRadixKeys.space dst2 records.length J ≤ lim.space)
    (hm : 0 < records.length)
    (hb0 : ∀ x ∈ records, |raw0 x| ≤ (U0 : ℤ))
    (hb1 : ∀ x ∈ records, |raw1 x| ≤ (U1 : ℤ))
    (hb2 : ∀ x ∈ records, |raw2 x| ≤ (U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ) ≤ lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ) ≤ lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ) ≤ lim.word)
    (hd : d+J+4 ≤ lim.depth) :
    Meets lim (program (records.map raw0) (records.map raw1) (records.map raw2)) 15 d
      [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2] μ
      (time (records.map raw0) (records.map raw1) (records.map raw2) J)
      (fun r ν => r=((dst2+LightRadixKeys.offset records.length J : ℕ) : ℤ) ∧
        recordOutput ν dst0 records raw0 p0 J ∧ recordOutput ν dst1 records raw1 p1 J ∧
        recordOutput ν dst2 records raw2 p2 J ∧ Kept μ ν base0) := by
  have hb (raw : R → ℤ) (U : ℕ) (h : ∀ x ∈ records, |raw x| ≤ (U : ℤ)) :
      ∀ x ∈ records.map raw, |x| ≤ (U : ℤ) := by
    intro x hx
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hx
    exact h a ha
  have h := program_meets (records.map raw0) (records.map raw1) (records.map raw2) μ hw
    (by simpa using hbase0) (by simpa using hnext0) (by simpa using hbase1)
    (by simpa using hnext1) (by simpa using hbase2) (by simpa using hspace2)
    (by simpa using hm) (by simpa using hm) (by simpa using hm)
    (hb raw0 U0 hb0) (hb raw1 U1 hb1) (hb raw2 U2 hb2) hw0 hw1 hw2 hd
  simpa only [output,recordOutput,List.length_map,values_eq_map] using h

end ThreeSum.LightTernaryParallelDictionaries
