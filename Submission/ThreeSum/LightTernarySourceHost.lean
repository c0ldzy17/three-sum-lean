import Submission.ThreeSum.LightTernaryParallelDictionaries
import Submission.ThreeSum.LightTernaryOriginalJoin
import Submission.ThreeSum.LightTernaryGroupedSources
import Submission.ThreeSum.TernarySourceHostRecords

namespace ThreeSum.LightTernarySourceHost
open Light RadixKeyLists ThreeSum.LightSubsetAddress
set_option maxHeartbeats 4000000
set_option maxRecDepth 20000
variable {lim : Limits}

def joined (xs ys zs : List ℤ) : Program := ReportingHostRelocation.program
  (LightTernaryParallelDictionaries.program xs ys zs) LightTernaryOriginalJoin.program

def libraries (xs ys zs : List ℤ) : Program :=
  ReportingHostRelocation.program (joined xs ys zs) LightTernaryGroupedSources.program

/-- Source tables, runtime radix length/bases, original hash array, join layout,
compact bank layout, weight array and factorial factor. Dictionary array
pointers and the join size/pointer are read from actual returned headers. -/
def body : Stmt :=
  .call 15 [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9] 23 ;;
  .set 24 (M (v 23)) ;;
  .set 25 (v 23 -' v 5) ;;
  .set 26 (v 1 +' v 25 +' k 1) ;;
  .set 27 (v 3 +' v 25 +' k 1) ;;
  .set 28 (v 5 +' v 25 +' k 1) ;;
  .call 27 [v 10,v 26,v 11,v 24,v 12,k 0,v 13] 29 ;;
  .set 30 (M (v 29)) ;;
  .set 31 (M (v 29 +' k 1)) ;;
  .call 28 [v 14,v 15,v 16,v 17,v 31,v 30,v 27,v 24,
    v 18,v 19,v 20,v 11,v 21,v 28,v 22] 32 ;;
  .set 0 (v 19)

def program (xs ys zs : List ℤ) : Program := libraries xs ys zs++[body]
def size (xs : List ℤ) (J : ℕ) : ℕ := xs.length^J
def dictionary (xs : List ℤ) (p J : ℕ) (i : ℕ) : ℤ := (values (p : ℤ) xs J).getD i 0

def count (xs : List ℤ) (p J M NL : ℕ) (input : ℕ → ℤ) : ℕ :=
  WantedResidueKeys.total M input (dictionary xs p J) NL (size xs J) 0

def time (xs ys zs : List ℤ) (p J M NL U L bank groups : ℕ) (input : ℕ → ℤ) : ℕ :=
  LightTernaryParallelDictionaries.time xs ys zs J+
    LightWantedSetup.time M input (dictionary xs p J) NL (size xs J) U 0 0+
    LightTernaryGroupedSources.time L (count xs p J M NL input) bank groups+500

theorem program_meets (xs ys zs : List ℤ) (hxy : ys.length=xs.length) (hxz : zs.length=xs.length)
    {base0 dst0 base1 dst1 base2 dst2 p0 p1 p2 U0 U1 U2 J d
      src NL M free a bank powers W L keyBase valueBase weightBase weightU factor groups U : ℕ}
    (μ : ℕ → ℤ) (input weight : ℕ → ℤ) (codes key group : ℕ → ℕ)
    (hw : (lim.space : ℤ)≤lim.word) (hm : 0<xs.length)
    (hbase0 : base0+xs.length≤dst0)
    (hnext0 : LightRadixKeys.space dst0 xs.length J≤base1)
    (hbase1 : base1+xs.length≤dst1)
    (hnext1 : LightRadixKeys.space dst1 xs.length J≤base2)
    (hbase2 : base2+xs.length≤dst2)
    (hinitEnd : LightRadixKeys.space dst2 xs.length J≤free)
    (hsrc : src+NL≤base0) (hweights : weightBase+NL≤base0)
    (hbank : a+bank≤base0) (hpowerEnd : powers+(W+1)≤base0)
    (hkeyBase : LightWantedSetup.space free M input (dictionary xs p0 J)
      NL (size xs J) U 0 0≤keyBase)
    (hkeyEnd : keyBase+count xs p0 J M NL input≤valueBase)
    (hvalues : valueBase+groups*bank≤lim.space)
    (hb0 : ∀ x∈xs, |x|≤(U0 : ℤ)) (hb1 : ∀ x∈ys, |x|≤(U1 : ℤ))
    (hb2 : ∀ x∈zs, |x|≤(U2 : ℤ))
    (hw0 : (LightRadixKeys.word p0 U0 J : ℤ)≤lim.word)
    (hw1 : (LightRadixKeys.word p1 U1 J : ℤ)≤lim.word)
    (hw2 : (LightRadixKeys.word p2 U2 J : ℤ)≤lim.word)
    (hM : 0<M) (hjoinWord : (LightSourceResidues.word M M U 0 : ℤ)≤lim.word)
    (hlookupWord : ((bank+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hgroupWord : ((groups*bank+1 : ℕ) : ℤ)≤lim.word)
    (hgroupSpace : groups*bank+1≤lim.space)
    (hfactor : (factor : ℤ)≤lim.word)
    (hweighted : (factor : ℤ)*(count xs p0 J M NL input*weightU : ℕ)≤lim.word)
    (hhistWord : ((count xs p0 J M NL input+1 : ℕ) : ℤ)*weightU≤lim.word)
    (hinput : ∀ i<NL, μ (src+i)=input i) (hinputBound : ∀ i<NL, |input i|≤(U : ℤ))
    (hweightRead : ∀ i<NL, μ (weightBase+i)=weight i)
    (hweightBound : ∀ i<NL, |weight i|≤(weightU : ℤ))
    (hglobal : U0*(p0+1)^J≤U)
    (hcodes : ∀ i<bank, μ (a+i)=(codes i : ℤ))
    (hcodeBound : ∀ i<bank, codes i<2^W)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i k, i<k → k<bank → codes i<codes k)
    (hwordCode : ∀ j<size xs J, dictionary ys p1 J j=(codes (key j) : ℤ))
    (hkey : ∀ j<size xs J, key j<bank)
    (hgroupCode : ∀ j<size xs J, dictionary zs p2 J j=(group j : ℤ))
    (hgroup : ∀ j<size xs J, group j<groups)
    (hL : L≤W) (hn : bank<2^L) (hd : d+NL+L+J+8≤lim.depth) :
    Meets lim (program xs ys zs) 34 d
      [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2,src,NL,M,free,
        a,bank,powers,L,keyBase,valueBase,weightBase,factor,groups] μ
      (time xs ys zs p0 J M NL U L bank groups input)
      (fun r ν => r=(valueBase : ℤ) ∧ Kept μ ν base0 ∧
        ∃ ps : List (ℕ × ℕ), ps.length=count xs p0 J M NL input ∧ ps.Nodup ∧
          (∀ i j, (i,j)∈ps ↔ i<NL ∧ j<size xs J ∧ (M : ℤ)∣input i-dictionary xs p0 J j) ∧
          ∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
            LightTernaryWeightedHistogram.total
              (fun i => group (ps.getD i (0,0)).2*bank+key (ps.getD i (0,0)).2)
              (fun i => weight (ps.getD i (0,0)).1) r (count xs p0 J M NL input)) := by
  let NR := size xs J
  let hits := count xs p0 J M NL input
  let pb := LightWantedSetup.pairBase free NL NR M
  have hfreeKey : free≤keyBase := by
    have hp := Nat.le_max_left (LightSourceResidues.space pb M U 0) (pb+2*hits)
    unfold LightWantedSetup.space at hkeyBase
    have hpb : free≤pb := by unfold pb LightWantedSetup.pairBase LightWantedSetup.bucketBase LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightSourceBucketSetup.next; omega
    have hh := (Nat.le_max_right (LightSourceResidues.space pb M U 0) (pb+2*hits)).trans hkeyBase
    omega
  have hkeySpace : keyBase≤lim.space := by omega
  have hinitSpace : LightRadixKeys.space dst2 xs.length J≤lim.space := by omega
  have h1Space : LightRadixKeys.space dst1 xs.length J≤free := by unfold LightRadixKeys.space at hinitEnd; omega
  have h0Space : LightRadixKeys.space dst0 xs.length J≤free := by unfold LightRadixKeys.space at h1Space; omega
  have hDict0End : dst0+LightRadixKeys.offset xs.length J+1+NR≤free := by
    simpa only [LightRadixKeys.space,NR,size] using h0Space
  have hDict1End : dst1+LightRadixKeys.offset xs.length J+1+NR≤free := by
    simpa only [LightRadixKeys.space,NR,size] using h1Space
  have hDict2End : dst2+LightRadixKeys.offset xs.length J+1+NR≤free := by
    simpa only [LightRadixKeys.space,NR,size] using hinitEnd
  have hFreeW : (free : ℤ)≤lim.word := (Int.ofNat_le.mpr (hfreeKey.trans hkeySpace)).trans hw
  have hMW : (M : ℤ)≤lim.word := by unfold LightSourceResidues.word at hjoinWord; omega
  have hdct := (LightTernaryParallelDictionaries.program_meets xs ys zs (d := d+1) μ hw hbase0 hnext0
      (by simpa only [hxy] using hbase1) (by simpa only [hxy] using hnext1)
      (by simpa only [hxz] using hbase2) (by simpa only [hxz] using hinitSpace)
      hm (by omega) (by omega) hb0 hb1 hb2 hw0 hw1 hw2 (by omega)).append
        ((LightTernaryOriginalJoin.program.map (ReportingHostRelocation.relocate 16))++
          (LightTernaryGroupedSources.program.map (ReportingHostRelocation.relocate 28))++[body])
  have hdct' : Meets lim (program xs ys zs) 15 (d+1)
      [base0,dst0,base1,dst1,base2,dst2,J,p0,p1,p2] μ
      (LightTernaryParallelDictionaries.time xs ys zs J)
      (fun r ν => r=((dst2+LightRadixKeys.offset xs.length J : ℕ) : ℤ) ∧
        LightTernaryParallelDictionaries.output ν dst0 xs p0 J ∧
        LightTernaryParallelDictionaries.output ν dst1 ys p1 J ∧
        LightTernaryParallelDictionaries.output ν dst2 zs p2 J ∧ Kept μ ν base0) := by
    simpa only [program,libraries,joined,ReportingHostRelocation.program,
      LightTernaryParallelDictionaries.program,LightTernaryParallelDictionaries.libraries,
      LightFixedRadixDictionary.program,LightTernaryOriginalJoin.program,LightWantedSetup.program_length,
      LightTernaryGroupedSources.program,List.length_cons,List.length_nil,List.length_append,
      List.length_map,Nat.reduceAdd,List.append_assoc,hxz] using hdct
  have hp0 : (p0 : ℤ)≤lim.word := by unfold LightRadixKeys.word LightRadixRows.word at hw0; omega
  have hp1 : (p1 : ℤ)≤lim.word := by unfold LightRadixKeys.word LightRadixRows.word at hw1; omega
  have hp2 : (p2 : ℤ)≤lim.word := by unfold LightRadixKeys.word LightRadixRows.word at hw2; omega
  have hJ : (J : ℤ)≤lim.word := by have hh:=LightRadixKeys.le_offset xs.length J; unfold LightRadixKeys.space at hinitSpace; omega
  have hAllBase : dst2≤lim.space := by unfold LightRadixKeys.space at hinitSpace; omega
  have hAllWord : (dst2 : ℤ)≤lim.word := (Int.ofNat_le.mpr hAllBase).trans hw
  have hSpaceBases0 : dst0≤dst2 := by unfold LightRadixKeys.space at hnext0 hnext1; omega
  have hSpaceBases1 : dst1≤dst2 := by unfold LightRadixKeys.space at hnext1; omega
  have hbase0W : (base0 : ℤ)≤lim.word := by omega
  have hbase1W : (base1 : ℤ)≤lim.word := by omega
  have hbase2W : (base2 : ℤ)≤lim.word := by omega
  have hdst0W : (dst0 : ℤ)≤lim.word := by omega
  have hdst1W : (dst1 : ℤ)≤lim.word := by omega
  apply Meets.of_body (by rfl : (program xs ys zs)[34]?=some body)
  unfold body time
  light_call hdct' using LightWantedSetup.time,LightTernaryGroupedSources.time with head μ0 ⟨hhead,hout0,hout1,hout2,hkeep0⟩
  have hheader : μ0 head.toNat=(NR : ℤ) := by rw [hhead]; simpa only [NR,size,hxz,Int.toNat_natCast] using hout2.1
  have hNR : (NR : ℤ)≤lim.word := by unfold NR size; unfold LightRadixKeys.space at hinitSpace; omega
  have hHeaderAddr : dst2+LightRadixKeys.offset xs.length J<lim.space := by unfold LightRadixKeys.space at hinitSpace; omega
  have hheaderDirect : μ0 (dst2+LightRadixKeys.offset xs.length J)=(NR : ℤ) := by
    simpa only [NR,size,hxz] using hout2.1
  light_set (NR : ℕ) using hheader,hheaderDirect,hhead,hHeaderAddr,LightWantedSetup.time,LightTernaryGroupedSources.time
  light_set (LightRadixKeys.offset xs.length J : ℕ) using hhead,LightWantedSetup.time,LightTernaryGroupedSources.time
  light_set (dst0+LightRadixKeys.offset xs.length J+1 : ℕ) using LightWantedSetup.time,LightTernaryGroupedSources.time
  light_set (dst1+LightRadixKeys.offset xs.length J+1 : ℕ) using LightWantedSetup.time,LightTernaryGroupedSources.time
  light_set (dst2+LightRadixKeys.offset xs.length J+1 : ℕ) using LightWantedSetup.time,LightTernaryGroupedSources.time
  have hinput0 (i : ℕ) (hi : i<NL) : μ0 (src+i)=input i := (hkeep0 _ (by omega)).trans (hinput i hi)
  have hdict0 (j : ℕ) (hj : j<NR) : μ0 (dst0+LightRadixKeys.offset xs.length J+1+j)=dictionary xs p0 J j := by
    unfold dictionary
    rw [List.getD_eq_getElem _ _ (by simpa only [values_length,NR,size] using hj)]
    exact hout0.2 j (by simpa only [values_length,NR,size] using hj)
  have hbound (j : ℕ) (hj : j<NR) : |dictionary xs p0 J j|≤(U : ℤ) := by
    unfold dictionary
    rw [List.getD_eq_getElem _ _ (by simpa only [values_length,NR,size] using hj)]
    exact (values_bounded p0 U0 xs hb0 J _ (List.getElem_mem (by simpa only [values_length,NR,size] using hj))).trans (Int.ofNat_le.mpr hglobal)
  have hjBase := ReportingHostRelocation.meets
    (LightWantedSetup.program_meets (d := d+1) input (dictionary xs p0 J) hw hM
      (by omega : src+NL≤free)
      hDict0End
      (hkeyBase.trans hkeySpace) hjoinWord (by simp) (by omega) hinput0 hdict0 hinputBound hbound)
    (LightTernaryParallelDictionaries.program xs ys zs)
  have hj := hjBase.append ((LightTernaryGroupedSources.program.map (ReportingHostRelocation.relocate 28))++[body])
  have hj' : Meets lim (program xs ys zs) 27 (d+1)
      [src,dst0+LightRadixKeys.offset xs.length J+1,NL,NR,M,0,free] μ0
      (LightWantedSetup.time M input (dictionary xs p0 J) NL NR U 0 0)
      (fun r ν => r=(free : ℤ) ∧ LightWantedSetup.Output ν free M input (dictionary xs p0 J) NL NR 0 ∧ Kept μ0 ν free) := by
    simpa only [program,libraries,joined,ReportingHostRelocation.program,
      LightTernaryParallelDictionaries.program,LightTernaryParallelDictionaries.libraries,
      LightFixedRadixDictionary.program,LightTernaryOriginalJoin.program,LightWantedSetup.program_length,
      LightTernaryGroupedSources.program,List.length_cons,List.length_nil,List.length_append,
      List.length_map,Nat.reduceAdd,List.append_assoc,NR,size,Nat.cast_add,Nat.cast_ofNat,Nat.cast_one] using hj
  light_call hj' using NR,LightWantedSetup.time,LightTernaryGroupedSources.time with res μ1 ⟨hres,houtput,hkeep1⟩
  obtain ⟨hcount,hpairptr,hend,hshift,ps,hlen,hnodup,hmem,hseg⟩ := houtput
  have hcount' : μ1 free=(hits : ℤ) := hcount
  have hpairptr' : μ1 (free+1)=(pb : ℤ) := hpairptr
  have hpairEnd : pb+2*hits≤keyBase := (Nat.le_max_right _ _).trans hkeyBase
  have hpbLower : free+4≤pb := by
    unfold pb LightWantedSetup.pairBase LightWantedSetup.bucketBase LightWantedSetup.rightCodes LightWantedSetup.leftCodes LightSourceBucketSetup.next
    omega
  have hcountW : (hits : ℤ)≤lim.word := by omega
  have hpbW : (pb : ℤ)≤lim.word := by omega
  light_set (hits : ℕ) using NR,hres,hcount',LightTernaryGroupedSources.time
  light_set (pb : ℕ) using NR,hres,hpairptr',LightTernaryGroupedSources.time
  let original := fun i => (ps.getD i (0,0)).1
  let position := fun i => (ps.getD i (0,0)).2
  have hpos (i : ℕ) (hi : i<hits) : original i<NL ∧ position i<NR := by
    have hip : i<ps.length := by omega
    have hpmem : ps.getD i (0,0)∈ps := by rw [List.getD_eq_getElem _ _ hip]; exact List.getElem_mem hip
    exact ⟨(hmem _ _).mp hpmem |>.1,(hmem _ _).mp hpmem |>.2.1⟩
  have hpairRead (i : ℕ) (hi : i<hits) : μ1 (pb+2*i)=(original i : ℤ) ∧ μ1 (pb+2*i+1)=(position i : ℤ) :=
    TernarySourceHostRecords.pair_reads ps μ1 pb hseg i (by omega)
  have hwordRead (i : ℕ) (hi : i<hits) : μ1 (dst1+LightRadixKeys.offset xs.length J+1+position i)=(codes (key (position i)) : ℤ) := by
    rw [hkeep1 _ (by have hh:=(hpos i hi).2; unfold LightRadixKeys.space at h1Space; omega)]
    have hj := (hpos i hi).2
    have hr := hout1.2 (position i) (by simpa only [values_length,hxy,NR,size] using hj)
    rw [← List.getD_eq_getElem _ 0 (by simpa only [values_length,hxy,NR,size] using hj)] at hr
    simpa only [hxy] using hr.trans (hwordCode _ hj)
  have hgroupRead (i : ℕ) (hi : i<hits) : μ1 (dst2+LightRadixKeys.offset xs.length J+1+position i)=(group (position i) : ℤ) := by
    rw [hkeep1 _ (by have hh:=(hpos i hi).2; unfold LightRadixKeys.space at hinitEnd; omega)]
    have hj := (hpos i hi).2
    have hr := hout2.2 (position i) (by simpa only [values_length,hxz,NR,size] using hj)
    rw [← List.getD_eq_getElem _ 0 (by simpa only [values_length,hxz,NR,size] using hj)] at hr
    simpa only [hxz] using hr.trans (hgroupCode _ hj)
  have hcodeRead (i : ℕ) (hi : i<bank) : μ1 (a+i)=(codes i : ℤ) :=
    (hkeep1 _ (by omega)).trans ((hkeep0 _ (by omega)).trans (hcodes i hi))
  have hpows : Powers μ1 powers W := fun i hi =>
    (hkeep1 _ (by omega)).trans ((hkeep0 _ (by omega)).trans (hpowers i hi))
  have hweightsRead (i : ℕ) (hi : i<hits) : μ1 (weightBase+original i)=weight (original i) :=
    (hkeep1 _ (by have hh:=(hpos i hi).1; omega)).trans
      ((hkeep0 _ (by have hh:=(hpos i hi).1; omega)).trans (hweightRead _ (hpos i hi).1))
  have hhBase := ReportingHostRelocation.meets
    (LightTernaryGroupedSources.meets (P := LightTernaryGroupedSources.program)
      (pMain := 0) (pKeys := 1) (pHist := 3) (pScale := 5) (pSearch := 2) (pFill := 4) (d := d+1) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl) (by rfl)
      μ1 codes position original (fun i => key (position i)) (fun i => group (position i))
      (fun i => weight (original i)) factor hw (by omega) hpairEnd
      (by unfold LightRadixKeys.space at h1Space; omega) (by omega) (by omega)
      (by unfold LightRadixKeys.space at hinitEnd; omega) hgroupRead
      (fun i hi => hgroup _ (hpos i hi).2) hgroupWord hgroupSpace hkeyEnd hvalues hlookupWord
      hfactor hweighted hhistWord hcodeRead (fun i hi => (hpairRead i hi).2)
      (fun i hi => (hpos i hi).2) hwordRead (fun i hi => hkey _ (hpos i hi).2)
      hcodeBound hpows hsorted (fun i hi => (hpairRead i hi).1) (fun i hi => (hpos i hi).1)
      hweightsRead (fun i hi => hweightBound _ (hpos i hi).1) hL hn (by omega))
    (joined xs ys zs)
  have hh := hhBase.append [body]
  have hh' : Meets lim (program xs ys zs) 28 (d+1)
      [a,bank,powers,L,pb,hits,dst1+LightRadixKeys.offset xs.length J+1,NR,keyBase,valueBase,
        weightBase,NL,factor,dst2+LightRadixKeys.offset xs.length J+1,groups] μ1
      (LightTernaryGroupedSources.time L hits bank groups)
      (fun _ ν => (∀ r<groups*bank, ν (valueBase+r)=(factor : ℤ)*
        LightTernaryWeightedHistogram.total (fun i => group (position i)*bank+key (position i))
          (fun i => weight (original i)) r hits) ∧
        ∀ x, (x<keyBase ∨ keyBase+hits≤x) →
          (x<valueBase ∨ valueBase+groups*bank≤x) → ν x=μ1 x) := by
    simpa only [program,libraries,joined,ReportingHostRelocation.program,
      LightTernaryParallelDictionaries.program,LightTernaryParallelDictionaries.libraries,
      LightFixedRadixDictionary.program,LightTernaryOriginalJoin.program,LightWantedSetup.program_length,
      LightTernaryGroupedSources.program,List.length_cons,List.length_nil,List.length_append,
      List.length_map,Nat.reduceAdd,List.append_assoc,Nat.cast_add,Nat.cast_one] using hh
  light_call hh' using NR,hits,LightTernaryGroupedSources.time with out ν ⟨hvaluesFinal,hkeepFinal⟩
  light_set (valueBase : ℕ) using NR,hits,LightTernaryGroupedSources.time
  refine ⟨rfl,?_,ps,hlen,hnodup,?_,hvaluesFinal⟩
  · intro x hx
    change ν x=μ x
    rw [hkeepFinal x (Or.inl (by omega)) (Or.inl (by omega)),hkeep1 x (by omega),hkeep0 x hx]
  · intro i j
    simpa only [Int.add_zero] using hmem i j

end ThreeSum.LightTernarySourceHost
