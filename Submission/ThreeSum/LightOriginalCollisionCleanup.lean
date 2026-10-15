import Submission.ThreeSum.LightDeletedTwoSum
import Submission.ThreeSum.TernaryOriginalCollisions

/-! Actual original-bucket filtering and exact deletion cleanup, with collision-score cost. -/
noncomputable section
namespace ThreeSum.LightOriginalCollisionCleanup
open Light ThreeSum.LightSubsetAddress
open ThreeSum.LightOriginalBucketFilter
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
set_option maxRecDepth 12000

def counts (keys : ℕ → ℕ) (n r : ℕ) : ℕ := LightHistogram.count keys r n

def badIndices (keys : ℕ → ℕ) (n : ℕ) : List ℕ := bad keys (counts keys n) n

def badIndex (keys : ℕ → ℕ) (n j : ℕ) : ℕ :=
  if hj : j<(badIndices keys n).length then (badIndices keys n)[j] else 0

theorem badIndex_lt {keys : ℕ → ℕ} {n j : ℕ} (hj : j<(badIndices keys n).length) : badIndex keys n j<n := by
  have hm := List.getElem_mem hj
  have hh := List.mem_filter.mp hm
  have hr := List.mem_range.mp hh.1
  simpa only [badIndex,dif_pos hj] using hr

theorem count_self_positive {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) : 0<counts keys n (keys i) := by
  change 0<((Finset.range n).filter (fun j => keys j=keys i)).card
  apply Finset.card_pos.mpr
  exact ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,rfl⟩⟩

theorem count_self_ne_one_iff {keys : ℕ → ℕ} {n i : ℕ} (hi : i<n) :
    counts keys n (keys i)≠1 ↔ ∃ j<n, j≠i ∧ keys j=keys i := by
  have hm : i∈(Finset.range n).filter (fun j => keys j=keys i) :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,rfl⟩
  change ((Finset.range n).filter (fun j => keys j=keys i)).card≠1 ↔ _
  constructor
  · intro h
    by_contra hn
    have he : (Finset.range n).filter (fun j => keys j=keys i)={i} := by
      ext j
      constructor
      · intro hj
        obtain ⟨hjn,he⟩ := Finset.mem_filter.mp hj
        have hji : j=i := by
          by_contra hne
          exact hn ⟨j,Finset.mem_range.mp hjn,hne,he⟩
        simp [hji]
      · intro hj
        simpa only [Finset.mem_singleton.mp hj] using hm
    exact h (by rw [he]; simp)
  · rintro ⟨j,hj,hne,he⟩ hcard
    obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hcard
    have hiK : i=k := Finset.mem_singleton.mp (hk ▸ hm)
    have hjM : j∈(Finset.range n).filter (fun j => keys j=keys i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,he⟩
    have hjK : j=k := Finset.mem_singleton.mp (hk ▸ hjM)
    exact hne (hjK.trans hiK.symm)

/-- The physically emitted bad-index list is charged by the literal original
ordered collision score, with no maximum-bucket assumption. -/
theorem bad_length_le_collisions (keys : ℕ → ℕ) (n : ℕ) :
    (badIndices keys n).length≤
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card := by
  let xs := badIndices keys n
  have hnodup : xs.Nodup := (List.nodup_range (n := n)).filter _
  have hxn : ∀ i∈xs, i<n := by
    intro i hi
    exact List.mem_range.mp (List.mem_filter.mp hi).1
  have hxdel : ∀ i (hi : i∈xs), (⟨i,hxn i hi⟩ : Fin n)∈
      TernaryOriginalCollisions.deleted (fun i : Fin n => keys i.val) := by
    intro i hi
    have hb : counts keys n (keys i)≠1 := by simpa using (List.mem_filter.mp hi).2
    obtain ⟨j,hj,hne,he⟩ := (count_self_ne_one_iff (hxn i hi)).mp hb
    simp only [TernaryOriginalCollisions.deleted,Finset.mem_filter,Finset.mem_univ,true_and]
    refine ⟨⟨j,hj⟩,?_,he.symm⟩
    intro hh
    exact hne (congrArg Fin.val hh).symm
  let f : (xs.toFinset) → (TernaryOriginalCollisions.deleted (fun i : Fin n => keys i.val)) :=
    fun a => ⟨⟨a.val,hxn a.val (List.mem_toFinset.mp a.property)⟩,
      hxdel a.val (List.mem_toFinset.mp a.property)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    exact congrArg (fun c => c.val.val) hab
  have hc := Fintype.card_le_of_injective f hinj
  have hlen : xs.toFinset.card=xs.length := List.toFinset_card_of_nodup hnodup
  have hb : xs.length≤(TernaryOriginalCollisions.deleted (fun i : Fin n => keys i.val)).card := by
    simpa only [Fintype.card_coe,hlen] using hc
  exact hb.trans (TernaryOriginalCollisions.deleted_card_le_collisions _)

def body (pFilter pCleanup : ℕ) : Stmt :=
  .call pFilter [v 0,v 1,v 2,v 3,v 4] 13 ;;
  .call pCleanup [v 4 +' v 1,v 13,v 5,v 1,v 6,v 7,v 8,v 9,v 10,v 11,v 12] 0

def time (keys : ℕ → ℕ) (n scanN L : ℕ) : ℕ := LightOriginalBucketFilter.time n+
  LightDeletedTwoSum.time (badIndices keys n).length scanN L+200

variable {lim : Limits} {P : Program}

theorem meets {pMain pFilter pCleanup pTwoSum pLookup pSearch keyBase n hist q out valuesBase scanBase scanN
    targetBase targetN powers W L U d : ℕ} (sign : ℤ)
    (hmain : P[pMain]?=some (body pFilter pCleanup))
    (hfilter : P[pFilter]?=some LightOriginalBucketFilter.body)
    (hcleanup : P[pCleanup]?=some (LightDeletedTwoSum.body pTwoSum))
    (htwo : P[pTwoSum]?=some (LightColoredTwoSum.body pLookup))
    (hlookup : P[pLookup]?=some (LightBandLookup.body pSearch))
    (hsearch : P[pSearch]?=some (LightBandLookup.searchBody pSearch))
    (μ : ℕ → ℤ) (keys : ℕ → ℕ) (values scan target : ℕ → ℤ)
    (hw : (lim.space : ℤ)≤lim.word)
    (hkeysSpace : keyBase+n≤out) (hhistSpace : hist+q≤out) (hout : out+2*n≤lim.space)
    (hvaluesSpace : valuesBase+n≤out) (hscanSpace : scanBase+scanN≤out) (htargetSpace : targetBase+targetN≤out)
    (hspace : powers+(W+1)≤out)
    (hword : ((targetN+2^(W+1)+16 : ℕ) : ℤ)≤lim.word)
    (hkeys : ∀ i<n, keys i<q) (hreadKeys : ∀ i<n, μ (keyBase+i)=(keys i : ℤ))
    (hcounts : ∀ k<q, μ (hist+k)=(counts keys n k : ℤ))
    (hvalues : ∀ i<n, |values i|≤U) (hreadValues : ∀ i<n, μ (valuesBase+i)=values i)
    (hscan : ∀ i<scanN, |scan i|≤U) (hreadScan : ∀ i<scanN, μ (scanBase+i)=scan i)
    (hreadTarget : ∀ i<targetN, μ (targetBase+i)=target i)
    (hsign : |sign|≤1) (hvalueWord : 2*(U : ℤ)+3≤lim.word)
    (hpowers : Powers μ powers W)
    (hsorted : ∀ i j, i<j → j<targetN → target i<target j)
    (hL : L≤W) (htargetN : targetN<2^L) (hd : d+L+4≤lim.depth) :
    Meets lim P pMain d [keyBase,n,hist,q,out,valuesBase,scanBase,scanN,targetBase,targetN,powers,L,sign] μ
      (time keys n scanN L)
      (fun r ν => r=(LightDeletedTwoSum.flag (badIndex keys n) values scan target targetN scanN
          (badIndices keys n).length sign : ℤ) ∧
        Seg ν out (cells (good keys (counts keys n) n)) ∧ Seg ν (out+n) (cells (badIndices keys n)) ∧
        SameOutside μ ν out (2*n)) := by
  have hnword : (n : ℤ)≤lim.word := by omega
  have hcword : ∀ k<q, (counts keys n k : ℤ)≤lim.word := by
    intro k hk
    exact (Int.ofNat_le.mpr (LightHistogram.count_le keys k n)).trans hnword
  have hf := LightOriginalBucketFilter.meets (d := d+1) hfilter μ keys (counts keys n) hw
    hkeysSpace hhistSpace hout hkeys hreadKeys hcounts hcword (by omega)
  apply Meets.of_body hmain
  unfold body time
  light_call hf using LightOriginalBucketFilter.time,LightDeletedTwoSum.time
    with badN ν ⟨hBadN,hGood,hBad,H⟩
  change badN=((badIndices keys n).length : ℤ) at hBadN
  have hKeep {x : ℕ} (hx : x<out) : ν x=μ x := H x (Or.inl hx)
  have hIdRead : ∀ i<(badIndices keys n).length, ν (out+n+i)=(badIndex keys n i : ℤ) := by
    intro i hi
    have hh := hBad i (by simpa [cells,badIndices] using hi)
    rw [badIndex,dif_pos hi]
    simpa [cells,List.bind_eq_flatMap,List.pure_def,←List.map_eq_flatMap,List.getElem_map,badIndices] using hh
  have hPowers : Powers ν powers W := by
    intro i hi; rw [hKeep (by omega),hpowers i hi]
  have hBadLen : (badIndices keys n).length≤n := (lengths keys (counts keys n) n).2
  have hc := LightDeletedTwoSum.meets (d := d+1) (badBase := out+n)
    (badN := (badIndices keys n).length) (valuesBase := valuesBase) (originalN := n)
    (scanBase := scanBase) (scanN := scanN) (targetBase := targetBase) (targetN := targetN)
    (powers := powers) (W := W) (L := L) (U := U) sign hcleanup htwo hlookup hsearch ν
    (badIndex keys n) values scan target hw (by omega)
    (by omega) (by omega) (by omega) (by omega) hword (fun i hi => badIndex_lt hi) hIdRead
    hvalues (fun i hi => by rw [hKeep (by omega),hreadValues i hi]) hscan
    (fun i hi => by rw [hKeep (by omega),hreadScan i hi])
    (fun i hi => by rw [hKeep (by omega),hreadTarget i hi]) hsign hvalueWord hPowers hsorted hL htargetN (by omega)
  light_call hc using hBadN,LightOriginalBucketFilter.time,LightDeletedTwoSum.time
    with result ξ ⟨hResult,hMem⟩
  subst ξ
  refine ⟨?_,hGood,hBad,H⟩
  change result=_
  exact hResult

theorem mem_badIndices {keys : ℕ → ℕ} {n i : ℕ} :
    i∈badIndices keys n ↔ i<n ∧ ∃ j<n, j≠i ∧ keys j=keys i := by
  constructor
  · intro hi
    obtain ⟨hin,hcount⟩ := List.mem_filter.mp hi
    have hin' : i<n := List.mem_range.mp hin
    exact ⟨hin',(count_self_ne_one_iff hin').mp (of_decide_eq_true hcount)⟩
  · rintro ⟨hin,hpartner⟩
    exact List.mem_filter.mpr ⟨List.mem_range.mpr hin,by
      simpa using (count_self_ne_one_iff hin).mpr hpartner⟩

theorem surviving_keys_injective {keys : ℕ → ℕ} {n i j : ℕ}
    (hi : i∈good keys (counts keys n) n) (hj : j∈good keys (counts keys n) n)
    (he : keys i=keys j) : i=j := by
  have hin := List.mem_range.mp (List.mem_filter.mp hi).1
  have hjn := List.mem_range.mp (List.mem_filter.mp hj).1
  have hc : counts keys n (keys i)=1 := of_decide_eq_true (List.mem_filter.mp hi).2
  by_contra hne
  exact ((count_self_ne_one_iff hin).mpr ⟨j,hjn,Ne.symm hne,he.symm⟩) hc

/-- The cleanup flag checks precisely the original records in nonsingleton
buckets, with their original values, rather than representations of records. -/
theorem hit_iff {keys : ℕ → ℕ} {n scanN targetN : ℕ}
    (values scan target : ℕ → ℤ) (sign : ℤ) :
    LightDeletedTwoSum.Hit (badIndex keys n) values scan target targetN scanN (badIndices keys n).length sign ↔
      ∃ i<n, (∃ j<n, j≠i ∧ keys j=keys i) ∧ LightColoredTwoSum.Hit scan target targetN scanN (values i) sign := by
  constructor
  · rintro ⟨j,hj,hh⟩
    have hm : badIndex keys n j∈badIndices keys n := by
      simpa only [badIndex,dif_pos hj] using List.getElem_mem hj
    obtain ⟨hin,hpartner⟩ := mem_badIndices.mp hm
    exact ⟨_,hin,hpartner,hh⟩
  · rintro ⟨i,hin,hpartner,hh⟩
    have hm : i∈badIndices keys n := mem_badIndices.mpr ⟨hin,hpartner⟩
    obtain ⟨j,hj,he⟩ := List.mem_iff_getElem.mp hm
    refine ⟨j,hj,?_⟩
    simpa only [badIndex,dif_pos hj,he] using hh

/-- Every original colored solution is either found during literal collision
cleanup or survives in both source classes. This accounts for all inputs. -/
theorem colored_decomposition (A B C : ℕ → ℤ) (keysB keysC : ℕ → ℕ) (nA nB nC : ℕ) :
    (∃ i<nA, ∃ j<nB, ∃ k<nC, C k=A i+B j) ↔
      LightDeletedTwoSum.Hit (badIndex keysB nB) B A C nC nA (badIndices keysB nB).length 1 ∨
      LightDeletedTwoSum.Hit (badIndex keysC nC) C A B nB nA (badIndices keysC nC).length (-1) ∨
      ∃ i<nA, ∃ j∈good keysB (counts keysB nB) nB, ∃ k∈good keysC (counts keysC nC) nC,
        C k=A i+B j := by
  rw [hit_iff,hit_iff]
  constructor
  · rintro ⟨i,hi,j,hj,k,hk,he⟩
    by_cases hb : counts keysB nB (keysB j)=1
    · by_cases hc : counts keysC nC (keysC k)=1
      · apply Or.inr
        apply Or.inr
        refine ⟨i,hi,j,?_,k,?_,he⟩
        · exact List.mem_filter.mpr ⟨List.mem_range.mpr hj,by simpa using hb⟩
        · exact List.mem_filter.mpr ⟨List.mem_range.mpr hk,by simpa using hc⟩
      · apply Or.inr
        apply Or.inl
        refine ⟨k,hk,(count_self_ne_one_iff hk).mp hc,i,hi,j,hj,?_⟩
        omega
    · apply Or.inl
      refine ⟨j,hj,(count_self_ne_one_iff hj).mp hb,i,hi,k,hk,?_⟩
      simpa using he
  · rintro (⟨j,hj,_,i,hi,k,hk,he⟩ | ⟨k,hk,_,i,hi,j,hj,he⟩ | ⟨i,hi,j,hj,k,hk,he⟩)
    · exact ⟨i,hi,j,hj,k,hk,by simpa using he⟩
    · exact ⟨i,hi,j,hj,k,hk,by omega⟩
    · exact ⟨i,hi,j,List.mem_range.mp (List.mem_filter.mp hj).1,
        k,List.mem_range.mp (List.mem_filter.mp hk).1,he⟩

theorem time_bound (keys : ℕ → ℕ) (n scanN L : ℕ) :
    time keys n scanN L≤200*n+400+
      (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card*
        (scanN*(120*L+330)+300) := by
  have hb := bad_length_le_collisions keys n
  have hm := Nat.mul_le_mul_right (scanN*(120*L+330)+300) hb
  unfold time LightOriginalBucketFilter.time LightDeletedTwoSum.time LightColoredTwoSum.time
    LightBandLookup.time LightBandLookup.searchTime
  nlinarith only [hm]

/-- Six actual procedures; the exact binary membership search is included. -/
def program : Program := [body 1 2,LightOriginalBucketFilter.body,LightDeletedTwoSum.body 3,
  LightColoredTwoSum.body 4,LightBandLookup.body 5,LightBandLookup.searchBody 5]

@[simp] theorem program_length : program.length=6 := rfl

def program_meets {lim : Limits} {keyBase n hist q out valuesBase scanBase scanN targetBase targetN powers W L U d : ℕ}
    (sign : ℤ) :=
  meets (lim := lim) (P := program) (pMain := 0) (pFilter := 1) (pCleanup := 2) (pTwoSum := 3)
    (pLookup := 4) (pSearch := 5) (keyBase := keyBase) (n := n) (hist := hist) (q := q) (out := out)
    (valuesBase := valuesBase) (scanBase := scanBase) (scanN := scanN) (targetBase := targetBase)
    (targetN := targetN) (powers := powers) (W := W) (L := L) (U := U) (d := d) sign rfl rfl rfl rfl rfl rfl

end ThreeSum.LightOriginalCollisionCleanup
