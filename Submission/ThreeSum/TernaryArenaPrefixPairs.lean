import Submission.ThreeSum.TernaryArenaPrefixGroups
import Submission.ThreeSum.TernaryNativePairAccess

noncomputable section
namespace ThreeSum.TernaryArenaPrefixPairs
open Finset TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCoverLocal
open TernaryArenaSourceSetup TernaryExtensionEncoding TernaryCanonicalDictionaries
open TernaryNativePrefixLineage TernaryArenaPrefixGroups TernaryArenaPairModel
open TernaryFixedDictionaries
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 5000000
variable {p m F Λ r : ℕ} [Fact p.Prime]
variable (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) (L R : ℕ→Fin Λ→ℤ)
    (row : ℕ→(Fin Λ→ZMod p)→ₗ[ZMod p] ZMod p) (root : ℕ→ℕ→ZMod p)
    (Q : TernaryGoodOutputCatalog.Output m)

abbrev S := setup (r := r) maps τ cap Q (input I L R row root r)

variable {maps τ cap I L R row root Q}

def pair (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count)
    (x : TernaryNativePairMoments.Pair (S (r := r) maps τ cap I L R row root Q) j.val) :
    (M maps τ cap I L R row root).Pair (group maps τ cap I L R row root r j) :=
  ⟨((⟨x.val.1.1,TernaryCompactPairedSupport.native_left_lt x⟩,
      ⟨x.val.2.1,TernaryCompactPairedSupport.native_right_lt x⟩),edge j.isLt x),by
    intro t
    refine ⟨rfl,?_,?_,?_,?_⟩
    · obtain ⟨i,hi,h⟩ := TernaryArenaSourceModel.original_rows maps cap (input I L R row root r)
        false (fun b t => row t.val (fun a => (L b a : ZMod p))) (by intros; rfl) _ (left_mem x)
      have he : i=leftIndex x := Fin.ext hi
      rw [he] at h
      exact (congrFun h t).trans (left_hash j.isLt x t)
    · obtain ⟨i,hi,h⟩ := TernaryArenaSourceModel.original_rows maps cap (input I L R row root r)
        true (fun c t => row t.val (fun a => (R c a : ZMod p))) (by intros; rfl) _ (right_mem x)
      have he : i=rightIndex x := Fin.ext hi
      rw [he] at h
      exact (congrFun h t).trans (right_hash j.isLt x t)
    · have hm := TernaryCanonicalSourceBank.block_mem false maps cap (leftIndex x) t
      have hk : keepLeft maps cap (TernaryCanonicalSourceBank.block false maps cap (leftIndex x) t).1
          (TernaryCanonicalSourceBank.block false maps cap (leftIndex x) t).2.val := by
        simpa [records,trimmedLeftRecords,acceptedLeft,keepLeft,leftNative] using hm
      have ho := congrFun (left_occurrence j.isLt x) t
      rw [ho] at hk
      exact hk
    · have hm := TernaryCanonicalSourceBank.block_mem true maps cap (rightIndex x) t
      have hk : keepRight maps cap (TernaryCanonicalSourceBank.block true maps cap (rightIndex x) t).1
          (TernaryCanonicalSourceBank.block true maps cap (rightIndex x) t).2.val := by
        simpa [records,trimmedRightRecords,acceptedRight,keepRight,rightNative] using hm
      have ho := congrFun (right_occurrence j.isLt x) t
      rw [ho] at hk
      exact hk⟩

theorem pair_injective (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count) :
    Function.Injective (pair (maps := maps) (τ := τ) (cap := cap) (I := I) (L := L) (R := R)
      (row := row) (root := root) (Q := Q) j) := by
  intro x y he
  apply pair_encoding_injective j.isLt
  have hh := congrArg Subtype.val he
  apply Prod.ext
  · exact Prod.ext (congrArg (fun z => z.1.1.val) hh) (congrArg (fun z => z.1.2.val) hh)
  · exact congrArg (fun z : (Fin I.nB×Fin I.nC)×(Fin r→ActualEdge m) => z.2) hh


theorem pair_surjective (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count) :
    Function.Surjective (pair (maps := maps) (τ := τ) (cap := cap) (I := I) (L := L) (R := R)
      (row := row) (root := root) (Q := Q) j) := by
  intro y
  let out := (group maps τ cap I L R row root r j).val.2
  let ls : Fin r→SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) :=
    fun t => ((out t).1,⟨left (y.val.2 t),left_mem_vertices _⟩)
  let rs : Fin r→SourceRecord (fixedLength m) (fixedAlpha m) (Fin F) :=
    fun t => ((out t).1,⟨right (y.val.2 t),right_mem_vertices _⟩)
  have hls (t : Fin r) : ls t∈records (α := fixedAlpha m) false maps cap := by
    have hh := (y.property t).2.2.2.1
    change TernaryArenaPrefixGroups.keepLeft maps cap (out t).1 (left (y.val.2 t)) at hh
    simpa [records,trimmedLeftRecords,acceptedLeft,TernaryArenaPrefixGroups.keepLeft,leftNative,ls] using hh
  have hrs (t : Fin r) : rs t∈records (α := fixedAlpha m) true maps cap := by
    have hh := (y.property t).2.2.2.2
    change TernaryArenaPrefixGroups.keepRight maps cap (out t).1 (right (y.val.2 t)) at hh
    simpa [records,trimmedRightRecords,acceptedRight,TernaryArenaPrefixGroups.keepRight,rightNative,rs] using hh
  let il := TernaryCanonicalSourceBank.encodeBlock false maps cap ls hls
  let ir := TernaryCanonicalSourceBank.encodeBlock true maps cap rs hrs
  have hbl : TernaryCanonicalSourceBank.block false maps cap il=ls :=
    TernaryCanonicalSourceBank.block_encodeBlock false maps cap ls hls
  have hbr : TernaryCanonicalSourceBank.block true maps cap ir=rs :=
    TernaryCanonicalSourceBank.block_encodeBlock true maps cap rs hrs
  let I' := input I L R row root r
  let host := S (r := r) maps τ cap I L R row root Q
  have hlkey : host.left.input y.val.1.1.val=
      LightTernarySourceHost.dictionary host.left.xs p r il.val := by
    change (coefficientCode (fun t : Fin r => row t.val (fun a => (L y.val.1.1.val a : ZMod p))) : ℤ)=
      LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) false maps cap).map (native false maps)) p r il.val
    rw [TernaryCanonicalSourceBank.dictionary_native false maps cap il]
    congr 1
    congr 1
    funext t
    change row t.val (fun a => (L y.val.1.1.val a : ZMod p))=leftNative maps
      (TernaryCanonicalSourceBank.block false maps cap il t)
    rw [hbl]
    exact (y.property t).2.1
  have hrkey : host.right.input y.val.1.2.val=
      LightTernarySourceHost.dictionary host.right.xs p r ir.val := by
    change (coefficientCode (fun t : Fin r => row t.val (fun a => (R y.val.1.2.val a : ZMod p))) : ℤ)=
      LightTernarySourceHost.dictionary ((records (α := fixedAlpha m) true maps cap).map (native true maps)) p r ir.val
    rw [TernaryCanonicalSourceBank.dictionary_native true maps cap ir]
    congr 1
    congr 1
    funext t
    change row t.val (fun a => (R y.val.1.2.val a : ZMod p))=rightNative maps
      (TernaryCanonicalSourceBank.block true maps cap ir t)
    rw [hbr]
    exact (y.property t).2.2.1
  have hgl : host.left.group il.val=host.front.group j.val := by
    change (source (r := r) maps cap I' false).group il.val=
      (TernaryWantedBatchIndex.get (entries (r := r) maps τ I') j.val).2.2
    rw [TernaryArenaSourceModel.group_spec maps cap I' false il,hbl]
    exact (TernaryArenaQueryModel.group_code maps τ I'.targets I'.positions I'.requesterCount j).symm
  have hgr : host.right.group ir.val=host.front.group j.val := by
    change (source (r := r) maps cap I' true).group ir.val=
      (TernaryWantedBatchIndex.get (entries (r := r) maps τ I') j.val).2.2
    rw [TernaryArenaSourceModel.group_spec maps cap I' true ir,hbr]
    exact (TernaryArenaQueryModel.group_code maps τ I'.targets I'.positions I'.requesterCount j).symm
  have hlword : host.front.E.word (host.left.key il.val)=TernaryRepeatedWords.canonical (fun t => left (y.val.2 t)) := by
    change (TernaryBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I' false).key il.val)=_
    rw [TernaryArenaSourceModel.word_spec maps cap I' false il]
    change TernaryRepeatedWords.canonical (fun t => (TernaryCanonicalSourceBank.block false maps cap il t).2.val)=_
    rw [hbl]
  have hrword : host.front.E.word (host.right.key ir.val)=TernaryRepeatedWords.canonical (fun t => right (y.val.2 t)) := by
    change (TernaryBankCanonical.enumeration (N m r) (cut m r)).word
      ((source (r := r) maps cap I' true).key ir.val)=_
    rw [TernaryArenaSourceModel.word_spec maps cap I' true ir]
    change TernaryRepeatedWords.canonical (fun t => (TernaryCanonicalSourceBank.block true maps cap ir t).2.val)=_
    rw [hbr]
  have hq : host.front.Q j.val=TernaryRepeatedWords.canonical (fun t => output (y.val.2 t)) := by
    rw [TernaryArenaQueryModel.setup_Q j.isLt]
    change TernaryRepeatedWords.canonical (fun t => (out t).2.val)=_
    apply congrArg TernaryRepeatedWords.canonical
    funext t
    exact (y.property t).1.symm
  have hp : ((y.val.1.1.val,il.val),(y.val.1.2.val,ir.val))∈TernaryNativePairMoments.pairs host j.val := by
    apply (TernaryNativePairAccess.mem_pair _ _ _ _ _ _).mpr
    refine ⟨?_,hgl,?_,hgr,?_⟩
    · apply (TernarySourceHostModel.mem_records _ _ _ _ _ _).mpr
      refine ⟨y.val.1.1.isLt,?_,?_⟩
      · change il.val<((records (α := fixedAlpha m) false maps cap).map (native false maps)).length^r
        simpa only [List.length_map] using il.isLt
      · rw [hlkey]
        change ((p^r : ℕ) : ℤ)∣LightTernarySourceHost.dictionary host.left.xs p r il.val-
          LightTernarySourceHost.dictionary host.left.xs p r il.val
        rw [sub_self]; exact dvd_zero _
    · apply (TernarySourceHostModel.mem_records _ _ _ _ _ _).mpr
      refine ⟨y.val.1.2.isLt,?_,?_⟩
      · change ir.val<((records (α := fixedAlpha m) true maps cap).map (native true maps)).length^r
        simpa only [List.length_map] using ir.isLt
      · rw [hrkey]
        change ((p^r : ℕ) : ℤ)∣LightTernarySourceHost.dictionary host.right.xs p r ir.val-
          LightTernarySourceHost.dictionary host.right.xs p r ir.val
        rw [sub_self]; exact dvd_zero _
    · rw [hlword,hrword,hq]
      exact TernaryRepeatedWords.canonical_adds _ _ _ (fun t => (edge_data (y.val.2 t)).2.2.2)
  let x : TernaryNativePairMoments.Pair host j.val := ⟨_,hp⟩
  refine ⟨x,?_⟩
  apply Subtype.ext
  apply Prod.ext
  · apply Prod.ext <;> apply Fin.ext <;> rfl
  funext t
  apply endpoint_injective (fixedAlpha m) (fixedPi m)
  have hixl : leftIndex x=il := rfl
  have hixr : rightIndex x=ir := rfl
  apply Prod.ext
  · change (TernaryCanonicalSourceBank.block false maps cap (leftIndex x) t).2.val=left (y.val.2 t)
    rw [hixl,hbl]
  · change (TernaryCanonicalSourceBank.block true maps cap (rightIndex x) t).2.val=right (y.val.2 t)
    rw [hixr,hbr]

def pairEquiv (j : Fin (S (r := r) maps τ cap I L R row root Q).front.count) :=
  Equiv.ofBijective (pair (maps := maps) (τ := τ) (cap := cap) (I := I) (L := L) (R := R)
      (row := row) (root := root) (Q := Q) j)
    ⟨pair_injective j,pair_surjective j⟩

end ThreeSum.TernaryArenaPrefixPairs
