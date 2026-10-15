import Submission.ThreeSum.TernaryNativeRequesterCoverage
import Submission.ThreeSum.TernaryWantedBatchIndex

noncomputable section
namespace ThreeSum.TernaryNativeCompleteFrontend
open TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps TernaryCanonicalDictionaries
open TernaryExtensionEncoding TernaryNativeRequesterCoverage
open TernaryCanonicalNativeCompleteness LightTernarySourceHost
set_option maxHeartbeats 4000000
variable {p m F r : ℕ} [Fact p.Prime]

def localRecords (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) :=
  records (α := fixedAlpha m) right maps cap

def nativeDictionary (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) (i : ℕ) : ℤ :=
  dictionary ((localRecords maps cap right).map (native right maps)) p r i

def wordDictionary (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) (i : ℕ) : ℤ :=
  dictionary ((localRecords maps cap right).map wordCode) (4^(fixedLength m)) r i

def groupDictionary (maps : Fin F→Weight m p) (cap : ℕ) (right : Bool) (i : ℕ) : ℤ :=
  dictionary ((localRecords maps cap right).map mapCode) F r i

/-- Exact representation facts for the three aligned, literal tuple arrays.
These are equalities of concrete finite dictionaries and lookup results. -/
structure Sources (S : TernarySourceCountExecutionFactory.Setup (r*fixedLength m))
    (maps : Fin F→Weight m p) (cap : ℕ) : Prop where
  leftSize : size S.left.xs S.left.J=(localRecords maps cap false).length^r
  rightSize : size S.right.xs S.right.J=(localRecords maps cap true).length^r
  leftNative : ∀j<(localRecords maps cap false).length^r,
    dictionary S.left.xs S.left.p0 S.left.J j=nativeDictionary (r := r) maps cap false j
  rightNative : ∀j<(localRecords maps cap true).length^r,
    dictionary S.right.xs S.right.p0 S.right.J j=nativeDictionary (r := r) maps cap true j
  leftWord : ∀j<(localRecords maps cap false).length^r,
    (TernaryCodeSemantics.address (S.front.E.word (S.left.key j)) : ℤ)=wordDictionary (r := r) maps cap false j
  rightWord : ∀j<(localRecords maps cap true).length^r,
    (TernaryCodeSemantics.address (S.front.E.word (S.right.key j)) : ℤ)=wordDictionary (r := r) maps cap true j
  leftGroup : ∀j<(localRecords maps cap false).length^r,
    (S.left.group j : ℤ)=groupDictionary (r := r) maps cap false j
  rightGroup : ∀j<(localRecords maps cap true).length^r,
    (S.right.group j : ℤ)=groupDictionary (r := r) maps cap true j

def queries {J : ℕ} (maps : Fin F→Weight m p) (τ U radix : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A : ℕ→ℤ) (nA : ℕ) : List TernaryWantedBatchIndex.Entry :=
  TernaryWantedBatchIndex.entries p (4^(fixedLength m)) F r
    (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
    (TernaryGoodOutputCatalog.mapCodes maps τ) (target H U radix A) (position J) (nA*2^J)

structure Queries {J : ℕ} (S : TernarySourceCountExecutionFactory.Setup (r*fixedLength m))
    (maps : Fin F→Weight m p) (τ U radix : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A : ℕ→ℤ) (nA : ℕ) (pos : ℕ→ℕ) : Prop where
  count : S.front.count=(queries maps τ U radix H A nA).length
  group : ∀i<S.front.count, S.front.group i=(TernaryWantedBatchIndex.get (queries maps τ U radix H A nA) i).2.2
  word : ∀i<S.front.count, TernaryCodeSemantics.address (S.front.Q i)=
    (TernaryWantedBatchIndex.get (queries maps τ U radix H A nA) i).2.1
  position : ∀i<S.front.count, pos i=(TernaryWantedBatchIndex.get (queries maps τ U radix H A nA) i).1

theorem complete {J U radix nA : ℕ}
    (S : TernarySourceCountExecutionFactory.Setup (r*fixedLength m))
    (maps : Fin F→Weight m p) (cap τ : ℕ)
    (hcover : ∀ a b : ZMod p, ∃ i, TernaryCoverFrequency.Covers m p cap τ (maps i) (a,b))
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (pos : ℕ→ℕ)
    (hsources : Sources S maps cap) (hqueries : Queries S maps τ U radix H A nA pos)
    (hleft : ∀j<S.left.NL, S.left.input j=(coefficientCode (sourceLeft H U radix (B j)) : ℤ))
    (hright : ∀j<S.right.NL, S.right.input j=(coefficientCode (sourceRight H U radix (C j)) : ℤ))
    (hA : ∀i<nA, |A i|≤(U : ℤ)) (hB : ∀j<S.left.NL, |B j|≤(U : ℤ))
    (hC : ∀k<S.right.NL, |C k|≤(U : ℤ)) (hcap : 4*U<radix^J) :
    (∃ i<S.front.count, ∃ pair : TernaryNativePairMoments.Pair S i,
      TernaryNativePairMoments.mode B C pair=A (pos i)) ↔
      (∃ i<nA, ∃j<S.left.NL, ∃k<S.right.NL, C k=A i+B j) := by
  classical
  have hpos : ∀i<S.front.count, pos i<nA := by
    intro i hi
    have hm := TernaryWantedBatchIndex.get_mem (xs := queries maps τ U radix H A nA)
      (i := i) (by simpa only [← hqueries.count] using hi)
    have hh := (TernaryWantedBatchIndex.mem_entries _ _ _ _ _ _ _ _ _ _ _).mp hm
    obtain ⟨t,ht,hp,_⟩ := hh
    rw [hqueries.position i hi,hp]
    exact position_lt ht
  constructor
  · exact TernaryNativePairAccess.sound S A B C pos nA hpos
  · rintro ⟨i,hi,j,hj,k,hk,hrel⟩
    obtain ⟨t,ht,hpt,htt⟩ := TernaryNativeRequesterCoverage.complete H A (B j) (C k)
      hi (hA i hi) (hB j hj) (hC k hk) hcap hrel
    obtain ⟨occ,e,jL,jR,hjL,hjR,hnL,hnR,hwL,hwR,hgL,hgR,hwant,hadds⟩ :=
      TernaryCanonicalNativeCompleteness.complete maps cap τ hcover
        (sourceLeft H U radix (B j)) (sourceRight H U radix (C k))
    let entry : TernaryWantedBatchIndex.Entry :=
      (i,TernaryCodeSemantics.address (TernaryRepeatedWords.canonical (fun x => TernaryCoverLocal.output (e x))),bankId occ)
    have he : entry∈queries maps τ U radix H A nA := by
      apply (TernaryWantedBatchIndex.mem_entries _ _ _ _ _ _ _ _ _ _ _).mpr
      refine ⟨t,ht,hpt.symm,?_⟩
      simpa only [htt] using hwant
    obtain ⟨q,hq⟩ := List.mem_iff_get.mp he
    have hqi : q.val<S.front.count := by simpa only [hqueries.count] using q.isLt
    have hget : TernaryWantedBatchIndex.get (queries maps τ U radix H A nA) q.val=entry := by
      unfold TernaryWantedBatchIndex.get
      rw [List.getD_eq_getElem _ _ q.isLt]
      simpa only [List.get_eq_getElem] using hq
    have hQ : S.front.Q q.val=TernaryRepeatedWords.canonical (fun x => TernaryCoverLocal.output (e x)) := by
      apply TernaryCodeSemantics.address_injective
      rw [hqueries.word q.val hqi,hget]
    have hgroup : S.front.group q.val=bankId occ := by rw [hqueries.group q.val hqi,hget]
    obtain ⟨pair,hpairL,hpairR⟩ := TernaryNativePairAccess.exists_pair S q.val j k jL jR
      (TernaryRepeatedWords.canonical (fun x => TernaryCoverLocal.left (e x)))
      (TernaryRepeatedWords.canonical (fun x => TernaryCoverLocal.right (e x))) hj hk
      (by rw [hsources.leftSize]; exact hjL) (by rw [hsources.rightSize]; exact hjR)
      (by rw [hleft j hj,hsources.leftNative jL hjL]; exact hnL.symm)
      (by rw [hright k hk,hsources.rightNative jR hjR]; exact hnR.symm)
      (by apply Int.ofNat_inj.mp; rw [hsources.leftGroup jL hjL,hgroup]; exact hgL)
      (by apply Int.ofNat_inj.mp; rw [hsources.rightGroup jR hjR,hgroup]; exact hgR)
      (by apply Int.ofNat_inj.mp; exact (hsources.leftWord jL hjL).trans hwL)
      (by apply Int.ofNat_inj.mp; exact (hsources.rightWord jR hjR).trans hwR)
      (by rw [hQ]; exact hadds)
    refine ⟨q.val,hqi,pair,?_⟩
    unfold TernaryNativePairMoments.mode
    rw [hpairL,hpairR,hqueries.position q.val hqi,hget]
    dsimp only [entry]
    omega

end ThreeSum.TernaryNativeCompleteFrontend
