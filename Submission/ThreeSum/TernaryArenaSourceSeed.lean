import Submission.ThreeSum.TernaryArenaSourceCertificate
import Submission.ThreeSum.TernarySourceWeightSeed
import Submission.ThreeSum.TernaryArenaSourceLayout
import Submission.ThreeSum.TernaryArenaSourceControls

noncomputable section
namespace ThreeSum.TernaryArenaSourceSeed
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryCanonicalDictionaries LightTernarySourceHost
open TernaryNativeCompleteFrontend
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 3000000

/-- Exact canonical dictionary and bank semantics of the physically allocated
source. These facts have no execution or resource assumptions. -/
structure Canonical (S : TernarySourceExecutionFactory.Setup)
    (E : ℕ→TritWord (N m r)) : Prop where
  xy : S.ys.length=S.xs.length
  xz : S.zs.length=S.xs.length
  native : ∀ x∈S.xs, |x|≤(S.U0 : ℤ)
  words : ∀ x∈S.ys, |x|≤(S.U1 : ℤ)
  maps : ∀ x∈S.zs, |x|≤(S.U2 : ℤ)
  codeBound : ∀i<S.bank, S.codes i<2^S.W
  sorted : ∀i k, i<k→k<S.bank→S.codes i<S.codes k
  wordCode : ∀j<size S.xs S.J, dictionary S.ys S.p1 S.J j=(S.codes (S.key j) : ℤ)
  key : ∀j<size S.xs S.J, S.key j<S.bank
  groupCode : ∀j<size S.xs S.J, dictionary S.zs S.p2 S.J j=(S.group j : ℤ)
  group : ∀j<size S.xs S.J, S.group j<S.groups
  injective : ∀i j, i<S.bank→j<S.bank→E i=E j→i=j
  factorial : ∀x∈S.records, (S.factor : ℤ)=TernaryConvolution.factorial (E (S.key x.2))

private theorem four_pow (n : ℕ) : 4^n=2^(2*n) := by
  rw [Nat.pow_mul]

/-- Both source colors use the same literal bank addresses and occurrence
identifiers as the canonical tuple dictionaries. -/
theorem canonical (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) (hF : 1<F) :
    Canonical (source (r := r) maps cap I right)
      (TernaryBankCanonical.enumeration (N m r) (cut m r)).word := by
  let S := source (r := r) maps cap I right
  have hsize (j : ℕ) (hj : j<size S.xs S.J) :
      j<(TernaryCanonicalDictionaries.records (α := fixedAlpha m) right maps cap).length^r := by
    simpa [S,source,size,localRecords] using hj
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simp [source]
  · simp [source]
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact native_bound right maps v
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact wordCode_bound v
  · intro x hx
    obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    simpa only [source,Fintype.card_fin] using mapCode_bound v
  · intro i hi
    change (bankCodes m r).getD i 0<2^(2*N m r)
    rw [←four_pow]
    apply TernaryAddresses.mem_codes_lt
    have hii : i<(bankCodes m r).length := hi
    rw [List.getD_eq_getElem _ _ hii]
    exact List.getElem_mem hii
  · intro i k hik hk
    change (bankCodes m r).getD i 0<(bankCodes m r).getD k 0
    have hkk : k<(bankCodes m r).length := hk
    rw [List.getD_eq_getElem _ _ (by omega),List.getD_eq_getElem _ _ hkk]
    exact List.pairwise_iff_getElem.mp (TernaryAddresses.codes_strictly_sorted _ _) i k (show i<(bankCodes m r).length by omega) hkk hik
  · intro j hj
    exact TernaryArenaSourceModel.word_code maps cap I right ⟨j,hsize j hj⟩
  · intro j hj
    exact TernaryArenaSourceModel.key_lt maps cap I right ⟨j,hsize j hj⟩
  · intro j hj
    have hg := TernaryCanonicalSourceBank.dictionary_group right maps cap ⟨j,hsize j hj⟩
    change dictionary ((localRecords maps cap right).map mapCode) F r j=
      ((dictionary ((localRecords maps cap right).map mapCode) F r j).toNat : ℤ)
    change dictionary ((TernaryCanonicalDictionaries.records (α := fixedAlpha m) right maps cap).map mapCode) F r j=
      ((dictionary ((TernaryCanonicalDictionaries.records (α := fixedAlpha m) right maps cap).map mapCode) F r j).toNat : ℤ)
    rw [hg,Int.toNat_natCast]
  · intro j hj
    have occBound (occ : Fin r→Fin F) : TernaryNativeBlockPairs.occurrenceCode occ<F^r := by
      have hh := Nat.ofDigits_lt_base_pow_length hF (l := List.ofFn fun i : Fin r =>
        (Fintype.equivFin (Fin F) (occ i)).val) (by
          intro x hx
          obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
          simpa only [Fintype.card_fin] using (Fintype.equivFin (Fin F) (occ i)).isLt)
      simpa only [List.length_ofFn,TernaryNativeBlockPairs.occurrenceCode] using hh
    rw [TernaryArenaSourceModel.group_spec maps cap I right ⟨j,hsize j hj⟩]
    exact occBound _
  · intro i j hi hj he
    have hsorted := TernaryBankCanonical.sorted (N m r) (cut m r)
    rcases lt_trichotomy i j with h|rfl|h
    · have := hsorted i j h hj
      rw [he] at this
      omega
    · rfl
    · have := hsorted j i h hi
      rw [he] at this
      omega
  · intro x hx
    exact TernaryArenaSourceCertificate.source_factorial maps cap I right x.2
      ((TernarySourceHostModel.mem_records _ _ _ _ _ _).mp hx).2.1

/-- Physical reads and pointer separation for a source call. All data are
read from the original key array and the actually enumerated prefix bank. -/
structure Memory (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool)
    (lim : Limits) (μ : ℕ→ℤ) (weight : ℕ→ℤ) : Prop where
  nonempty : 0<(localRecords maps cap right).length
  sourceBefore : (source (r := r) maps cap I right).src+(source (r := r) maps cap I right).NL≤
    (source (r := r) maps cap I right).base0
  weightsBefore : (source (r := r) maps cap I right).weightBase+(source (r := r) maps cap I right).NL≤
    (source (r := r) maps cap I right).base0
  bankBefore : I.prefixFree+nb m r≤(source (r := r) maps cap I right).base0
  powersBefore : I.prefixFree+4^(N m r)+(2*N m r+1)≤(source (r := r) maps cap I right).base0
  groupSpace : F^r*nb m r+1≤lim.space
  bankSize : nb m r<2^(2*N m r)
  input : ∀i<(source (r := r) maps cap I right).NL,
    μ ((source (r := r) maps cap I right).src+i)=(source (r := r) maps cap I right).input i
  inputBound : ∀i<(source (r := r) maps cap I right).NL,
    |(source (r := r) maps cap I right).input i|≤(p*(p+1)^r : ℕ)
  weights : ∀i<(source (r := r) maps cap I right).NL, |weight i|≤(I.weightCap : ℤ)
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)

/-- The literal canonical source has all its pure preconditions. No source
execution receipt or mathematical source-value oracle is an input. -/
theorem seed {lim : Limits} {d : ℕ} {μ : ℕ→ℤ} {weight : ℕ→ℤ}
    (maps : Fin F→Weight m p) (cap : ℕ) (I : Input) (right : Bool) (hF : 1<F)
    (hw : (lim.space : ℤ)≤lim.word)
    (G : TernaryArenaSourceLayout.Geometry (source (r := r) maps cap I right) lim.space)
    (W : TernaryArenaSourceControls.Controls (r := r) maps cap I right lim d)
    (M : Memory (r := r) maps cap I right lim μ weight) :
    TernarySourceExecutionFactory.Seed (source (r := r) maps cap I right) lim d μ weight
      (TernaryBankCanonical.enumeration (N m r) (cut m r)).word := by
  have C := canonical (r := r) maps cap I right hF
  refine {
    hxy:=C.xy
    hxz:=C.xz
    hw:=hw
    hm:=by simpa only [source,List.length_map] using M.nonempty
    hbase0:=G.base0
    hnext0:=G.next0
    hbase1:=G.base1
    hnext1:=G.next1
    hbase2:=G.base2
    hinitEnd:=G.initEnd
    hkeyBase:=G.keyBase
    hkeyEnd:=G.keyEnd
    hvalues:=G.values
    hsrc:=M.sourceBefore
    hweights:=M.weightsBefore
    hbank:=M.bankBefore
    hpowerEnd:=M.powersBefore
    hb0:=C.native
    hb1:=C.words
    hb2:=C.maps
    hw0:=W.hword0
    hw1:=W.hword1
    hw2:=W.hword2
    hM:=by
      dsimp [source]
      exact pow_pos (Fact.out : p.Prime).pos r
    hjoinWord:=W.join
    hlookupWord:=W.lookup
    hgroupWord:=W.group
    hgroupSpace:=M.groupSpace
    hfactor:=W.factor
    hweighted:=W.weighted
    hhistWord:=W.hist
    hinput:=M.input
    hinputBound:=M.inputBound
    hweightBound:=M.weights
    hglobal:=le_rfl
    hpowers:=M.powers
    hcodes:=?_
    hcodeBound:=C.codeBound
    hsorted:=C.sorted
    hwordCode:=C.wordCode
    hkey:=C.key
    hgroupCode:=C.groupCode
    hgroup:=C.group
    hL:=le_rfl
    hn:=M.bankSize
    hd:=W.callDepth
    hinjective:=C.injective
    hfactorModel:=C.factorial }
  intro i hi
  have hi' : i<(bankCodes m r).length := hi
  have hs := M.codes i (by simpa [List.bind_eq_flatMap,←List.map_eq_flatMap] using hi')
  change μ (I.prefixFree+i)=((bankCodes m r).getD i 0 : ℤ)
  rw [List.getD_eq_getElem _ _ hi']
  simpa [List.bind_eq_flatMap,←List.map_eq_flatMap] using hs

end ThreeSum.TernaryArenaSourceSeed
