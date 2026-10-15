import Submission.ThreeSum.TernaryArenaSourceValues
import Submission.ThreeSum.TernaryArenaQueryModel
import Submission.ThreeSum.TernaryCountFrontendBudget

noncomputable section
namespace ThreeSum.TernaryArenaCountReady
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
open TernaryBank TernaryCodeSemantics LightTernaryNearPair
set_option maxHeartbeats 6000000
set_option maxRecDepth 16000
attribute [local instance] Classical.propDecidable
variable {p m F r : ℕ} [Fact p.Prime]

/-- A proof-only maximum over the fixed homogeneous output type. It is never
passed to the program as a table or used as advice. -/
def queryTime (I : Input) (V : ℕ) : ℕ :=
  ((Finset.univ : Finset (TritWord (N m r))).filter
    (fun Q => HasType Q (fun d => r*fixedPi m d))).sup
    (fun Q => LightTernaryPreparedWanted.time
      (nearConfig (m := m) (r := r) I false V) (nearConfig (m := m) (r := r) I true V) Q)

structure Capacity {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ) (I : Input) : Prop where
  endSpace : finish I.free I.capacity≤lim.space
  prefixBank : I.prefixFree+nb m r≤addr I.free I.capacity 48
  bankValues : F^r*nb m r≤I.capacity
  stages : F^r*((N m r+1)*nb m r)≤I.capacity
  records : 3*(entries (r := r) maps τ I).length≤I.capacity
  metadata : 4*nb m r≤I.capacity
  powers : 2*N m r+1≤I.capacity
  nearRows : 3^(N m r)≤I.capacity
  nearMetadata : 2*N m r*3^(N m r)+N m r≤I.capacity
  division : TernaryFrontendResources.eulerBound (N m r) (valueCap (r := r) maps cap I)+3≤I.capacity
  word : (TernaryFrontendResources.word (N m r) (nb m r) (F^r)
    (entries (r := r) maps τ I).length (3^(N m r)) (valueCap (r := r) maps cap I) : ℤ)≤lim.word
  depth : d+5*N m r+16≤lim.depth
  time : queryTime (m := m) (r := r) I (valueCap (r := r) maps cap I)≤I.queryTime

private theorem four_pow (n : ℕ) : 4^n=2^(2*n) := by rw [Nat.pow_mul]

theorem bank_size (hN : 0<N m r) : nb m r<2^(2*N m r) := by
  unfold nb bankCodes
  rw [TernaryBankEnumeration.codes_length_eq_bank_card,←four_pow]
  exact (TernaryBank.bank_card_le _ _).trans_lt (Nat.pow_lt_pow_left (by decide) (by omega))

theorem bank_pos : 0<nb m r := by
  unfold nb bankCodes
  rw [TernaryBankEnumeration.codes_length_eq_bank_card]
  apply Finset.card_pos.mpr
  refine ⟨fun _ => 0,?_⟩
  simp [TernaryBank.mem_bank,TernaryBank.rank]

theorem rows_le (Q : TritWord (N m r)) :
    LightTernaryPreparedWanted.rows Q (cut m r)≤3^(N m r) := by
  unfold LightTernaryPreparedWanted.rows
  rw [TernaryNearBankEnumeration.codes_length_eq_nearWords_card]
  exact (Finset.card_le_univ _).trans_eq (by simp [TritWord])

private theorem grouped_end {base group groups N nb : ℕ} (hg : group<groups) :
    base+group*((N+1)*nb)+N*nb+nb≤base+groups*((N+1)*nb) := by
  have hh := Nat.mul_le_mul_right ((N+1)*nb) (Nat.succ_le_of_lt hg)
  nlinarith

/-- Builds every actual frontend guard, including its per-query near plan,
from the canonical source/wanted arrays and scalar arena capacities. -/
theorem ready {lim : Limits} {d : ℕ} (maps : Fin F→Weight m p) (τ cap : ℕ)
    (localQ : TernaryGoodOutputCatalog.Output m) (I : Input) (μ : ℕ→ℤ)
    (leftWeight rightWeight : ℕ→ℤ) (hF : 1<F) (hN : 0<N m r)
    (hw : (lim.space : ℤ)≤lim.word)
    (C : Capacity (lim := lim) (d := d) (r := r) maps τ cap I)
    (hcodes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ))))
    (hrecords : Seg μ (addr I.free I.capacity 19) (TernaryWantedBatchIndex.cells (entries (r := r) maps τ I)))
    (hleft : ∀i<I.nB, |leftWeight i|≤(I.weightCap : ℤ))
    (hright : ∀i<I.nC, |rightWeight i|≤(I.weightCap : ℤ)) :
    TernaryCountExecutionFactory.Ready (front (r := r) maps τ cap localQ I) lim d μ
      ((source (r := r) maps cap I false).values (TernaryBankCanonical.enumeration (N m r) (cut m r)).word leftWeight)
      ((source (r := r) maps cap I true).values (TernaryBankCanonical.enumeration (N m r) (cut m r)).word rightWeight) := by
  let n := N m r
  let A := valueCap (r := r) maps cap I
  let S := front (r := r) maps τ cap localQ I
  have hn : nb m r<2^(2*n) := bank_size hN
  have hnC : n≤I.capacity := by
    have := C.powers
    dsimp [n]
    omega
  have hcountC : S.count≤I.capacity := by
    have := C.records
    dsimp [S,front]
    omega
  have h54 : addr I.free I.capacity 54≤lim.space := (before (i := 54) (j := slots) (by decide) (by omega : 0≤I.capacity)).trans C.endSpace
  have hstageF : S.fbase+S.groups*((n+1)*nb m r)≤S.gbase := before (by decide) C.stages
  have hstageG : S.gbase+S.groups*((n+1)*nb m r)≤S.hbase := before (by decide) C.stages
  have hstageH : S.hbase+S.groups*((n+1)*nb m r)≤S.dst := before (by decide) C.stages
  have hDst : S.dst+S.count≤addr I.free I.capacity 54 := before (by decide) hcountC
  obtain ⟨wlookup,wN,wstride,wtail,wforward,wproduct,winverse⟩ :=
    TernaryFrontendResources.bank_controls n (nb m r) (F^r) S.count (3^n) A
  obtain ⟨_,_,_,_,_,_,_,wgroup,wcount⟩ :=
    TernaryFrontendResources.controls n (nb m r) (F^r) S.count (3^n) A
  have w := C.word
  refine {
    hw:=hw
    ha:=C.prefixBank
    hfs:=before (by decide) C.bankValues
    hgs:=before (by decide) C.bankValues
    hmeta:=before (by decide) C.metadata
    hpows:=before (by decide) C.powers
    hfg:=hstageF
    hgh:=hstageG
    hHdst:=hstageH
    hword:=(Int.ofNat_le.mpr wlookup).trans w
    hNword:=?_
    hgroupsWord:=?_
    hcodes:=TernaryBankCanonical.read_of_seg μ hcodes
    hsorted:=TernaryBankCanonical.sorted n (cut m r)
    hF:=fun g hg W => TernaryArenaSourceValues.bound maps cap I false leftWeight g W hleft
    hG:=fun g hg W => TernaryArenaSourceValues.bound maps cap I true rightWeight g W hright
    hforwardWord:=?_
    hproductWord:=(Int.ofNat_le.mpr wproduct).trans w
    hinverseWord:=?_
    hL:=le_rfl
    hn:=hn
    hrecords:=before (by decide) C.records
    hdst:=hDst
    hspace:=h54
    hreadGroup:=?_
    hreadQ:=?_
    hgroup:=?_
    hRank:=?_
    hcountWord:=?_
    hstrideWord:=(Int.ofNat_le.mpr wstride).trans w
    htailWord:=(Int.ofNat_le.mpr wtail).trans w
    hplan:=?_
    htime:=?_
    hd:=by
      have := C.depth
      dsimp [front,nearConfig,TernaryArenaFrontendResources.config]
      omega }
  · exact_mod_cast (Int.ofNat_le.mpr wN).trans w
  · exact_mod_cast (Int.ofNat_le.mpr wgroup).trans w
  · exact_mod_cast (Int.ofNat_le.mpr wforward).trans w
  · exact_mod_cast (Int.ofNat_le.mpr winverse).trans w
  · intro j hj
    exact (TernaryWantedBatchIndex.read_three _ hrecords hj).2.2
  · intro j hj
    have hh := (TernaryWantedBatchIndex.read_three _ hrecords hj).2.1
    rw [←TernaryArenaQueryModel.setup_address (τ := τ) (cap := cap) (localQ := localQ) hj] at hh
    exact hh
  · intro j hj
    exact TernaryArenaQueryModel.setup_group_lt hF hj
  · intro j hj
    change rank ((setup (r := r) maps τ cap localQ I).front.Q j)=rank ((setup (r := r) maps τ cap localQ I).front.Qstar)
    rw [TernaryDimensionBounds.rank_eq_counts,TernaryDimensionBounds.rank_eq_counts]
    rw [TernaryArenaQueryModel.setup_same_type hj 1,TernaryArenaQueryModel.setup_same_type hj 2]
  · exact_mod_cast (Int.ofNat_le.mpr wcount).trans w
  · intro j hj
    have hg := TernaryArenaQueryModel.setup_group_lt (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) hF hj
    change S.group j<F^r at hg
    have hFend := (grouped_end (base := S.fbase) (N := n) (nb := nb m r) hg).trans hstageF
    have hGend := (grouped_end (base := S.gbase) (N := n) (nb := nb m r) hg).trans hstageG
    have hHend := (grouped_end (base := S.hbase) (N := n) (nb := nb m r) hg).trans hstageH
    have ha : alphaRank m=10864922*m := by
      unfold alphaRank fixedAlpha
      change 8908424*m+2*(978249*m)=10864922*m
      ring
    have hs : r*alphaRank m≤cut m r := by
      rw [ha]
      dsimp [cut,LightTernaryPrefixSetup.T]
      nlinarith
    have ht : cut m r≤2*n := by
      simpa [cut,n,N,LightTernaryPrefixSetup.N,fixedLength,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using (LightTernaryPrefixSetup.dimensions m r).2.2
    have hout : cut m r<rank (S.Q j) := by
      change cut m r<rank ((setup (r := r) maps τ cap localQ I).front.Q j)
      rw [TernaryArenaQueryModel.setup_rank (maps := maps) (τ := τ) (cap := cap) (localQ := localQ) hj]
      have hpos : 0<r*m := by
        dsimp [N,fixedLength] at hN
        nlinarith
      rw [ha]
      dsimp [cut,LightTernaryPrefixSetup.T]
      nlinarith
    have hH54 : S.hbase+S.group j*((n+1)*nb m r)+(n+1)*nb m r≤addr I.free I.capacity 54 := by
      simpa only [Nat.add_mul,Nat.one_mul,Nat.add_assoc] using
        (hHend.trans (before (i := 53) (j := 54) (by decide) (by omega : 0≤I.capacity)))
    have hp := TernaryArenaFrontendResources.plan (S.Q j) S.E
      ((source (r := r) maps cap I false).values S.E.word leftWeight (S.group j))
      ((source (r := r) maps cap I true).values S.E.word rightWeight (S.group j))
      (rows_le (S.Q j)) C.nearRows hnC C.powers C.nearMetadata C.division ht hs hs hn
      ((rows_le (S.Q j)).trans_lt (by exact (Nat.pow_lt_pow_left (by decide) (by omega) : 3^n<4^n) |>.trans_eq (four_pow n)))
      bank_pos (C.prefixBank.trans (before (by decide) (by omega : 0≤I.capacity)))
      (hFend.trans (before (by decide) (by omega : 0≤I.capacity)))
      (hGend.trans (before (by decide) (by omega : 0≤I.capacity)))
      hH54
      C.endSpace hw C.word
      (TernaryArenaSourceValues.homogeneous maps cap I false leftWeight (S.group j))
      (TernaryArenaSourceValues.homogeneous maps cap I true rightWeight (S.group j))
      (fun W => TernaryArenaSourceValues.bound maps cap I false leftWeight (S.group j) W hleft)
      (fun W => TernaryArenaSourceValues.bound maps cap I true rightWeight (S.group j) W hright)
      hout (TernaryBankCanonical.sorted n (cut m r))
    exact hp
  · intro j hj
    rw [TernaryCountFrontendBudget.prepared_time_sourceConfig]
    apply le_trans _ C.time
    exact Finset.le_sup (f := fun Q => LightTernaryPreparedWanted.time
      (nearConfig (m := m) (r := r) I false A) (nearConfig (m := m) (r := r) I true A) Q)
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _,TernaryArenaQueryModel.setup_typed hj⟩)

end ThreeSum.TernaryArenaCountReady
