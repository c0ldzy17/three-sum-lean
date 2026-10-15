import Submission.ThreeSum.TernaryArenaSourceBounds
import Submission.ThreeSum.TernaryArenaCountReady

noncomputable section
namespace ThreeSum.TernaryArenaFrontBounds
open TernaryArenaPrefixFootprints TernaryArenaSourceSetup TernaryArenaSourceBounds
open TernaryCoverGoodMaps TernaryLocalParameters
set_option maxHeartbeats 6000000

variable {p m F r : ℕ} [Fact p.Prime]

theorem wanted_count (maps : Fin F→Weight m p) (τ : ℕ) (I : Input)
    (M b n U : ℕ) (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U)) :
    (entries (r := r) maps τ I).length≤
      n*2^(LightTernaryDimensions.J M b n U)*(wantedWidth maps τ)^r := by
  unfold entries
  rw [TernaryWantedBatchIndex.entries_length_eq_count]
  refine (TernaryWantedBatchCount.count_le _ _ _ _ (wantedWidth maps τ) _ _ _ _ I.positions ?_ _).trans
    (Nat.mul_le_mul_right _ hO)
  intro x
  have hh := List.length_filter_le (fun i => (p : ℤ) ∣ x-(TernaryGoodOutputCatalog.raws maps τ).getD i 0)
    (List.range (TernaryGoodOutputCatalog.raws maps τ).length)
  exact hh.trans (by simp only [List.length_range]; unfold wantedWidth; omega)

theorem word_mono {N nb nb' G count count' R R' V V' : ℕ}
    (hb : nb≤nb') (hc : count≤count') (hr : R≤R') (hv : V≤V') :
    TernaryFrontendResources.word N nb G count R V≤
      TernaryFrontendResources.word N nb' G count' R' V' := by
  unfold TernaryFrontendResources.word TernaryFrontendResources.eulerBound
    TernaryFrontendResources.sourceZeta
  gcongr

theorem front_bounds (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U) :
    let A := numbers maps τ cap M b K H drift scale n U r
    F^r*nb m r≤A.sourceHistogram ∧
    F^r*((N m r+1)*nb m r)≤A.bankCells ∧
    3*(entries (r := r) maps τ I).length≤A.tensorCells ∧
    4*nb m r≤A.bankCells ∧ 2*N m r+1≤A.prefixCells ∧
    3^(N m r)≤A.prefixCells ∧
    2*N m r*3^(N m r)+N m r≤A.nearMetadata ∧
    TernaryFrontendResources.eulerBound (N m r) (valueCap (r := r) maps cap I)+3≤A.nearDivision ∧
    TernaryFrontendResources.word (N m r) (nb m r) (F^r)
      (entries (r := r) maps τ I).length (3^(N m r)) (valueCap (r := r) maps cap I)≤A.frontendWord := by
  have hb := TernaryArenaSourceBounds.bank_size m r
  have hc := wanted_count (r := r) maps τ I M b n U hO
  have hv := value_cap (r := r) maps cap I n U H hnB hnC hweight
  have hn : N m r=fixedLength m*r := by unfold N; ring
  have hpow : 4^(N m r)=(4^fixedLength m)^r := by rw [hn,pow_mul]
  have h3 : 3^(N m r)≤(4^fixedLength m)^r := by
    rw [←hpow]
    exact Nat.pow_le_pow_left (by decide) _
  have h3cells : 3*(entries (r := r) maps τ I).length≤
      n*2^(LightTernaryDimensions.J M b n U)*(wantedWidth maps τ)^r*
        (LightTernaryDimensions.J M b n U+2)^4 := by
    have hp : 3≤(LightTernaryDimensions.J M b n U+2)^4 := by
      have := Nat.pow_le_pow_left (show 2≤LightTernaryDimensions.J M b n U+2 by omega) 4
      norm_num at this
      omega
    nlinarith [Nat.mul_le_mul hc hp]
  have hmeta := Nat.add_le_add_right (Nat.mul_le_mul_left (2*N m r) h3) (N m r)
  have hdiv := Nat.mul_le_mul_left (2*(N m r+1)*(4^fixedLength m)^r) hv
  have hw := word_mono (N := N m r) (G := F^r) hb hc h3 hv
  dsimp only
  dsimp only [numbers]
  rw [hn] at hmeta hdiv hw h3 ⊢
  simp only [TernaryFrontendResources.eulerBound,TernaryFrontendResources.sourceZeta] at hdiv ⊢
  have hpowN : 4^(fixedLength m*r)=(4^fixedLength m)^r := pow_mul _ _ _
  simp only [hpowN]
  have hwordeq : TernaryFrontendResources.word (fixedLength m*r) ((4^fixedLength m)^r) (F^r)
      (n*2^(LightTernaryDimensions.J M b n U)*(wantedWidth maps τ)^r) ((4^fixedLength m)^r)
      ((2^fixedAlpha m 2)^r*weight H (4^fixedLength m) U*(2*n*(sourceWidth maps cap)^r+1))=
      (numbers maps τ cap M b K H drift scale n U r).frontendWord := by
    simp only [TernaryFrontendResources.word,TernaryFrontendResources.eulerBound,
      TernaryFrontendResources.sourceZeta,numbers,hpowN]
    rw [show 2^(2*(fixedLength m*r)+1)=2*(4^fixedLength m)^r by
      rw [pow_succ,show 2*(fixedLength m*r)=(2*fixedLength m)*r by ring,pow_mul]
      norm_num [pow_mul,mul_comm]]
    rw [show 4^(fixedLength m*r+1)=4*(4^fixedLength m)^r by rw [pow_succ,pow_mul]; ring]
    ring
  rw [hwordeq] at hw
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,hw⟩
  · nlinarith [Nat.mul_le_mul_left (F^r) hb]
  · nlinarith [Nat.mul_le_mul_left (F^r*(fixedLength m*r+1)) hb]
  · omega
  · omega
  · omega
  · omega
  · exact hmeta
  · nlinarith


theorem capacity {lim : Light.Limits} {d : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale : ℕ)
    (I : Input) (n U : ℕ) (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (hweight : I.weightCap≤weight H (4^fixedLength m) U)
    (HC : Fits I.capacity (numbers maps τ cap M b K H drift scale n U r))
    (hend : TernaryArenaLayout.finish I.free I.capacity≤lim.space)
    (hprefix : I.prefixFree=TernaryArenaLayout.addr I.free I.capacity 13)
    (hw : (I.capacity : ℤ)≤lim.word) (hd : d+I.capacity≤lim.depth)
    (htime : TernaryArenaCountReady.queryTime (m := m) (r := r) I
      (valueCap (r := r) maps cap I)≤I.queryTime) :
    TernaryArenaCountReady.Capacity (lim := lim) (d := d) (r := r) maps τ cap I := by
  obtain ⟨hhist,hstage,hrecords,hmeta,hpowers,hrows,hnear,hdiv,hword⟩ :=
    front_bounds (r := r) maps τ cap M b K H drift scale I n U hnB hnC hO hweight
  have hpow : (4^fixedLength m)^r≤I.capacity := by
    have h := HC.prefixCells
    dsimp [numbers] at h
    omega
  have hb := (TernaryArenaSourceBounds.bank_size m r).trans hpow
  refine {
    endSpace:=hend
    prefixBank:=?_
    bankValues:=hhist.trans HC.sourceHistogram
    stages:=hstage.trans HC.bankCells
    records:=hrecords.trans HC.tensorCells
    metadata:=hmeta.trans HC.bankCells
    powers:=hpowers.trans HC.prefixCells
    nearRows:=hrows.trans HC.prefixCells
    nearMetadata:=hnear.trans HC.nearMetadata
    division:=hdiv.trans HC.nearDivision
    word:=(Int.ofNat_le.mpr (hword.trans HC.frontendWord)).trans hw
    depth:=?_
    time:=htime }
  · rw [hprefix]
    exact TernaryArenaLayout.before (by decide) hb
  · have h := HC.depth
    have hN : N m r=fixedLength m*r := by unfold N; ring
    dsimp [numbers] at h
    rw [hN]
    omega

end ThreeSum.TernaryArenaFrontBounds
