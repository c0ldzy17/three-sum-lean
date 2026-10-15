import Submission.ThreeSum.TernaryArenaSeedCandidate
import Submission.ThreeSum.TernaryArenaTensorReady

noncomputable section
namespace ThreeSum.TernaryArenaSeedScoreReady
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
open LightTernarySeedScoreFactory TernaryArenaSeedCandidate
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 8000000
set_option maxRecDepth 24000

structure TensorGuard {lim : Limits} {depth K U seed : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ) : Prop where
  family : 1<F
  dimension : 0<N m r
  wordSpace : (lim.space : ℤ)≤lim.word
  capacity : TernaryArenaCountReady.Capacity (lim := lim) (d := depth+4) (r := r)
    maps τ cap (sourceInput I A seed D)
  nB : I.nB≤I.capacity
  nC : I.nC≤I.capacity
  prefixEnd : I.prefixFree+4^(N m r)+(2*N m r+1)≤addr I.free I.capacity 16
  headerBeforePrefix : addr I.free I.capacity 1+106≤I.prefixFree
  localNonempty : ∀right, 0<(localRecords maps cap right).length
  geometry : ∀right, TernaryArenaSourceLayout.Geometry
    (source (r := r) maps cap (sourceInput I A seed D) right) lim.space
  controls : ∀right, TernaryArenaSourceControls.Controls (r := r) maps cap
    (sourceInput I A seed D) right lim (depth+4)
  codes : Seg μ I.prefixFree ((bankCodes m r).map (fun c => (c : ℤ)))
  powers : LightSubsetAddress.Powers μ (I.prefixFree+4^(N m r)) (2*N m r)
  header : ∀i<106, i≠104 → μ (addr I.free I.capacity 1+i)=
    (setup (r := r) maps τ cap Q (sourceInput I A seed D)).argv.getD i 0
  leftEnd : A.leftTagged+I.nB*(A.J+2)≤addr I.free I.capacity 1
  rightEnd : A.rightTagged+I.nC*(A.J+2)≤addr I.free I.capacity 1
  leftRead : ∀i<I.nB,∀j<A.J+2,
    μ (A.leftTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=L i j
  rightRead : ∀i<I.nC,∀j<A.J+2,
    μ (A.rightTagged+i*(A.J+2)+TernarySignedLayout.offset A.J j)=R i j
  leftBound : ∀i<I.nB,∀j<A.J+2, |L i j|≤(U : ℤ)
  rightBound : ∀i<I.nC,∀j<A.J+2, |R i j|≤(U : ℤ)
  weightCap : U^2≤I.weightCap
  headerCells : 106≤I.capacity
  tensorCells : (entries (r := r) maps τ (sourceInput I A seed D)).length*(A.J+2)^4≤I.capacity
  quadCells : 4≤I.capacity
  powersCells : 5≤I.capacity
  columnCells : TernaryPairedColumnEnumeration.width K+1≤I.capacity
  tensorWord : (TernaryTensorWordResources.word K A.J
    (entries (r := r) maps τ (sourceInput I A seed D)).length
    (TernaryNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q (sourceInput I A seed D))) U : ℤ)≤lim.word

theorem count_eq (maps : Fin F→Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed : ℕ)
    (D : Data (config p r I A seed)) :
    (setup (r := r) maps τ cap Q (sourceInput I A seed D)).front.count=
      D.H (4^fixedLength m) F (TernaryGoodOutputCatalog.raws maps τ)
        (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) := by
  exact TernaryWantedBatchIndex.entries_length_eq_count _ _ _ _ _ _ _ _ _ _

/-- The actual append/wanted outputs supply the host's source keys and
wanted records. The sole count-header write is proved from its literal store. -/
theorem tensor_after_built {lim : Limits} {depth K U seed : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (P : AppendGuard (config p r I A seed) D lim depth μ)
    (G : TensorGuard (lim := lim) (depth := depth) (K := K) (U := U) maps τ cap Q I A D μ L R)
    (H : Built (config p r I A seed) D (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ ν) :
    LightTernaryTensorFactory.Ready (setup (r := r) maps τ cap Q (sourceInput I A seed D))
      lim (depth+1) K A.J (addr I.free I.capacity 1) A.leftTagged A.rightTagged
      (addr I.free I.capacity 23) (addr I.free I.capacity 24) (addr I.free I.capacity 25)
      (addr I.free I.capacity 26) (addr I.free I.capacity 27)
      (Function.update ν (addr I.free I.capacity 1+104)
        (D.H (4^fixedLength m) F (TernaryGoodOutputCatalog.raws maps τ)
          (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) : ℤ))
      L R U (TernaryNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q (sourceInput I A seed D))) := by
  let S := setup (r := r) maps τ cap Q (sourceInput I A seed D)
  let h := D.H (4^fixedLength m) F (TernaryGoodOutputCatalog.raws maps τ)
    (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ)
  let ξ := Function.update ν (addr I.free I.capacity 1+104) (h : ℤ)
  have kept : Kept μ ν (addr I.free I.capacity 16) := H.1.1.1.1
  have hc : S.front.count=h := count_eq maps τ cap Q I A seed D
  have hcodesEnd : I.prefixFree+(bankCodes m r).length≤addr I.free I.capacity 16 := by
    have hb := TernaryArenaCountReady.bank_size G.dimension
    have he : 4^(N m r)=2^(2*N m r) := by rw [Nat.pow_mul]
    have hp := G.prefixEnd
    change I.prefixFree+nb m r≤_
    omega
  have prefixRead (x : ℕ) (hx : I.prefixFree≤x) (hend : x<addr I.free I.capacity 16) : ξ x=μ x := by
    dsimp [ξ]
    rw [Function.update_of_ne (by have := G.headerBeforePrefix; omega)]
    exact kept x hend
  have aboveRead (x : ℕ) (hx : addr I.free I.capacity 16≤x) : ξ x=ν x := by
    dsimp [ξ]
    rw [Function.update_of_ne (by have := G.prefixEnd; have := G.headerBeforePrefix; omega)]
  have inputs : TernaryArenaSourceCountSeed.Reads (r := r) maps τ (sourceInput I A seed D) ξ := by
    refine ⟨?_,?_,?_,?_,?_,?_,?_⟩
    all_goals dsimp only [sourceInput]
    · intro i hi
      rw [aboveRead _ (by omega)]
      exact H.1.1.1.2 i hi
    · intro i hi
      rw [aboveRead _ (by have hh : addr I.free I.capacity 16≤addr I.free I.capacity 17 := before (by decide) (by omega : 0≤I.capacity); omega)]
      exact H.1.1.2 i hi
    · intro i hi
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have hh := LightTernaryAppendKeys.key_lt p (p^(r-1)) (A.J+2) D.oldB D.B D.coeff i (Fact.out : p.Prime).pos (P.oldBBound i hi)
      have hp : p^(r-1)*p≤p*(p+1)^r := by
        have hp1 := Nat.pow_le_pow_left (show p≤p+1 by omega) (r-1)
        have hp2 := Nat.pow_le_pow_right (show 1≤p+1 by omega) (show r-1≤r by omega)
        nlinarith
      exact_mod_cast hh.le.trans hp
    · intro i hi
      rw [abs_of_nonneg (Nat.cast_nonneg _)]
      have hh := LightTernaryAppendKeys.key_lt p (p^(r-1)) (A.J+2) D.oldC D.Cvalues D.coeff i (Fact.out : p.Prime).pos (P.oldCBound i hi)
      have hp : p^(r-1)*p≤p*(p+1)^r := by
        have hp1 := Nat.pow_le_pow_left (show p≤p+1 by omega) (r-1)
        have hp2 := Nat.pow_le_pow_right (show 1≤p+1 by omega) (show r-1≤r by omega)
        nlinarith
      exact_mod_cast hh.le.trans hp
    · intro i hi
      have hi' : i<(bankCodes m r).length := by simpa [List.bind_eq_flatMap,←List.map_eq_flatMap] using hi
      rw [prefixRead _ (by omega) (by omega)]
      exact G.codes i hi
    · intro i hi
      rw [prefixRead _ ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)) (by have := G.prefixEnd; omega)]
      exact G.powers i hi
    · have hs := H.2
      change Seg ξ (addr I.free I.capacity 19) _
      dsimp only [entries,sourceInput]
      rw [TernaryWantedBatchIndex.cells_entries_eq_rows]
      intro i hi
      rw [aboveRead _ (by have := P.BC; have := P.CO; have := G.capacity.records; dsimp [addr]; omega)]
      exact hs i hi
  have header : Seg ξ (addr I.free I.capacity 1) S.argv := by
    have hlen : S.argv.length=106 := rfl
    intro i hi
    have hi106 : i<106 := by simpa only [hlen] using hi
    have hbase : addr I.free I.capacity 1+i<addr I.free I.capacity 16 := by
      have := G.headerBeforePrefix
      have := G.prefixEnd
      omega
    rw [←List.getD_eq_getElem _ _ hi]
    by_cases he : i=104
    · subst i
      have h104 : S.argv.getD 104 0=(S.front.count : ℤ) := rfl
      rw [h104,hc]
      exact Function.update_self _ _ _
    · change ξ _=_
      dsimp [ξ]
      rw [Function.update_of_ne (by omega),kept _ hbase]
      exact G.header i hi106 he
  have tagRead (base n : ℕ) (L : ℕ→ℕ→ℤ)
      (hend : base+n*(A.J+2)≤addr I.free I.capacity 1)
      (hr : ∀i<n,∀j<A.J+2, μ (base+i*(A.J+2)+TernarySignedLayout.offset A.J j)=L i j) :
      ∀i<n,∀j<A.J+2, ξ (base+i*(A.J+2)+TernarySignedLayout.offset A.J j)=L i j := by
    intro i hi j hj
    have hoff := TernarySignedLayout.offset_lt hj
    have hmul := Nat.mul_le_mul_right (A.J+2) (Nat.succ_le_of_lt hi)
    have hx : base+i*(A.J+2)+TernarySignedLayout.offset A.J j<addr I.free I.capacity 1 := by nlinarith
    dsimp [ξ]
    rw [Function.update_of_ne (by omega),kept _ (by have := G.prefixEnd; have := G.headerBeforePrefix; omega)]
    exact hr i hi j hj
  apply TernaryArenaTensorReady.ready maps τ cap Q (sourceInput I A seed D) ξ L R
    G.family G.dimension G.wordSpace G.capacity G.nB G.nC G.prefixEnd G.localNonempty G.geometry G.controls inputs header
  · exact G.leftEnd.trans (before (by decide) (by omega : 0≤I.capacity))
  · exact G.rightEnd.trans (before (by decide) (by omega : 0≤I.capacity))
  · exact tagRead _ _ _ G.leftEnd G.leftRead
  · exact tagRead _ _ _ G.rightEnd G.rightRead
  · exact G.leftBound
  · exact G.rightBound
  · exact G.weightCap
  · exact G.headerCells
  · exact G.tensorCells
  · exact G.quadCells
  · exact G.powersCells
  · exact G.columnCells
  · exact G.tensorWord

private theorem frontWord_count (N nb groups count R A : ℕ) :
    3*count+5≤TernaryFrontendResources.word N nb groups count R A := by
  unfold TernaryFrontendResources.word
  generalize (N+1)*nb=s
  generalize 2^(2*N+1)=t
  generalize 4^(N+1)=u
  generalize TernaryFrontendResources.sourceZeta N A=z
  generalize TernaryFrontendResources.eulerBound N A=e
  generalize z^2=zz
  generalize 4^N*zz=pr
  omega

private theorem collision_card_le (n : ℕ) (keys : ℕ→ℕ) :
    (TernaryOriginalCollisions.collisionPairs (fun i : Fin n => keys i.val)).card≤n*n := by
  exact (Finset.card_le_univ _).trans_eq (by simp)

/-- Actual primitive guards and the canonical tensor constructor close the
entire SeedScore factory, including all nine real kernel calls. -/
theorem ready {lim : Limits} {depth K U seed V : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (P : AppendGuard (config p r I A seed) D lim depth μ)
    (Gspan : SpanGuard (config p r I A seed) D lim μ)
    (Gwanted : WantedGuard (config p r I A seed) D lim depth (4^fixedLength m) F
      (F*TernaryGoodOutputCatalog.cap m p τ) V (TernaryGoodOutputCatalog.raws maps τ)
      (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) μ)
    (Gcollision : CollisionGuard (config p r I A seed) D lim (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ))
    (G : TensorGuard (lim := lim) (depth := depth) (K := K) (U := U) maps τ cap Q I A D μ L R)
    (hseed : seed<I.capacity) :
    LightTernarySeedScoreFactory.Ready (config p r I A seed) D lim depth
      (4^fixedLength m) F (F*TernaryGoodOutputCatalog.cap m p τ) V K (N m r) U
      (setup (r := r) maps τ cap Q (sourceInput I A seed D)) L R
      (TernaryNativeMomentBounds.scoreBound (setup (r := r) maps τ cap Q (sourceInput I A seed D)))
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) μ := by
  have scoreAddr (i : ℕ) (hi : i<slots) : addr I.free I.capacity i+seed<lim.space := by
    have hh := region_space (free := I.free) (len := seed+1) hi
      (show seed+1≤I.capacity by omega) G.capacity.endSpace
    omega
  have hB : |D.collisionB|≤lim.word := by
    have hc := collision_card_le I.nB D.newB
    have hh := Gcollision.Bword
    change |((TernaryOriginalCollisions.collisionPairs (fun i : Fin I.nB => D.newB i.val)).card : ℤ)|≤_
    rw [Int.abs_natCast]
    apply (Int.ofNat_le.mpr hc).trans
    have hn : I.nB*I.nB≤I.nB*I.nB+I.nB+p^(r-1)*p+16 := by omega
    exact (Int.ofNat_le.mpr hn).trans hh
  have hC : |D.collisionC|≤lim.word := by
    have hc := collision_card_le I.nC D.newC
    have hh := Gcollision.Cword
    change |((TernaryOriginalCollisions.collisionPairs (fun i : Fin I.nC => D.newC i.val)).card : ℤ)|≤_
    rw [Int.abs_natCast]
    apply (Int.ofNat_le.mpr hc).trans
    have hn : I.nC*I.nC≤I.nC*I.nC+I.nC+p^(r-1)*p+16 := by omega
    exact (Int.ofNat_le.mpr hn).trans hh
  refine {
    append:=P
    span:=Gspan
    wanted:=Gwanted
    collision:=Gcollision
    leftN:=rfl
    rightN:=rfl
    count:=count_eq maps τ cap Q I A seed D
    countOutput:=rfl
    leftWeights:=rfl
    rightWeights:=rfl
    headerBefore:=G.headerBeforePrefix.trans
      (((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans G.prefixEnd)
    tensorAfter:=before (by decide) (by omega : 0≤I.capacity)
    tensor:=fun ν H => tensor_after_built maps τ cap Q I A D μ ν L R P G H
    flagAddr:=scoreAddr 9 (by decide)
    BAddr:=scoreAddr 10 (by decide)
    CAddr:=scoreAddr 11 (by decide)
    PAddr:=scoreAddr 12 (by decide)
    BWord:=hB
    CWord:=hC
    divideWord:=?_ }
  have he := count_eq maps τ cap Q I A seed D
  have hw := G.capacity.word
  have hn : 3*(entries (r := r) maps τ (sourceInput I A seed D)).length+5≤
      TernaryFrontendResources.word (N m r) (nb m r) (F^r)
        (entries (r := r) maps τ (sourceInput I A seed D)).length
        (3^(N m r)) (valueCap (r := r) maps cap (sourceInput I A seed D)) := by
    exact frontWord_count _ _ _ _ _ _
  have he' : (entries (r := r) maps τ (sourceInput I A seed D)).length=
    D.H (4^fixedLength m) F (TernaryGoodOutputCatalog.raws maps τ)
      (TernaryGoodOutputCatalog.wordCodes maps τ) (TernaryGoodOutputCatalog.mapCodes maps τ) := he
  rw [he'] at hn hw
  exact (Int.ofNat_le.mpr hn).trans hw

end ThreeSum.TernaryArenaSeedScoreReady
