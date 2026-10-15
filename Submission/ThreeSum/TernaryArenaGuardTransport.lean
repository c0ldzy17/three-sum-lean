import Submission.ThreeSum.TernaryArenaCandidateGuard
import Submission.ThreeSum.TernaryArenaScoreScan
import Submission.ThreeSum.LightTernaryControllerFull

noncomputable section
namespace ThreeSum.TernaryArenaGuardTransport
open Light TernaryJointType TernaryLocalParameters TernaryCoverGoodMaps
open TernaryArenaSourceSetup TernaryNativeCompleteFrontend TernaryArenaLayout
open LightTernarySeedScoreFactory TernaryArenaSeedCandidate TernaryArenaScoreScan
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000
set_option maxRecDepth 24000

private theorem low {I : Input} {x : ℕ} (hx : x<I.free) : Protected I x := by
  unfold Protected addr
  omega

private theorem initial {I : Input} {x : ℕ} (hx : x<addr I.free I.capacity 1) : Protected I x := by
  unfold Protected addr at *
  omega

private theorem middle {I : Input} {x : ℕ} (hC : 106≤I.capacity)
    (hl : addr I.free I.capacity 2≤x) (hu : x<addr I.free I.capacity 9) : Protected I x := by
  unfold Protected addr at *
  omega

private theorem bank {I : Input} {x : ℕ} (hC : 106≤I.capacity)
    (hl : addr I.free I.capacity 13≤x) (hu : x<addr I.free I.capacity 16) : Protected I x := by
  unfold Protected addr at *
  omega

/-- Only immutable original arrays, old key slots4..6 and catalog7 are
read by the primitive guards. Four score arrays and host104 are excluded. -/
theorem primitive {I : Input} {A : Inputs} {seed positionCap : ℕ}
    {D : Data (config p r I A seed)} {μ ν : ℕ→ℤ}
    (M : TernaryArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (h : KeepInputs I μ ν) (hC : 106≤I.capacity)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hnO : I.requesterCount≤I.capacity) (hspan : A.J*p^(r-1)≤I.capacity) :
    TernaryArenaSeedPrimitiveGuards.Reads I A seed D ν positionCap := by
  have hk : Kept μ ν I.free := fun x hx => h x (low hx)
  refine {M with BRead:=?_,CRead:=?_,ORead:=?_,coeffRead:=?_,oldBRead:=?_,oldCRead:=?_,oldORead:=?_,catalogRead:=?_,positionRead:=?_}
  · intro i hi k hk'
    rw [hk _ (by have := M.matrixB; nlinarith)]
    exact M.BRead i hi k hk'
  · intro i hi k hk'
    rw [hk _ (by have := M.matrixC; nlinarith)]
    exact M.CRead i hi k hk'
  · intro i hi k hk'
    rw [hk _ (by have := M.matrixO; nlinarith)]
    exact M.ORead i hi k hk'
  · intro k hk'
    rw [hk _ (by have := M.menu; omega)]
    exact M.coeffRead k hk'
  · intro i hi
    have he : addr I.free I.capacity 4+I.nB≤addr I.free I.capacity 9 := before (by decide) hnB
    rw [h _ (middle hC (by unfold addr; omega) (by omega))]
    exact M.oldBRead i hi
  · intro i hi
    have he : addr I.free I.capacity 5+I.nC≤addr I.free I.capacity 9 := before (by decide) hnC
    rw [h _ (middle hC (by unfold addr; omega) (by omega))]
    exact M.oldCRead i hi
  · intro i hi
    have he : addr I.free I.capacity 6+I.requesterCount≤addr I.free I.capacity 9 := before (by decide) hnO
    rw [h _ (middle hC (by unfold addr; omega) (by omega))]
    exact M.oldORead i hi
  · intro k hk' i hi
    have he : addr I.free I.capacity 7+A.J*p^(r-1)≤addr I.free I.capacity 9 := before (by decide) hspan
    have hmul := Nat.mul_le_mul_left A.J (Nat.succ_le_of_lt hk')
    rw [h _ (middle hC (by unfold addr; omega) (by nlinarith))]
    exact M.catalogRead k hk' i hi
  · intro i hi
    rw [hk _ (by have := M.positions; omega)]
    exact M.positionRead i hi

/-- The canonical bank/powers occupy slots13..15, the signed source arrays
precede host1, and only host104 may change in the106-word header. -/
theorem tensor {lim : Limits} {depth K U seed : ℕ}
    {maps : Fin F→Weight m p} {τ cap : ℕ} {Q : TernaryGoodOutputCatalog.Output m}
    {I : Input} {A : Inputs} {D : Data (config p r I A seed)} {μ ν : ℕ→ℤ} {L R : ℕ→ℕ→ℤ}
    (G : TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R) (h : KeepInputs I μ ν)
    (hprefix : I.prefixFree=addr I.free I.capacity 13) :
    TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D ν L R := by
  refine {G with codes:=?_,powers:=?_,header:=?_,leftRead:=?_,rightRead:=?_}
  · intro i hi
    have hii : i<(bankCodes m r).length := by simpa [List.bind_eq_flatMap,←List.map_eq_flatMap] using hi
    have hnb := TernaryArenaCountReady.bank_size G.dimension
    have hfour : 4^(N m r)=2^(2*N m r) := by rw [Nat.pow_mul]
    have he : I.prefixFree+(bankCodes m r).length≤addr I.free I.capacity 16 := by
      have := G.prefixEnd
      change I.prefixFree+nb m r≤_
      omega
    rw [h _ (bank G.headerCells (by rw [←hprefix]; omega) (by omega))]
    exact G.codes i hi
  · intro i hi
    have he := G.prefixEnd
    have hl : addr I.free I.capacity 13≤I.prefixFree+4^(N m r)+i := by
      rw [←hprefix]
      exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
    rw [h _ (bank G.headerCells hl (by omega))]
    exact G.powers i hi
  · intro i hi hne
    have hi' : addr I.free I.capacity 1+i<addr I.free I.capacity 9 := by
      have he : addr I.free I.capacity 1+106≤addr I.free I.capacity 9 := before (by decide) G.headerCells
      omega
    rw [h _ ⟨Or.inl hi',by unfold addr at *; omega,by omega⟩]
    exact G.header i hi hne
  · intro i hi j hj
    have hoff := TernarySignedLayout.offset_lt hj
    have hmul := Nat.mul_le_mul_right (A.J+2) (Nat.succ_le_of_lt hi)
    rw [h _ (initial (by have := G.leftEnd; nlinarith))]
    exact G.leftRead i hi j hj
  · intro i hi j hj
    have hoff := TernarySignedLayout.offset_lt hj
    have hmul := Nat.mul_le_mul_right (A.J+2) (Nat.succ_le_of_lt hi)
    rw [h _ (initial (by have := G.rightEnd; nlinarith))]
    exact G.rightRead i hi j hj

/-- A scanning state obtains the full actual candidate guard from the
initial physical inputs and ScoreScan's proved immutable-memory invariant. -/
theorem guard {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : TernaryArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : TernaryArenaCandidateGuard.Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (h : KeepInputs I μ ν) (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hτ : 0<τ) (hraw : 1≤(TernaryGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(TernaryArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).score K|≤lim.word) :
    (TernaryArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).Guard lim depth K (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) ν := by
  exact TernaryArenaCandidateGuard.guard maps τ cap Q I A D ν L R
    (primitive M h G.headerCells G.nB G.nC B.requester B.catalog)
    (tensor G h hprefix) B hτ hraw hpaired

/-- The concrete arena also supplies every stronger replay-retention guard. -/
theorem full_guard {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : TernaryArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : TernaryArenaCandidateGuard.Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (h : KeepInputs I μ ν) (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hτ : 0<τ) (hraw : 1≤(TernaryGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(TernaryArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).score K|≤lim.word) :
    (TernaryArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).FullGuard lim depth K (4^fixedLength m) F
      (TernaryGoodOutputCatalog.raws maps τ) (TernaryGoodOutputCatalog.wordCodes maps τ)
      (TernaryGoodOutputCatalog.mapCodes maps τ) ν := by
  have H := guard maps τ cap Q I A D μ ν L R M G B h hprefix hτ hraw hpaired
  refine ⟨H,?_,?_⟩
  · exact H.1.collision.histogramAfter.trans (before (by decide) (by omega : 0≤I.capacity))
  · have loc (slot : ℕ) (h9 : 9≤slot) (h12 : slot≤12) :
        addr I.free I.capacity slot+seed<addr I.free I.capacity 16 ∧
        addr I.free I.capacity slot+seed≠addr I.free I.capacity 1+104 := by
      have hLo := Nat.mul_le_mul_right I.capacity h9
      have hHi := Nat.mul_le_mul_right I.capacity (show slot+1≤16 by omega)
      have hs := B.seed
      have hc := G.headerCells
      unfold addr
      constructor <;> nlinarith
    intro x hx
    change x∈[addr I.free I.capacity 9+seed,addr I.free I.capacity 10+seed,
      addr I.free I.capacity 11+seed,addr I.free I.capacity 12+seed] at hx
    simp only [List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] at hx
    rcases hx with rfl|rfl|rfl|rfl
    · exact loc 9 (by decide) (by decide)
    · exact loc 10 (by decide) (by decide)
    · exact loc 11 (by decide) (by decide)
    · exact loc 12 (by decide) (by decide)


private theorem coefficient_word_le (J p b power : ℕ) :
    LightPrimeCoefficient.word p≤LightTernaryAppendKeys.word (J+2) p b power := by
  have hm : (p+1)*(p+1)≤(p+1)*(p+b+1) := Nat.mul_le_mul_left _ (by omega)
  have hn : (p+1)*(p+b+1)≤(J+3)*((p+1)*(p+b+1)) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hp := hm.trans hn
  unfold LightPrimeCoefficient.word LightTernaryAppendKeys.word LightSignedRowHash.word
  nlinarith

/-- Replaying a selected actual candidate needs only the same immutable
input invariant. The real span extension reads catalog7 and writes8. -/
theorem span_guard {lim : Limits} {depth K U seed positionCap : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (A : Inputs) (D : Data (config p r I A seed))
    (μ ν : ℕ→ℤ) (L R : ℕ→ℕ→ℤ)
    (M : TernaryArenaSeedPrimitiveGuards.Reads I A seed D μ positionCap)
    (G : TernaryArenaSeedScoreReady.TensorGuard (lim := lim) (depth := depth) (K := K) (U := U)
      maps τ cap Q I A D μ L R)
    (B : TernaryArenaCandidateGuard.Resources (lim := lim) (depth := depth) (positionCap := positionCap) maps τ I A D)
    (h : KeepInputs I μ ν) (hprefix : I.prefixFree=addr I.free I.capacity 13)
    (hτ : 0<τ) (hraw : 1≤(TernaryGoodOutputCatalog.raws maps τ).length)
    (hpaired : |(TernaryArenaCandidateGuard.actual maps τ cap U Q I A seed D L R).score K|≤lim.word)
    (hnewSpan : A.J*p^(r-1)*p≤I.capacity) :
    LightTernaryControllerFactory.SpanGuard (config p r I A seed) D lim depth
      (addr I.free I.capacity 8) ν := by
  have H := guard maps τ cap Q I A D μ ν L R M G B h hprefix hτ hraw hpaired
  have ha := H.1.append
  have hs := H.1.span
  have hp : 0<p := (Fact.out : p.Prime).pos
  have hsource : A.J*p^(r-1)≤I.capacity :=
    (Nat.le_mul_of_pos_right _ hp).trans hnewSpan
  have rowBefore : (config p r I A seed).row+A.J≤addr I.free I.capacity 8 := by
    have hm := M.menu
    have hfree : I.free≤addr I.free I.capacity 8 := by unfold addr; omega
    omega
  refine {
    represents:=hs.represents
    rowsPos:=by change 0<p^(r-1); positivity
    spaceWord:=G.wordSpace
    source:=before (by decide) hsource
    row:=rowBefore
    output:=region_space (by decide) hnewSpan G.capacity.endSpace
    word:=(Int.ofNat_le.mpr (coefficient_word_le A.J p D.bB (p^(r-1)))).trans ha.Bword
    controls:=hs.controls
    bounded:=hs.bounded
    read:=hs.read
    rowRead:=?_
    depth:=by have := ha.depth; omega }
  intro i hi
  have hd : D.coeff i=LightStoredSpan.rowValues (TernaryPhysicalDigitSpan.physicalDigits D.logicalRow) i := hs.digits i hi
  rw [←hd]
  exact ha.coeffRead i (by change i<A.J+2; change i<A.J at hi; omega)


end ThreeSum.TernaryArenaGuardTransport
