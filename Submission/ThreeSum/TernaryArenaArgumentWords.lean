import Submission.ThreeSum.TernaryArenaMomentResources

/-! Every actual reporting argument is either a proved arena/prefix pointer
or one of the explicitly bounded canonical dimensions. Free addresses are
bounded by the supplied memory limit, independently of n and U. -/
noncomputable section
namespace ThreeSum.TernaryArenaArgumentWords
open Light TernaryArenaSourceSetup TernaryArenaLayout TernaryCoverGoodMaps
open TernaryLocalParameters TernaryJointType
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 2000000
set_option maxRecDepth 20000

def scalars (m p F r count : ℕ) : List ℕ :=
  [r,p,4^fixedLength m,F,p^r,nb m r,2*N m r,cut m r,r*alphaRank m,
    2^(r*fixedAlpha m 2),F^r,(N m r+1)*nb m r,N m r*nb m r,4^(N m r),count,1]
def scalarControl (m p F r count : ℕ) : ℕ :=(scalars m p F r count).sum

private theorem rank_max {N : ℕ} (Q : TritWord N) : TernaryBank.rank Q≤2*N := by
  have hh : ∑ i : Fin N, (Q i).val≤∑ _i : Fin N, 2 := by
    apply Finset.sum_le_sum
    intro i hi
    have := (Q i).isLt
    omega
  simpa [TernaryBank.rank,Nat.mul_comm] using hh

theorem args_word {lim : Limits} {originalB originalC : ℕ}
    (maps : Fin F→Weight m p) (τ cap : ℕ) (Q : TernaryGoodOutputCatalog.Output m)
    (I : Input) (hw : (lim.space : ℤ)≤lim.word)
    (hend : finish I.free I.capacity≤lim.space)
    (hscalars : scalarControl m p F r (entries (r := r) maps τ I).length≤I.capacity)
    (hnB : I.nB≤I.capacity) (hnC : I.nC≤I.capacity)
    (hprefix : I.prefixFree+4^(N m r)+(2*N m r+1)≤lim.space)
    (hB : originalB+I.nB≤lim.space) (hC : originalC+I.nC≤lim.space) :
    ∀ z∈LightTernaryMomentChannelFactory.args (setup (r := r) maps τ cap Q I)
      originalB originalC (addr I.free I.capacity 25), |z|≤lim.word := by
  have hcapacity : I.capacity≤lim.space := by
    have hh := region_space (free := I.free) (C := I.capacity) (slot := 0)
      (len := I.capacity) (by decide) le_rfl hend
    exact (Nat.le_add_left I.capacity I.free).trans (by simpa only [addr,Nat.zero_mul,Nat.add_zero] using hh)
  have hptr (s : ℕ) (hs : s<67) : addr I.free I.capacity s≤lim.space :=
    region_space (len := 0) hs (Nat.zero_le _) hend
  have hsmall (a : ℕ) (ha : a∈scalars m p F r (entries (r := r) maps τ I).length) :
      a≤I.capacity := (List.le_sum_of_mem ha).trans hscalars
  have hnum (a : ℕ) (ha : a∈scalars m p F r (entries (r := r) maps τ I).length) :
      a≤lim.space := (hsmall a ha).trans hcapacity
  have htail : N m r*nb m r≤I.capacity := hsmall _ (by simp [scalars])
  have hptrTail (s : ℕ) (hs : s<67) :
      addr I.free I.capacity s+N m r*nb m r≤lim.space := region_space hs htail hend
  have hpower : I.prefixFree+4^(N m r)≤lim.space := (Nat.le_add_right _ _).trans hprefix
  have hfree : I.prefixFree≤lim.space := (Nat.le_add_right _ _).trans hpower
  have hBptr : originalB≤lim.space := (Nat.le_add_right _ _).trans hB
  have hCptr : originalC≤lim.space := (Nat.le_add_right _ _).trans hC
  have hNB : I.nB≤lim.space := hnB.trans hcapacity
  have hNC : I.nC≤lim.space := hnC.trans hcapacity
  have hzero : 0≤lim.space := Nat.zero_le _
  have hN : N m r≤lim.space := (show N m r≤2*N m r by omega).trans
    (hnum _ (by simp [scalars]))
  have hQ : TernaryCodeSemantics.address
      (TernaryRepeatedWords.canonical (fun _ : Fin r => Q.val))≤lim.space :=
    (TernaryCodeSemantics.address_lt _).le.trans (hnum (4^(N m r)) (by simp [scalars]))
  have hD : LightTernaryPreparedWanted.D
      (TernaryRepeatedWords.canonical (fun _ : Fin r => Q.val)) (cut m r)≤lim.space := by
    have hrank : TernaryBank.rank (TernaryRepeatedWords.canonical (fun _ : Fin r => Q.val))≤2*N m r :=
      rank_max _
    exact (Nat.sub_le _ _).trans (hrank.trans (hnum _ (by simp [scalars])))
  have hcast (a : ℕ) (ha : a≤lim.space) : (a : ℤ)≤lim.word := (Int.ofNat_le.mpr ha).trans hw
  have h2N : |2*(N m r : ℤ)|≤lim.word := by
    rw [abs_of_nonneg (by positivity)]
    simpa using hcast (2*N m r) (hnum _ (by simp [scalars]))
  intro z hz
  dsimp only [LightTernaryMomentChannelFactory.args,LightTernaryMomentChannelStep.args,
    TernarySourceCountExecutionFactory.Setup.argv,LightTernarySourceCountHost.args,
    TernarySourceExecutionFactory.Setup.argv,LightTernarySourceCountHost.sourceArgs,
    TernaryCountExecutionFactory.Setup.argv,LightTernaryCountFrontend.args,
    LightTernaryWantedRows.args,LightTernaryWantedRowDispatch.args,LightTernaryPreparedWanted.args,
    LightTernaryWantedQuery.args,LightTernaryNearPair.args,
    setup,source,front,nearConfig,TernaryArenaFrontendResources.config] at hz
  simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,or_assoc,
    Bool.false_eq_true,ite_false,ite_true] at hz
  -- The following finite cases are exactly the runtime ABI's 115 entries.
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try simp only [← Nat.cast_mul,← Nat.cast_add,Int.abs_natCast]
  all_goals try exact h2N
  all_goals apply hcast
  all_goals first
    | exact hBptr | exact hCptr | exact hNB | exact hNC | exact hfree | exact hpower
    | exact hzero | exact hN | exact hQ | exact hD
    | exact hptr _ (by decide)
    | exact hptrTail _ (by decide)
    | exact hnum _ (by simp [scalars,N])

end ThreeSum.TernaryArenaArgumentWords
