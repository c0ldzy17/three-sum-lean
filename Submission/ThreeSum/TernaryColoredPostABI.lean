import Submission.ThreeSum.LightTernaryColoredSolver
import Submission.ThreeSum.TernaryArenaFinalSolver

noncomputable section
namespace ThreeSum.TernaryColoredPostABI
open Light LightTernaryColoredSolver TernaryArenaLayout
set_option maxRecDepth 24000
set_option maxHeartbeats 5000000

private theorem zeroCounts_left {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) :
    (LightTernaryCompactReporter.zeroCounts S).argv.getD 11 0=0 := by rfl
private theorem zeroCounts_right {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) :
    (LightTernaryCompactReporter.zeroCounts S).argv.getD 34 0=0 := by rfl
private theorem count_read {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) :
    (LightTernaryCompactReporter.zeroCounts S).argv.getD 104 0=(S.front.count : ℤ) := by rfl

theorem host_values {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (loc μ : ℕ→ℤ) (host : ℕ) (hloc : loc 10=(host : ℤ))
    (hreads : ∀ i<106,i≠11→i≠34→
      μ (host+i)=(LightTernaryCompactReporter.zeroCounts S).argv.getD i 0) :
    hostArgs.map (fun e=>e.val ⟨loc,μ⟩)=(LightTernaryCompactReporter.zeroCounts S).argv := by
  apply List.ext_getElem
  · rfl
  · intro i hi hi'
    have hii : i<106 := by simpa only [hostArgs,List.length_map,List.length_range] using hi
    simp only [hostArgs,List.getElem_map,List.getElem_range,Expr.val,k,M,v]
    split_ifs with hh
    · rcases hh with rfl|rfl
      · exact (zeroCounts_left S).symm.trans (List.getD_eq_getElem _ _ hi')
      · exact (zeroCounts_right S).symm.trans (List.getD_eq_getElem _ _ hi')
    · change μ ((loc 10+(i : ℤ)).toNat)=_
      rw [hloc,←Int.natCast_add,Int.toNat_natCast]
      exact (hreads i hii (by tauto) (by tauto)).trans (List.getD_eq_getElem _ _ hi')

/-- The nineteen-field preparation header is read literally at the final
call site; only its first six fields are needed by the final ABI. -/
theorem post_values {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (loc μ : ℕ→ℤ) (header host free capacity aBase nA bBase nB cBase nC q L : ℕ)
    (hloc5 : loc 5=(header : ℤ)) (hloc6 : loc 6=(free : ℤ))
    (hloc7 : loc 7=(capacity : ℤ)) (hloc10 : loc 10=(host : ℤ))
    (hloc12 : loc 12=(q : ℤ)) (hloc14 : loc 14=(L : ℤ))
    (hheader : Seg μ header [(aBase : ℤ),nA,bBase,nB,cBase,nC])
    (hhost : ∀ i<106,i≠11→i≠34→
      μ (host+i)=(LightTernaryCompactReporter.zeroCounts S).argv.getD i 0)
    (hrecords : S.front.records=addr free capacity 19)
    (hweightsB : S.left.weightBase=addr free capacity 28)
    (hweightsC : S.right.weightBase=addr free capacity 29)
    (houtput : S.front.dst=addr free capacity 53) :
    postArgs.map (fun e=>e.val ⟨loc,μ⟩)=
      LightTernaryPreparedPostSelection.args S
        (TernaryArenaCleanupLayout.layout free capacity aBase nA bBase nB cBase nC q L)
        (addr free capacity 26) (addr free capacity 25) := by
  have hHost := host_values S loc μ host hloc10 hhost
  have h104 : μ (host+104)=(S.front.count : ℤ) :=
    (hhost 104 (by decide) (by decide) (by decide)).trans (count_read S)
  have h0 := hheader 0 (by simp)
  have h1 := hheader 1 (by simp)
  have h2 := hheader 2 (by simp)
  have h3 := hheader 3 (by simp)
  have h4 := hheader 4 (by simp)
  have h5 := hheader 5 (by simp)
  simp only [List.getElem_cons_zero,List.getElem_cons_succ] at h0 h1 h2 h3 h4 h5
  simp only [Nat.add_zero] at h0
  simp only [postArgs,List.map_append,List.map_cons,List.map_nil]
  rw [hHost]
  simp only [cleanupArgs,List.map_cons,List.map_nil,H,A,Expr.val,k,M,v,Op.eval,
    hloc5,hloc6,hloc7,hloc10,hloc12,hloc14,←Int.natCast_add,←Int.natCast_mul,
    Int.toNat_natCast,Nat.add_zero,h0,h1,h2,h3,h4,h5,h104]
  simp only [LightTernaryPreparedPostSelection.args,LightTernaryPostSelection.args,
    LightOriginalSurvivorPair.Layout.args,TernaryArenaCleanupLayout.layout,
    LightTernaryCompactReporter.args,LightTernaryMomentReporter.args,
    LightTernaryMomentChannelFactory.args,LightTernaryMomentChannelStep.args,
    LightTernaryCompactReporter.zeroCounts,hrecords,hweightsB,hweightsC,houtput]
  simp only [addr,Nat.cast_add,Nat.cast_mul,List.append_assoc,List.cons_append,List.nil_append]

theorem argv_zeroCounts {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N) :
    (LightTernaryCompactReporter.zeroCounts S).argv=(S.argv.set 11 0).set 34 0 := by rfl

theorem argv_zeroCounts_get {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (i : ℕ) (hi : i<106) (h11 : i≠11) (h34 : i≠34) :
    (LightTernaryCompactReporter.zeroCounts S).argv.getD i 0=S.argv.getD i 0 := by
  have hlen : S.argv.length=106 := rfl
  rw [argv_zeroCounts]
  simp only [List.getD_eq_getElem _ _ (by simpa only [List.length_set,hlen] using hi : i<((S.argv.set 11 0).set 34 0).length),
    List.getD_eq_getElem _ _ (by simpa only [List.length_set,hlen] using hi : i<S.argv.length)]
  rw [List.getElem_set_of_ne (Ne.symm h34),List.getElem_set_of_ne (Ne.symm h11)]

/-- Compact counts change only the two source-count words in the live ABI.
Frontend value/time caps are proof data and carry no runtime word. -/
theorem compact_argv {p m F r : ℕ} [Fact p.Prime]
    (maps : Fin F→TernaryCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : TernaryArenaSourceSetup.Input) (nB nC : ℕ) :
    (LightTernaryCompactReporter.zeroCounts
      (TernaryArenaSourceSetup.setup (r := r) maps τ cap Q {I with nB:=nB,nC:=nC})).argv=
    (LightTernaryCompactReporter.zeroCounts
      (TernaryArenaSourceSetup.setup (r := r) maps τ cap Q I)).argv := by rfl

theorem selected_argv {p m F r J : ℕ} [Fact p.Prime]
    (maps : Fin F→TernaryCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : TernaryArenaSourceSetup.Input)
    (U radix nA : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) :
    (LightTernaryCompactReporter.zeroCounts (TernaryArenaSourceSetup.setup (r := r) maps τ cap Q
      (TernaryArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC))).argv=
    (LightTernaryCompactReporter.zeroCounts (TernaryArenaSourceSetup.setup (r := r) maps τ cap Q
      (TernaryArenaNativeComplete.input I U radix nA H A B C))).argv := by rfl

theorem host_safe {lim : Limits} (loc μ : ℕ→ℤ) (host : ℕ)
    (hloc : loc 10=(host : ℤ)) (hspace : host+106≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word) :
    ∀e∈hostArgs,e.Safe lim ⟨loc,μ⟩ := by
  intro e he
  obtain ⟨i,hi,rfl⟩ := List.mem_map.mp he
  have hi' : i<106 := List.mem_range.mp hi
  split_ifs
  · change |(0 : ℤ)|≤lim.word
    have := Int.natCast_nonneg lim.space
    simpa using (show (0 : ℤ)≤lim.word by omega)
  · change (True ∧ (i : ℤ)≤lim.word ∧ |loc 10+(i : ℤ)|≤lim.word) ∧
      0≤loc 10+(i : ℤ) ∧ loc 10+(i : ℤ)<(lim.space : ℤ)
    rw [hloc]
    have hh : host+i<lim.space := by omega
    have hh' : ((host+i : ℕ) : ℤ)<(lim.space : ℤ) := by exact_mod_cast hh
    simp only [←Int.natCast_add,abs_of_nonneg (Int.natCast_nonneg _)]
    have hii : (i : ℤ)≤(lim.space : ℤ) := by exact_mod_cast (show i≤lim.space by omega)
    exact ⟨⟨trivial,hii.trans hw,hh'.le.trans hw⟩,Int.natCast_nonneg _,hh'⟩

theorem post_safe {lim : Limits} (loc μ : ℕ→ℤ)
    (header host free capacity aBase nA bBase nB cBase nC q L : ℕ)
    (hloc5 : loc 5=(header : ℤ)) (hloc6 : loc 6=(free : ℤ))
    (hloc7 : loc 7=(capacity : ℤ)) (hloc10 : loc 10=(host : ℤ))
    (hloc12 : loc 12=(q : ℤ)) (hloc14 : loc 14=(L : ℤ))
    (hheader : Seg μ header [(aBase : ℤ),nA,bBase,nB,cBase,nC])
    (hheaderSpace : header+6≤lim.space) (hhostSpace : host+106≤lim.space)
    (hcapacity : 106≤capacity) (hend : finish free capacity≤lim.space)
    (hcounts : nB+3*nC+1≤capacity)
    (ha : aBase≤lim.space) (hna : nA≤lim.space)
    (hb : bBase≤lim.space) (hc : cBase≤lim.space)
    (hq : q≤lim.space) (hL : L≤lim.space)
    (hw : (lim.space : ℤ)≤lim.word) : ∀e∈postArgs,e.Safe lim ⟨loc,μ⟩ := by
  have h0 := hheader 0 (by simp)
  have h1 := hheader 1 (by simp)
  have h2 := hheader 2 (by simp)
  have h3 := hheader 3 (by simp)
  have h4 := hheader 4 (by simp)
  have h5 := hheader 5 (by simp)
  simp only [List.getElem_cons_zero,List.getElem_cons_succ,Nat.add_zero] at h0 h1 h2 h3 h4 h5
  have hs := host_safe loc μ host hloc10 hhostSpace hw
  unfold finish slots addr at hend
  intro e he
  unfold postArgs at he
  generalize hEs : hostArgs=es at he
  simp only [cleanupArgs,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at he
  simp only [or_assoc] at he
  rcases he with he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he|he
  all_goals first
    | exact hs e (hEs.symm ▸ he)
    | subst e
      simp only [H,A,Expr.Safe,Limits.Addr,Expr.val,k,M,v,Op.eval,hloc5,hloc6,hloc7,hloc10,hloc12,hloc14,
        ←Int.natCast_add,←Int.natCast_mul,Int.toNat_natCast,Nat.add_zero,h0,h1,h2,h3,h4,h5]
      all_goals try simp only [abs_of_nonneg (Int.natCast_nonneg _),true_and]
      all_goals (repeat' apply And.intro) <;> omega

@[simp] theorem post_cost : (postArgs.map Expr.cost).sum=671 := by rfl

theorem selected_host_reads {p m F r J : ℕ} [Fact p.Prime]
    (maps : Fin F→TernaryCoverGoodMaps.Weight m p) (τ cap : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : TernaryArenaSourceSetup.Input)
    (U radix nA : ℕ)
    (H : (TernarySignedReduction.Coordinate J→ZMod p)→ₗ[ZMod p] (Fin r→ZMod p))
    (A B C : ℕ→ℤ) (keysB keysC : ℕ→ℕ) (μ : ℕ→ℤ) (host : ℕ)
    (hhost : Seg μ host (TernaryArenaSourceSetup.setup (r := r) maps τ cap Q
      (TernaryArenaNativeComplete.input I U radix nA H A B C)).argv) :
    ∀i<106,i≠11→i≠34→μ (host+i)=
      (LightTernaryCompactReporter.zeroCounts (TernaryArenaSourceSetup.setup (r := r) maps τ cap Q
        (TernaryArenaPostSelection.selectedInput I U radix nA H A B C keysB keysC))).argv.getD i 0 := by
  intro i hi h11 h34
  rw [selected_argv,argv_zeroCounts_get _ i hi h11 h34]
  have hil : i<(TernaryArenaSourceSetup.setup (r := r) maps τ cap Q
      (TernaryArenaNativeComplete.input I U radix nA H A B C)).argv.length := hi
  rw [List.getD_eq_getElem _ _ hil]
  exact hhost i hil

end ThreeSum.TernaryColoredPostABI
