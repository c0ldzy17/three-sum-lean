import Submission.ThreeSum.TernaryArenaCandidateGuard
import Submission.ThreeSum.TernaryArenaTensorBounds
import Submission.ThreeSum.TernaryArenaAllocationResources

noncomputable section
namespace ThreeSum.TernaryArenaCandidateScoreBounds
open TernaryNativePairMoments TernaryNativeMomentBounds TernaryNativeTensorScore
open TernaryArenaPrefixFootprints TernaryArenaSourceSetup TernaryArenaSourceBounds
open TernaryArenaSeedCandidate LightTernarySeedScoreFactory
open TernaryCoverGoodMaps TernaryLocalParameters TernaryNativeCompleteFrontend
open scoped BigOperators
variable {p m F r : ℕ} [Fact p.Prime]
set_option maxHeartbeats 6000000

/-- Every literal physical pair and ordered K-tuple is retained in this bound. -/
theorem paired_le {N : ℕ} (S : TernarySourceCountExecutionFactory.Setup N)
    (K J tag : ℕ) (L R : ℕ→ℕ→ℤ)
    (hL : ∀ i<S.left.NL, ∀ a<J+2, (L i a).natAbs≤tag)
    (hR : ∀ i<S.right.NL, ∀ a<J+2, (R i a).natAbs≤tag) :
    pairedPotential S K J L R≤
      S.front.count*(pairBound S)^K*(J+2)^(2*K)*(((2*K).factorial*tag^(2*K))^2) := by
  classical
  have hrow (i : Fin S.front.count) (e : Fin K→Pair S i.val) :
      TernaryPairedPotential.rowWeight (Sum.elim
        (fun j => originalLeft S J L i.val (e j))
        (fun j => originalRight S J R i.val (e j)))≤
        (J+2)^(2*K)*(((2*K).factorial*tag^(2*K))^2) := by
    have hh := TernaryPairedPotential.rowWeight_le (Sum.elim
      (fun j => originalLeft S J L i.val (e j))
      (fun j => originalRight S J R i.val (e j))) tag (by
        intro j a
        cases j with
        | inl j => exact hL _ (indices_lt (e j)).1 _ a.isLt
        | inr j => exact hR _ (indices_lt (e j)).2 _ a.isLt)
    simpa only [Fintype.card_sum,Fintype.card_fin,←two_mul] using hh
  have hsum (i : Fin S.front.count) :
      (∑ e : Fin K→Pair S i.val, TernaryPairedPotential.rowWeight (Sum.elim
        (fun j => originalLeft S J L i.val (e j))
        (fun j => originalRight S J R i.val (e j))))≤
      (pairBound S)^K*((J+2)^(2*K)*(((2*K).factorial*tag^(2*K))^2)) := by
    calc
      _≤∑ _e : Fin K→Pair S i.val, (J+2)^(2*K)*(((2*K).factorial*tag^(2*K))^2) :=
        Finset.sum_le_sum fun e _ => hrow i e
      _=(Fintype.card (Pair S i.val))^K*((J+2)^(2*K)*(((2*K).factorial*tag^(2*K))^2)) := by simp
      _≤_ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (pair_card_le S i.val) K)
  unfold pairedPotential
  calc
    _≤∑ _i : Fin S.front.count, (pairBound S)^K*((J+2)^(2*K)*(((2*K).factorial*tag^(2*K))^2)) :=
      Finset.sum_le_sum fun i _ => hsum i
    _=_ := by simp; ring

theorem actual_score_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale tag : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed n U : ℕ)
    (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ)
    (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (htag : tag≤2*(4^fixedLength m)+1)
    (hL : ∀i<I.nB,∀a<A.J+2,(L i a).natAbs≤tag)
    (hR : ∀i<I.nC,∀a<A.J+2,(R i a).natAbs≤tag) :
    |(TernaryArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K|≤
      ((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) := by
  let S := setup (r := r) maps τ cap Q (sourceInput I A seed D)
  have hpair : pairBound S≤(n*(sourceWidth maps cap)^r)^2 := by
    have hL' := Nat.pow_le_pow_left (local_le maps cap false) r
    have hR' := Nat.pow_le_pow_left (local_le maps cap true) r
    have hh := Nat.mul_le_mul (Nat.mul_le_mul hnB hL') (Nat.mul_le_mul hnC hR')
    simpa [pairBound,S,setup,source,sourceInput,LightTernarySourceHost.size,pow_two] using hh
  have hcount : S.front.count≤n*2^(LightTernaryDimensions.J M b n U)*(wantedWidth maps τ)^r :=
    TernaryArenaFrontBounds.wanted_count (r := r) maps τ (sourceInput I A seed D) M b n U hO
  have hp := paired_le S K A.J tag L R hL hR
  have htagpow := Nat.pow_le_pow_left htag (2*K)
  have hp' : pairedPotential S K A.J L R≤
      (n*2^(LightTernaryDimensions.J M b n U)*(wantedWidth maps τ)^r)*
      (((n*(sourceWidth maps cap)^r)^2)^K)*(A.J+2)^(2*K)*
      (((2*K).factorial*(2*(4^fixedLength m)+1)^(2*K))^2) := by
    apply hp.trans
    exact Nat.mul_le_mul
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul hcount (Nat.pow_le_pow_left hpair K)))
      (Nat.pow_le_pow_left (Nat.mul_le_mul_left _ htagpow) 2)
  have hs : (2^(r*fixedPi m 2))^K=(2^(fixedPi m 2*K))^r := by
    simp only [←pow_mul]
    congr 1
    ring
  have hnon : 0≤(TernaryArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K := by
    change 0≤((2:ℤ)^(r*fixedPi m 2))^K*(pairedPotential S K A.J L R : ℤ)
    positivity
  rw [abs_of_nonneg hnon]
  change ((2:ℤ)^(r*fixedPi m 2))^K*(pairedPotential S K A.J L R : ℤ)≤_
  have hscale : ((2:ℤ)^(r*fixedPi m 2))^K=((2^(fixedPi m 2*K))^r : ℕ) := by exact_mod_cast hs
  rw [hscale]
  have hm := Nat.mul_le_mul_left ((2^(fixedPi m 2*K))^r) hp'
  rw [hJ] at hm
  rw [hJ]
  have hn : (2^(fixedPi m 2*K))^r*pairedPotential S K (LightTernaryDimensions.J M b n U) L R≤
      (numbers maps τ cap M b K H drift scale n U r).candidateScore := by
    apply hm.trans
    dsimp only [numbers]
    nlinarith only [Nat.zero_le (n^2)]
  exact_mod_cast hn

theorem collision_le {a : ℕ} (f : Fin a→ℕ) :
    |((TernaryOriginalCollisions.collisionPairs f).card : ℤ)|≤(a^2 : ℕ) := by
  have hh : (TernaryOriginalCollisions.collisionPairs f).card≤a^2 := by
    calc
      _≤(Finset.univ : Finset (Fin a×Fin a)).card := Finset.card_filter_le _ _
      _=_ := by simp [pow_two]
  rw [abs_of_nonneg (by positivity)]
  exact_mod_cast hh

/-- One explicit score cap covers both original collision scores and the
scaled, fully repeated physical paired potential. -/
theorem common_cap (maps : Fin F→Weight m p) (τ cap M b K H drift scale tag : ℕ)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed n U : ℕ)
    (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ)
    (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (htag : tag≤2*(4^fixedLength m)+1)
    (hL : ∀i<I.nB,∀a<A.J+2,|L i a|≤(tag : ℤ))
    (hR : ∀i<I.nC,∀a<A.J+2,|R i a|≤(tag : ℤ)) :
    |D.collisionB|≤((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) ∧
    |D.collisionC|≤((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) ∧
    |(TernaryArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K|≤
      ((numbers maps τ cap M b K H drift scale n U r).candidateScore : ℤ) := by
  have hbase : n^2≤(numbers maps τ cap M b K H drift scale n U r).candidateScore := by
    dsimp only [numbers]
    omega
  have hB := collision_le (fun i : Fin I.nB=>D.newB i.val)
  have hC := collision_le (fun i : Fin I.nC=>D.newC i.val)
  have hBn := (Nat.pow_le_pow_left hnB 2).trans hbase
  have hCn := (Nat.pow_le_pow_left hnC 2).trans hbase
  refine ⟨hB.trans (Int.ofNat_le.mpr hBn),hC.trans (Int.ofNat_le.mpr hCn),?_⟩
  apply actual_score_bound maps τ cap M b K H drift scale tag Q I A seed n U D L R
    hJ hnB hnC hO htag
  · intro i hi a ha
    have hh:=hL i hi a ha
    rw [←Int.natCast_natAbs] at hh
    exact_mod_cast hh
  · intro i hi a ha
    have hh:=hR i hi a ha
    rw [←Int.natCast_natAbs] at hh
    exact_mod_cast hh

/-- Allocation's fixed hardware need supplies the selector's common score
cap and the candidate paired-score word guard. -/
theorem allocated {lim : Light.Limits} {depth : ℕ}
    (maps : Fin F→Weight m p) (τ cap M b K H drift scale tag : ℕ)
    (Alloc : TernaryArenaAllocation.Allocation maps τ cap M b K H drift scale)
    (Q : TernaryGoodOutputCatalog.Output m) (I : Input) (A : Inputs) (seed n U : ℕ)
    (D : Data (config p r I A seed)) (L R : ℕ→ℕ→ℤ)
    (hok : (TernaryArenaAllocationResources.need Alloc n U).Ok lim I.free depth)
    (hcap : I.capacity=TernaryArenaLayout.capacity Alloc.D Alloc.E (n+U))
    (hr : r≤Nat.clog M (n^2))
    (hJ : A.J=LightTernaryDimensions.J M b n U)
    (hnB : I.nB≤n) (hnC : I.nC≤n)
    (hO : I.requesterCount≤n*2^(LightTernaryDimensions.J M b n U))
    (htag : tag≤2*(4^fixedLength m)+1)
    (hL : ∀i<I.nB,∀a<A.J+2,|L i a|≤(tag : ℤ))
    (hR : ∀i<I.nC,∀a<A.J+2,|R i a|≤(tag : ℤ)) :
    |D.collisionB|≤(I.capacity : ℤ) ∧ |D.collisionC|≤(I.capacity : ℤ) ∧
    |(TernaryArenaCandidateGuard.actual maps τ cap tag Q I A seed D L R).score K|≤(I.capacity : ℤ) ∧
    (I.capacity : ℤ)≤lim.word := by
  have hc := (Alloc.fits n U r hr).candidateScore
  rw [←hcap] at hc
  obtain ⟨hB,hC,hP⟩ := common_cap maps τ cap M b K H drift scale tag Q I A seed n U D L R
    hJ hnB hnC hO htag hL hR
  have hw := (TernaryArenaAllocationResources.ok Alloc hok).2.1
  rw [←hcap] at hw
  exact ⟨hB.trans (Int.ofNat_le.mpr hc),hC.trans (Int.ofNat_le.mpr hc),
    hP.trans (Int.ofNat_le.mpr hc),hw⟩

end ThreeSum.TernaryArenaCandidateScoreBounds
