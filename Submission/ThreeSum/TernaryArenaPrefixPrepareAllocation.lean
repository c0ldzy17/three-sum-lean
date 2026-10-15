import Submission.ThreeSum.TernaryArenaPrefixPrepare
import Submission.ThreeSum.TernaryArenaSelectorAllocation

noncomputable section
namespace ThreeSum.TernaryArenaPrefixPrepareAllocation
open TernaryArenaPrefixFootprints TernaryArenaAllocation TernaryArenaLayout
open TernaryArenaSourceSetup TernaryArenaSourceBounds TernaryLocalParameters TernaryCoverGoodMaps
variable {p m F : ℕ} [Fact p.Prime]
set_option maxHeartbeats 10000000
set_option maxRecDepth 24000

private theorem repeated_lt (q b j : ℕ) (hq : q<b) :
    LightTernaryRepeatWord.value q b j<b^j := by
  induction j with
  | zero => simp [LightTernaryRepeatWord.value]
  | succ j ih =>
    have hh := Nat.mul_le_mul_right b (show LightTernaryRepeatWord.value q b j+1≤b^j by omega)
    simp only [LightTernaryRepeatWord.value,pow_succ]
    nlinarith

private theorem prefix_cells (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U r : ℕ) :
    LightTernaryPrefixSetup.word m r F+4^(LightTernaryPrefixSetup.N m r)+
      2*LightTernaryPrefixSetup.N m r+9≤
      (numbers maps τ cap M b K H drift scale n U r).prefixCells := by
  have hN : LightTernaryPrefixSetup.N m r=fixedLength m*r := by
    unfold LightTernaryPrefixSetup.N fixedLength
    ring
  unfold LightTernaryPrefixSetup.word
  rw [hN,pow_succ,pow_succ,pow_mul]
  dsimp only [numbers]
  nlinarith

/-- The actual dynamic preparation envelope contains no address advice.
Its scalar values fit the explicit fixed header footprint at the new prefix. -/
theorem envelope_bound (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j U0 : ℕ)
    (I : Input) (Q : TernaryGoodOutputCatalog.Output m)
    (hscale : 1≤drift*scale)
    (hU0 : U0≤LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightTernaryDimensions.J M b n U) (n*2^(LightTernaryDimensions.J M b n U))) :
    TernaryArenaPrefixPrepare.envelope
      (TernaryArenaPrefixPrepare.inputs p m F j (LightTernaryDimensions.J M b n U) n U0
        (p^(2*K)) drift scale I Q)≤
      (numbers maps τ cap M b K H drift scale n U (j+1)).prefixCells+
        (numbers maps τ cap M b K H drift scale n U (j+1)).prefixHeader := by
  let X := TernaryArenaPrefixPrepare.inputs p m F j (LightTernaryDimensions.J M b n U) n U0
    (p^(2*K)) drift scale I Q
  have hp : p^j≤p^(j+1) := Nat.pow_le_pow_right (Fact.out : p.Prime).one_lt.le (by omega)
  have ha : (p^(2*K))^j≤(p^(2*K))^(j+1) :=
    Nat.pow_le_pow_right (Nat.one_le_pow _ _ (Fact.out : p.Prime).one_lt.le) (by omega)
  have h9 : 9^j≤9^(j+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hd : (drift*scale)^j≤(drift*scale)^(j+1) := Nat.pow_le_pow_right hscale (by omega)
  have hp' := Nat.mul_le_mul_right p hp
  have ha' := Nat.mul_le_mul_right (p^(2*K)) ha
  have ht9 := Nat.mul_le_mul_right 9 (Nat.mul_le_mul_right (n*n) h9)
  have ht := Nat.mul_le_mul hU0 hd
  have ht1 := Nat.mul_le_mul_right drift ht
  have ht2 := Nat.mul_le_mul_right scale ht1
  have hQ := (TernaryCodeSemantics.address_lt Q.val).le
  have hrep := (repeated_lt (TernaryCodeSemantics.address Q.val) (4^fixedLength m) (j+1)
    (TernaryCodeSemantics.address_lt Q.val)).le
  have hrep' := hrep.trans (Nat.pow_le_pow_left (show 4^fixedLength m≤4^fixedLength m+1 by omega) (j+1))
  have hnb : LightTernaryPrefixSetup.nb m (j+1)≤(4^fixedLength m)^(j+1) := by
    convert bank_size m (j+1) using 1
    congr 1
    unfold LightTernaryPrefixSetup.nb nb bankCodes N cut LightTernaryPrefixSetup.N fixedLength
    congr 1
    ring
  have hstride := Nat.mul_le_mul_left (LightTernaryPrefixSetup.N m (j+1)+1) hnb
  have htail := Nat.mul_le_mul_left (LightTernaryPrefixSetup.N m (j+1)) hnb
  have hN : LightTernaryPrefixSetup.N m (j+1)=fixedLength m*(j+1) := by
    unfold LightTernaryPrefixSetup.N fixedLength
    ring
  have hT : LightTernaryPrefixSetup.T m (j+1)=20384999*m*(j+1) := by
    unfold LightTernaryPrefixSetup.T
    ring
  have hfactor : 2^(fixedAlpha m 2*(j+1))=(2^fixedAlpha m 2)^(j+1) := by rw [pow_mul]
  have hsub : 2*(alphaRank m*(j+1))-LightTernaryPrefixSetup.T m (j+1)-1≤2*(alphaRank m*(j+1)) :=
    (Nat.sub_le _ _).trans (Nat.sub_le _ _)
  have hc := prefix_cells maps τ cap M b K H drift scale n U (j+1)
  let parts : List ℕ := [j+1,m,p,p^(j+1),fixedAlpha m 2,alphaRank m,2*(4^fixedLength m),
    LightTernaryDimensions.J M b n U,fixedLength m*(j+1),20384999*m*(j+1),
    2*(fixedLength m*(j+1)),F^(j+1),(4^fixedLength m)^(j+1),p^(j+1)*p,
    fixedAlpha m 2*(j+1),(2^fixedAlpha m 2)^(j+1),alphaRank m*(j+1),
    (fixedLength m*(j+1)+1)*(4^fixedLength m)^(j+1),
    fixedLength m*(j+1)*(4^fixedLength m)^(j+1),2*(alphaRank m*(j+1)),
    (4^fixedLength m+1)^(j+1),(p^(2*K))^(j+1)*p^(2*K),9^(j+1)*n^2*9,
    LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightTernaryDimensions.J M b n U) (n*2^(LightTernaryDimensions.J M b n U))*
      (drift*scale)^(j+1)*drift*scale,
    LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightTernaryDimensions.J M b n U) (n*2^(LightTernaryDimensions.J M b n U))*
      (drift*scale)^(j+1)*drift,9]
  have hpart (i : ℕ) (hi : i<26) : parts[i]'(by change i<26;exact hi)≤parts.sum :=
    List.le_sum_of_mem (List.getElem_mem (by change i<26;exact hi))
  have hparts : (numbers maps τ cap M b K H drift scale n U (j+1)).prefixHeader=
      106+100*parts.sum := by
    dsimp only [numbers,parts]
    simp only [List.sum_cons,List.sum_nil]
    ring
  have hscalar : (TernaryArenaPrefixPrepare.scalars X).sum≤
      (numbers maps τ cap M b K H drift scale n U (j+1)).prefixHeader-106 := by
    have hs : ∀x∈TernaryArenaPrefixPrepare.scalars X,x≤parts.sum := by
      intro x hx
      dsimp only [TernaryArenaPrefixPrepare.scalars,X,TernaryArenaPrefixPrepare.inputs] at hx
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
      rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      · exact hpart 0 (by decide)
      · exact hpart 1 (by decide)
      · exact hpart 2 (by decide)
      · exact hp.trans (hpart 3 (by decide))
      · exact hpart 4 (by decide)
      · exact hpart 5 (by decide)
      · exact hQ.trans ((by omega : 4^fixedLength m≤2*(4^fixedLength m)).trans (hpart 6 (by decide)))
      · exact (by omega : 4^fixedLength m≤2*(4^fixedLength m)).trans (hpart 6 (by decide))
      · exact hpart 7 (by decide)
      · rw [hN];exact hpart 8 (by decide)
      · rw [hT];exact hpart 9 (by decide)
      · rw [hN];exact hpart 10 (by decide)
      · exact hpart 11 (by decide)
      · exact hnb.trans (hpart 12 (by decide))
      · exact hp'.trans (hpart 13 (by decide))
      · exact hpart 14 (by decide)
      · rw [hfactor];exact hpart 15 (by decide)
      · exact hpart 16 (by decide)
      · rw [hN] at hstride ⊢;exact hstride.trans (hpart 17 (by decide))
      · rw [hN] at htail ⊢;exact htail.trans (hpart 18 (by decide))
      · exact hpart 19 (by decide)
      · exact hsub.trans (hpart 19 (by decide))
      · exact hrep'.trans (hpart 20 (by decide))
      · exact hp'.trans (hpart 13 (by decide))
      · exact hp'.trans (hpart 13 (by decide))
      · exact ha'.trans (hpart 21 (by decide))
      · have hh : 9^(j+1)*n^2*9≤parts.sum := hpart 22 (by decide)
        rw [pow_two] at hh
        exact ht9.trans hh
      · have hh : 9^(j+1)*n^2*9≤parts.sum := hpart 22 (by decide)
        rw [pow_two] at hh
        exact ht9.trans hh
      · exact ht2.trans (hpart 23 (by decide))
      · exact ht1.trans (hpart 24 (by decide))
      · exact hpart 25 (by decide)
    have hh := List.sum_le_card_nsmul (TernaryArenaPrefixPrepare.scalars X) parts.sum hs
    rw [hparts]
    change (TernaryArenaPrefixPrepare.scalars X).sum≤(106+100*parts.sum)-106
    have hlen : (TernaryArenaPrefixPrepare.scalars X).length=31 := rfl
    simp only [hlen,nsmul_eq_mul] at hh
    omega
  unfold TernaryArenaPrefixPrepare.envelope TernaryArenaPrefixPrepare.footprint
  change 106+LightTernaryPrefixSetup.word m (j+1) F+
    (4^(LightTernaryPrefixSetup.N m (j+1))+2*LightTernaryPrefixSetup.N m (j+1)+9)+
    (TernaryArenaPrefixPrepare.scalars X).sum≤_
  have hh : 106≤(numbers maps τ cap M b K H drift scale n U (j+1)).prefixHeader := by
    dsimp only [numbers]
    omega
  omega

/-- The fixed polynomial capacity selected once for all inputs and prefixes
supplies the dynamic header constructor's last scalar premise. -/
theorem allocated (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j U0 : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (Q : TernaryGoodOutputCatalog.Output m) (hj : j+1≤Nat.clog M (n^2))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hscale : 1≤drift*scale)
    (hU0 : U0≤LightTernaryInitialBudgets.word K b (p^(2*K)) drift scale n
      (LightTernaryDimensions.J M b n U) (n*2^(LightTernaryDimensions.J M b n U))) :
    TernaryArenaPrefixPrepare.envelope
      (TernaryArenaPrefixPrepare.inputs p m F j (LightTernaryDimensions.J M b n U) n U0
        (p^(2*K)) drift scale I Q)≤I.capacity := by
  have hb := envelope_bound maps τ cap M b K H drift scale n U j U0 I Q hscale hU0
  have hs : (numbers maps τ cap M b K H drift scale n U (j+1)).prefixCells+
      (numbers maps τ cap M b K H drift scale n U (j+1)).prefixHeader≤
      total maps τ cap M b K H drift scale n U (j+1) := by
    unfold total
    generalize numbers maps τ cap M b K H drift scale n U (j+1)=A
    rw [Numbers.sum_list]
    omega
  rw [hcap]
  exact hb.trans (hs.trans (Alloc.total_le n U (j+1) hj))

/-- Specialization to the actual initialized paired threshold; the
requester-count cap is the only required input-size comparison. -/
theorem allocated_initial (maps : Fin F→Weight m p) (τ cap M b K H drift scale n U j nO : ℕ)
    (Alloc : Allocation maps τ cap M b K H drift scale) (I : Input)
    (Q : TernaryGoodOutputCatalog.Output m) (hj : j+1≤Nat.clog M (n^2))
    (hcap : I.capacity=capacity Alloc.D Alloc.E (n+U))
    (hscale : 1≤drift*scale)
    (hO : nO≤n*2^(LightTernaryDimensions.J M b n U)) :
    TernaryArenaPrefixPrepare.envelope
      (TernaryArenaPrefixPrepare.inputs p m F j (LightTernaryDimensions.J M b n U) n
        (LightTernaryInitialBudgets.initial K b n (LightTernaryDimensions.J M b n U) nO)
        (p^(2*K)) drift scale I Q)≤I.capacity := by
  apply allocated maps τ cap M b K H drift scale n U j _ Alloc I Q hj hcap hscale
  exact TernaryArenaSelectorAllocation.initial_le hO _ _ _

end ThreeSum.TernaryArenaPrefixPrepareAllocation
