import Submission.ThreeSum.BlockCoefficientRows
import Submission.ThreeSum.LightMaskHashes

/-!
# Constructing both raw endpoint arrays from selected block maps

The program constructs radix-weighted coefficient rows itself, then hashes
each stored subset in both orientations. Both endpoint arrays and the
coefficient rows are retained. The final specialization identifies the
results with the original block encoding, preserving occurrence indices.
-/

namespace ThreeSum.LightBlockSourceHashes

open Light BlockCoefficientRows

set_option maxHeartbeats 1500000
set_option maxRecDepth 10000

/-- Arguments: J, L, radix, occurrences, maps, coefficient-zero,
coefficient-one, masks, left output, right output, mask count, scratch. -/
def body (pCoefficients pHashes : ℕ) : Stmt :=
  .call pCoefficients [v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 11] 12 ;;
  .call pHashes [v 0 *' v 1,v 7,v 8,v 10,v 5,v 6,v 11] 12 ;;
  .call pHashes [v 0 *' v 1,v 7,v 9,v 10,v 6,v 5,v 11] 12

def time (J L n : ℕ) : ℕ :=
  LightBlockCoefficients.time J L + 2*LightMaskHashes.time (J*L) n + 200

def word (J L p U : ℕ) : ℕ :=
  LightBlockCoefficients.word J p U + LightOneHot.word (J*L) (p^J*U)

def space (work J L : ℕ) : ℕ := work + max (J+1) (J*L+1)

structure Procs (P : Program) (pMain : ℕ) where
  pCoefficients : ℕ
  pPowers : ℕ
  pScale : ℕ
  pHashes : ℕ
  pOneHot : ℕ
  coefficients : P[pCoefficients]? = some (LightBlockCoefficients.body pPowers pScale)
  powers : P[pPowers]? = some powTableBody
  scale : P[pScale]? = some LightScaleArray.body
  hashes : P[pHashes]? = some (LightMaskHashes.body pPowers pOneHot)
  onehot : P[pOneHot]? = some (LightOneHot.body pOneHot)
  main : P[pMain]? = some (body pCoefficients pHashes)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {J L p occ maps coeff0 coeff1 masks rawLeft rawRight n work U M : ℕ}
    (sel mask : ℕ → ℕ) (w0 w1 : ℕ → ℕ → ℕ)
    (hw : (lim.space : ℤ) ≤ lim.word) (hp : 1 ≤ p)
    (hd : d+J*L+2 ≤ lim.depth) (hspace : space work J L ≤ lim.space)
    (hocc : occ+J ≤ coeff0) (hmaps : maps+2*L*M ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*L ≤ coeff1)
    (hc1 : coeff1+J*L ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work) (hword : (word J L p U : ℤ) ≤ lim.word)
    (hsel : ∀ j < J, sel j < M)
    (hselRead : ∀ j < J, μ (occ+j) = (sel j : ℤ))
    (hread0 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+i) = (w0 s i : ℤ))
    (hread1 : ∀ s < M, ∀ i < L, μ (maps+2*L*s+L+i) = (w1 s i : ℤ))
    (hbound0 : ∀ s < M, ∀ i < L, w0 s i ≤ U)
    (hbound1 : ∀ s < M, ∀ i < L, w1 s i ≤ U)
    (hmaskRead : ∀ i < n, μ (masks+i) = (mask i : ℤ))
    (hmaskLt : ∀ i < n, mask i < 2^(J*L)) :
    Meets lim P pMain d [J,L,p,occ,maps,coeff0,coeff1,masks,rawLeft,rawRight,n,work]
      μ (time J L n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) =
          (OneHotMask.eval (flat J L p sel w0) (flat J L p sel w1) (J*L) (mask i) : ℤ)) ∧
        (∀ i < n, ν (rawRight+i) =
          (OneHotMask.eval (flat J L p sel w1) (flat J L p sel w0) (J*L) (mask i) : ℤ)) ∧
        LightBlockCoefficients.Rows ν coeff0 coeff1 L p sel w0 w1 J ∧ Kept μ ν coeff0) := by
  have hsc : work+(J+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_left _ _) work).trans hspace
  have hsh : work+(J*L+1) ≤ lim.space :=
    (Nat.add_le_add_left (le_max_right _ _) work).trans hspace
  have hcw : (LightBlockCoefficients.word J p U : ℤ) ≤ lim.word := by
    have hh : LightBlockCoefficients.word J p U ≤ word J L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hhw : (LightOneHot.word (J*L) (p^J*U) : ℤ) ≤ lim.word := by
    have hh : LightOneHot.word (J*L) (p^J*U) ≤ word J L p U := by unfold word; omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hwidth : (J : ℤ)*(L : ℤ) ≤ lim.word := by
    have hh : J*L ≤ lim.space := by omega
    exact (by exact_mod_cast hh : (J : ℤ)*(L : ℤ) ≤ lim.space).trans hw
  have hb0 : ∀ i < J*L, flat J L p sel w0 i ≤ p^J*U :=
    fun _ hi => flat_le hp hsel hbound0 hi
  have hb1 : ∀ i < J*L, flat J L p sel w1 i ≤ p^J*U :=
    fun _ hi => flat_le hp hsel hbound1 hi
  apply Meets.of_body S.main
  unfold body time
  have hc := LightBlockCoefficients.meets (d := d+1) (μ := μ)
    (J := J) (L := L) (p := p) (occ := occ) (maps := maps)
    (dst0 := coeff0) (dst1 := coeff1) (work := work) (U := U) (M := M)
    S.coefficients S.powers S.scale sel w0 w1 hw hp hocc hmaps hc0 (by omega)
    hsc hcw (by omega) hsel hselRead hread0 hread1 hbound0 hbound1
  light_call hc using LightBlockCoefficients.time,LightBlockCoefficients.roundTime,
    LightMaskHashes.time,LightOneHot.time,LightScaleArray.time with r μ₁ ⟨rows,kept₁,_⟩
  obtain ⟨rows0,rows1⟩ := rows_flat rows
  have masks₁ : ∀ i < n, μ₁ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₁ _ (by omega)).trans (hmaskRead i hi)
  have hl := LightMaskHashes.meets (d := d+1) (μ := μ₁)
    (L := J*L) (masks := masks) (dst := rawLeft) (n := n)
    (src0 := coeff0) (src1 := coeff1) (work := work) (U := p^J*U)
    S.hashes S.powers S.onehot mask (flat J L p sel w0) (flat J L p sel w1)
    hw (by omega) hsh (by omega) (by omega) hc1 (by omega) hhw masks₁ hmaskLt
    rows0 rows1 hb0 hb1
  light_call hl using LightBlockCoefficients.time,LightBlockCoefficients.roundTime,
    LightMaskHashes.time,LightOneHot.time,LightScaleArray.time with r μ₂ ⟨leftValues,_,kept₂⟩
  have masks₂ : ∀ i < n, μ₂ (masks+i) = (mask i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (masks₁ i hi)
  have rows0₂ : ∀ i < J*L, μ₂ (coeff0+i) = (flat J L p sel w0 i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows0 i hi)
  have rows1₂ : ∀ i < J*L, μ₂ (coeff1+i) = (flat J L p sel w1 i : ℤ) := by
    intro i hi
    exact (kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows1 i hi)
  have hr := LightMaskHashes.meets (d := d+1) (μ := μ₂)
    (L := J*L) (masks := masks) (dst := rawRight) (n := n)
    (src0 := coeff1) (src1 := coeff0) (work := work) (U := p^J*U)
    S.hashes S.powers S.onehot mask (flat J L p sel w1) (flat J L p sel w0)
    hw (by omega) hsh (by omega) (by omega) (by omega) hright hhw masks₂ hmaskLt
    rows1₂ rows0₂ hb1 hb0
  light_call hr using LightBlockCoefficients.time,LightBlockCoefficients.roundTime,
    LightMaskHashes.time,LightOneHot.time,LightScaleArray.time with r μ₃ ⟨rightValues,_,kept₃⟩
  refine ⟨?_,rightValues,?_,?_⟩
  · intro i hi
    exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans (leftValues i hi)
  · intro a ha i hi
    have he := LightBlockCoefficients.row_end_le (L := L) ha
    constructor
    · exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
        ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows a ha i hi).1)
    · exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
        ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (rows a ha i hi).2)
  · intro a ha
    exact (kept₃ _ ⟨by omega,Or.inl (by omega)⟩).trans
      ((kept₂ _ ⟨by omega,Or.inl (by omega)⟩).trans (kept₁ a ha))

def program : Program :=
  [body 1 4,LightBlockCoefficients.body 2 3,powTableBody,LightScaleArray.body,
    LightMaskHashes.body 2 5,LightOneHot.body 5]

def programProcs : Procs program 0 := ⟨1,2,3,4,5,rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- The fixed program returns the exact original block endpoints, rather
than an unspecified hash function supplied by its caller. -/
theorem program_meets
    {μ : ℕ → ℤ} {h J occ maps coeff0 coeff1 masks rawLeft rawRight n work : ℕ}
    (o : BlockEncoding.Occurrences h J)
    (sets : ℕ → Finset (BlockRows.Coord J (512*h)))
    (hw : (lim.space : ℤ) ≤ lim.word)
    (hd : d+J*(512*h)+2 ≤ lim.depth)
    (hspace : space work J (512*h) ≤ lim.space)
    (hocc : occ+J ≤ coeff0)
    (hmaps : maps+2*(512*h)*GlobalEncoding.scheduleSize h ≤ coeff0)
    (hmasks : masks+n ≤ coeff0) (hc0 : coeff0+J*(512*h) ≤ coeff1)
    (hc1 : coeff1+J*(512*h) ≤ rawLeft) (hleft : rawLeft+n ≤ rawRight)
    (hright : rawRight+n ≤ work)
    (hword : (word J (512*h) (LocalCoverBounds.localPrime h)
      (LocalCoverBounds.localPrime h) : ℤ) ≤ lim.word)
    (hselRead : ∀ j < J, μ (occ+j) = (occurrenceIndices o j : ℤ))
    (hread0 : ∀ s < GlobalEncoding.scheduleSize h, ∀ i < 512*h,
      μ (maps+2*(512*h)*s+i) = (mapRow h false s i : ℤ))
    (hread1 : ∀ s < GlobalEncoding.scheduleSize h, ∀ i < 512*h,
      μ (maps+2*(512*h)*s+512*h+i) = (mapRow h true s i : ℤ))
    (hmaskRead : ∀ i < n,
      μ (masks+i) = (SubsetAddress.subsetMask (BlockIndex.indexSet (sets i)) : ℤ)) :
    Meets lim program 0 d
      [J,512*h,LocalCoverBounds.localPrime h,occ,maps,coeff0,coeff1,masks,
        rawLeft,rawRight,n,work] μ (time J (512*h) n) (fun _ ν =>
        (∀ i < n, ν (rawLeft+i) = BlockEncoding.endpointLeft o (sets i)) ∧
        (∀ i < n, ν (rawRight+i) = BlockEncoding.endpointRight o (sets i)) ∧
        LightBlockCoefficients.Rows ν coeff0 coeff1 (512*h) (LocalCoverBounds.localPrime h)
          (occurrenceIndices o) (mapRow h false) (mapRow h true) J ∧
        Kept μ ν coeff0) := by
  have run := programProcs.meets (d := d) (μ := μ) (J := J) (L := 512*h)
    (p := LocalCoverBounds.localPrime h) (occ := occ) (maps := maps)
    (coeff0 := coeff0) (coeff1 := coeff1) (masks := masks) (rawLeft := rawLeft)
    (rawRight := rawRight) (n := n) (work := work) (U := LocalCoverBounds.localPrime h)
    (M := GlobalEncoding.scheduleSize h) (occurrenceIndices o)
    (fun i => SubsetAddress.subsetMask (BlockIndex.indexSet (sets i)))
    (mapRow h false) (mapRow h true) hw (LocalCoverBounds.localPrime_pos h)
    hd hspace hocc hmaps hmasks hc0 hc1 hleft hright hword
    (fun _ hj => occurrenceIndices_lt o hj) hselRead hread0 hread1
    (fun _ hs _ hi => mapRow_le false hs hi) (fun _ hs _ hi => mapRow_le true hs hi)
    hmaskRead (fun i _ => (SubsetAddress.subsetMask_isMask (BlockIndex.indexSet (sets i))).1)
  refine run.mono le_rfl ?_
  rintro r ν ⟨leftValues,rightValues,rows,kept⟩
  exact ⟨fun i hi => (leftValues i hi).trans (eval_left o (sets i)),
    fun i hi => (rightValues i hi).trans (eval_right o (sets i)),rows,kept⟩

theorem time_bound (J L n : ℕ) :
    time J L n ≤ 300*(J+1)*(L+1)+600*(J*L+1)*(n+1)+200 := by
  have hc := LightBlockCoefficients.time_bound J L
  have hh := LightMaskHashes.time_bound (J*L) n
  unfold time
  nlinarith

end ThreeSum.LightBlockSourceHashes
