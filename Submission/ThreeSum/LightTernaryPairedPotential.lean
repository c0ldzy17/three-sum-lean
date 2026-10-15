import Submission.ThreeSum.TernaryPairedColumnEnumeration
import Submission.ThreeSum.LightWeightRow

/-! Actual complete paired-potential arithmetic from a physical fourth
mixed tensor array. The program creates its own radix powers, enumerates
every ordered column tuple, evaluates the checked fixed polynomial, and
adds the signed values. No determinant/potential oracle is called. -/

noncomputable section
namespace ThreeSum.LightTernaryPairedPotential

open Light LightTernaryPairedPolynomial TernaryPairedColumnEnumeration TernaryPairedTensor
open scoped BigOperators

def columns (m Λ i : ℕ) : PairedIndex m → ℕ :=
  fun r => WeightEnumeration.digit Λ (width m) i (Fintype.equivFin (PairedIndex m) r).val

def term (m base Λ : ℕ) (μ : ℕ → ℤ) (i : ℕ) : ℤ :=
  value (fun q => μ (base+tensorIndex Λ (columns m Λ i q.1) (columns m Λ i q.2.1)
    (columns m Λ i q.2.2.1) (columns m Λ i q.2.2.2)))

def prefixSum (m base Λ : ℕ) (μ : ℕ → ℤ) (i : ℕ) : ℤ :=
  ∑ j ∈ Finset.range i, term m base Λ μ j

def body (m pPowers pRow pPoly : ℕ) : Stmt :=
  .call pPowers [v 3,k (width m+1),v 1] 4 ;;
  .set 5 (M (v 3 +' k (width m))) ;;
  .set 6 (k 0) ;;
  .for 7 (v 5) (
    .call pRow [k (width m),v 1,v 7,v 3,k 0,k 1,v 2,k (width m)] 8 ;;
    .call pPoly [v 0,v 1,v 2] 9 ;;
    .set 6 (v 6 +' v 9)) ;;
  .set 0 (v 6)

def time (m Λ : ℕ) : ℕ := powTableTime (width m+1)+Λ^(width m)*
  (LightWeightRow.time (width m) (Λ^width m)+LightTernaryPairedPolynomial.time m+300)+300

def word (m Λ : ℕ) (U : ℤ) : ℤ :=
  10*((Λ^(width m+1) : ℕ)+(Λ^width m)+width m+Λ+2)+
    2*((Λ^width m : ℕ)+1)*((polynomial m).bound U+1)

theorem term_abs_le (m base Λ : ℕ) (μ : ℕ → ℤ) (U : ℤ) (hU : 0≤U) (hΛ : 1≤Λ)
    (hT : ∀ k<Λ^4, |μ (base+k)|≤U) (i : ℕ) :
    |term m base Λ μ i|≤(polynomial m).bound U := by
  apply value_abs_le _ U hU
  intro q
  exact hT _ (tensorIndex_lt
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
    (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega)))

theorem prefixSum_abs_le (m base Λ : ℕ) (μ : ℕ → ℤ) (U : ℤ) (hU : 0≤U) (hΛ : 1≤Λ)
    (hT : ∀ k<Λ^4, |μ (base+k)|≤U) (i : ℕ) :
    |prefixSum m base Λ μ i| ≤ (i : ℤ)*(polynomial m).bound U := by
  unfold prefixSum
  calc
    _ ≤ ∑ j ∈ Finset.range i, |term m base Λ μ j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j ∈ Finset.range i, (polynomial m).bound U :=
      Finset.sum_le_sum fun j hj => term_abs_le m base Λ μ U hU hΛ hT j
    _ = _ := by simp

theorem prefixSum_eq_paired_potential {P₀ : Type*} [Fintype P₀]
    (m base Λ : ℕ) (μ : ℕ → ℤ) (L R' : P₀ → Fin Λ → ℤ)
    (hTensor : ∀ a b c d : Fin Λ, μ (base+tensorIndex Λ a.val b.val c.val d.val)=tensor L R' a b c d) :
    prefixSum m base Λ μ (Λ^width m) =
      ((∑ e : Fin m → P₀, TernaryPairedPotential.rowWeight
        (Sum.elim (fun i => L (e i)) (fun i => R' (e i)))) : ℤ) := by
  unfold prefixSum term
  change (∑ i ∈ Finset.range (Λ^width m),
    (fun cols : PairedIndex m → ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
      (fun r => WeightEnumeration.digit Λ (width m) i (Fintype.equivFin (PairedIndex m) r).val)) = _
  have he := sum_digits_eq_sum_columns m Λ
    (fun cols : PairedIndex m → ℕ => value (fun q =>
      μ (base+tensorIndex Λ (cols q.1) (cols q.2.1) (cols q.2.2.1) (cols q.2.2.2))))
  refine he.trans ?_
  have hformula := full_potential_tensor_expansion (m := m) L R'
  refine Eq.trans ?_ hformula.symm
  apply Finset.sum_congr rfl
  intro cols hcols
  unfold value
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact hTensor _ _ _ _

def Inv (m base Λ colsBase powers : ℕ) (μ₁ : ℕ → ℤ) (powRet : ℤ) (i : ℕ) (σ : State) : Prop :=
  ∃ (r₀ r₁ : ℤ) (ν : ℕ → ℤ),
    σ=⟨frame [base,Λ,colsBase,powers,powRet,Λ^width m,prefixSum m base Λ μ₁ i,i,r₀,r₁],ν⟩ ∧
      SameOutside μ₁ ν colsBase (width m)

theorem meets (m base Λ colsBase powers : ℕ) (μ : ℕ → ℤ)
    {lim : Limits} {P : Program} {pMain pPowers pRow pDigit pDivide pPoly depth : ℕ}
    (hmain : P[pMain]?=some (body m pPowers pRow pPoly))
    (hPowers : P[pPowers]?=some powTableBody)
    (hRow : P[pRow]?=some (LightWeightRow.body pDigit))
    (hDigit : P[pDigit]?=some (LightRadixDigit.body pDivide))
    (hDivide : P[pDivide]?=some LightSmallDivide.body)
    (hPoly : P[pPoly]?=some (LightTernaryPairedPolynomial.body m))
    (hΛ : 1≤Λ) (hw : (lim.space : ℤ)≤lim.word) (hd : depth+2<lim.depth)
    (hTspace : base+Λ^4≤lim.space) (hCspace : colsBase+width m≤lim.space)
    (hPspace : powers+(width m+1)≤lim.space)
    (hTC : Apart base (Λ^4) colsBase (width m))
    (hTP : Apart base (Λ^4) powers (width m+1))
    (hPC : Apart powers (width m+1) colsBase (width m))
    (U : ℤ) (hU : 0≤U) (hTabs : ∀ k<Λ^4, |μ (base+k)|≤U)
    (hWord : word m Λ U≤lim.word)
    (hPolyWord : (polynomial m).coefficient*(U+1)^(polynomial m).degree≤lim.word) :
    Meets lim P pMain depth [base,Λ,colsBase,powers] μ (time m Λ)
      (fun r ν => r=prefixSum m base Λ μ (Λ^width m) ∧
        (∀ k<Λ^4, ν (base+k)=μ (base+k)) ∧ Kept μ ν (min colsBase powers)) := by
  let B := (polynomial m).bound U
  let N := Λ^width m
  have hwidth : width m=m+m := by simp [width,PairedIndex,Fintype.card_sum]
  have hNp : (0 : ℤ)≤(Λ : ℤ)^width m := pow_nonneg (Int.natCast_nonneg _) _
  have hNLp : (0 : ℤ)≤(Λ : ℤ)^(width m+1) := pow_nonneg (Int.natCast_nonneg _) _
  have hDimNonneg : (0 : ℤ)≤width m := Int.natCast_nonneg _
  have hB : 1≤B := (polynomial m).bound_pos hU
  have hwordNat (x : ℕ) (hx : x≤Λ^(width m+1)+N+width m+Λ+2) : (x : ℤ)≤lim.word := by
    have hh : (x : ℤ)≤Λ^(width m+1)+N+width m+Λ+2 := by exact_mod_cast hx
    unfold word at hWord
    push_cast at hWord
    dsimp [B,N] at *
    nlinarith [Nat.zero_le (Λ^(width m+1)),Nat.zero_le (Λ^width m)]
  have hNWord := hwordNat N (by omega)
  have hdimWord := hwordNat (width m) (by omega)
  have hΛWord := hwordNat Λ (by omega)
  have hOneWord := hwordNat 1 (by omega)
  have hBWord : B≤lim.word := ((polynomial m).bound_polynomial hU).trans hPolyWord
  have hsumWord : (N+1 : ℤ)*B≤lim.word := by
    unfold word at hWord
    push_cast at hWord
    dsimp [B,N] at *
    nlinarith [Nat.zero_le (Λ^(width m+1)),Nat.zero_le (Λ^width m)]
  apply Meets.of_body hmain
  unfold body time
  have hp := powTable_meets (d := depth+1) (μ := μ) (dst := powers)
    (L := width m+1) (b := Λ) hPowers hw hPspace (by
      intro j hj
      exact hwordNat (Λ^j) ((Nat.pow_le_pow_right hΛ hj).trans (by omega)))
  light_call hp using LightWeightRow.time with powRet μ₁ ⟨hpow,hpowKeep⟩
  have hpread (e : ℕ) (he : e≤width m) : μ₁ (powers+e)=((Λ^e : ℕ) : ℤ) := by
    exact (by simpa [powList] using hpow e (by simp; omega))
  have hTread (k : ℕ) (hk : k<Λ^4) : μ₁ (base+k)=μ (base+k) := by
    exact hpowKeep _ (by omega)
  have hT₁ (k : ℕ) (hk : k<Λ^4) : |μ₁ (base+k)|≤U := by rw [hTread k hk]; exact hTabs k hk
  have hlast := hpread (width m) le_rfl
  simp only [hwidth] at hlast
  have hlastInt : μ₁ ((powers : ℤ)+((m : ℤ)+m)).toNat=(N : ℤ) := by
    have he : ((powers : ℤ)+((m : ℤ)+m)).toNat=powers+(m+m) := by omega
    rw [he]
    simpa [N,hwidth] using hlast
  light_set (N : ℕ) using hlastInt, hwidth, N, LightWeightRow.time
  light_set (0 : ℤ) using LightWeightRow.time
  refine Ends.pieceThen (Ends.for (T := N*(LightWeightRow.time (width m) N+
    LightTernaryPairedPolynomial.time m+250)+20)
    (Q := Inv m base Λ colsBase powers μ₁ powRet N)
    (Inv m base Λ colsBase powers μ₁ powRet) N
    (LightWeightRow.time (width m) N+LightTernaryPairedPolynomial.time m+240)
    ?_ ?_ ?_ ?_ (hT := by light_time [N,hwidth])) ?_
    (hT := by light_time [N,hwidth])
  · refine ⟨0,0,μ₁, ?_,SameOutside.refl⟩
    simp [Inv,prefixSum,update_frame_setLocal,N]
    exact (frame_append_zeros ([base,Λ,colsBase,powers,powRet,((Λ^(m+m) : ℕ) : ℤ),0,0] : List ℤ) 2).symm
  · rintro i _ hi _ ⟨r₀,r₁,ν,rfl,hkeep⟩
    have hpowν (e : ℕ) (he : e≤width m) : ν (powers+e)=((Λ^e : ℕ) : ℤ) := by
      rw [hkeep _ (by omega)]
      exact hpread e he
    have hreadν (k : ℕ) (hk : k<Λ^4) : ν (base+k)=μ₁ (base+k) := hkeep _ (by omega)
    have hRowWord : (LightWeightRow.word (width m) Λ i 0 1 : ℤ)≤lim.word := by
      have hx : LightWeightRow.word (width m) Λ i 0 1 ≤
          4*(Λ^(width m+1)+N+width m+Λ+2) := by unfold LightWeightRow.word; omega
      have hz := Int.ofNat_le.mpr hx
      unfold word at hWord
      push_cast at hWord hz
      dsimp [N,B] at *
      nlinarith
    have hrow := LightWeightRow.meets (d := depth+1) (μ := ν)
      (W := width m) (p := Λ) (k := i) (powers := powers) (start := 0) (stride := 1)
      (dst := colsBase) (n := width m) hRow hDigit hDivide hw (by omega) hΛ
      hCspace hPspace hPC hRowWord (by intro j hj; omega) hpowν
    have hrowTime : LightWeightRow.time (width m) i≤LightWeightRow.time (width m) N := by
      unfold LightWeightRow.time LightRadixDigit.time
      exact Nat.add_le_add_right (Nat.mul_le_mul_left _ (by omega)) _
    have hNcanonical : N=Λ^(m*2) := by simp only [N,hwidth]; congr 1; omega
    have hmi : m*i≤m*(Λ^(m*2)) := Nat.mul_le_mul_left m (by omega)
    light_call hrow using width,N,LightWeightRow.time,LightRadixDigit.time
      with rowRet ν₁ ⟨hcols,hrowKeep⟩
    have hkeep₁ := hkeep.trans hrowKeep
    have hread₁ (k : ℕ) (hk : k<Λ^4) : ν₁ (base+k)=μ₁ (base+k) := hkeep₁ _ (by omega)
    have hcolsr (r : PairedIndex m) :
        ν₁ (colsBase+(Fintype.equivFin (PairedIndex m) r).val)=(columns m Λ i r : ℤ) :=
      by simpa [columns] using hcols _ (Fintype.equivFin (PairedIndex m) r).isLt
    have hpoly := LightTernaryPairedPolynomial.meets m base Λ colsBase (columns m Λ i) ν₁
      (depth := depth+1) hPoly hΛ (fun r => WeightEnumeration.digit_lt (by omega)) hcolsr
      hTspace hCspace hw U hU (by intro k hk; rw [hread₁ k hk]; exact hT₁ k hk)
      hPolyWord
    light_call hpoly using width,N,LightWeightRow.time,LightRadixDigit.time
      with result ν₂ ⟨hresult,hmem⟩
    subst ν₂
    have heval : result=term m base Λ μ₁ i := by
      rw [hresult]
      unfold term
      congr 1
      funext q
      exact hread₁ _ (tensorIndex_lt (WeightEnumeration.digit_lt (by omega))
        (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
        (WeightEnumeration.digit_lt (by omega)))
    have hacc := prefixSum_abs_le m base Λ μ₁ U hU hΛ hT₁ i
    have hterm := term_abs_le m base Λ μ₁ U hU hΛ hT₁ i
    have haccWord : |prefixSum m base Λ μ₁ i|≤lim.word := by
      have hh : (i : ℤ)*B≤(N+1 : ℤ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i≤N+1)) (by omega)
      exact hacc.trans (hh.trans hsumWord)
    have htermWord := hterm.trans hBWord
    have ⟨haccLo,haccHi⟩ := abs_le.mp haccWord
    have ⟨htermLo,htermHi⟩ := abs_le.mp htermWord
    have hnext := prefixSum_abs_le m base Λ μ₁ U hU hΛ hT₁ (i+1)
    have hnextWord : |prefixSum m base Λ μ₁ (i+1)|≤lim.word := by
      have hh : ((i+1 : ℕ) : ℤ)*B≤(N+1 : ℤ)*B := mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : i+1≤N+1)) (by omega)
      exact hnext.trans (hh.trans hsumWord)
    have hprefixSum : prefixSum m base Λ μ₁ (i+1)=prefixSum m base Λ μ₁ i+term m base Λ μ₁ i :=
      Finset.sum_range_succ _ _
    have ⟨hnextLo,hnextHi⟩ := abs_le.mp hnextWord
    light_set (prefixSum m base Λ μ₁ (i+1)) using heval,hprefixSum,width,N,LightWeightRow.time,LightRadixDigit.time
    refine ⟨by simp, rowRet,result,ν₁, ?_,hkeep₁⟩
    simp [Inv,update_frame_setLocal]
  · intro σ hcounter hshape
    exact hshape
  · rintro i _ hi _ ⟨r₀,r₁,ν,rfl,hkeep⟩
    light_side [N,hwidth]
  · rintro σ ⟨r₀,r₁,ν,rfl,hkeep⟩
    have hfinalEq : prefixSum m base Λ μ₁ N=prefixSum m base Λ μ N := by
      unfold prefixSum
      apply Finset.sum_congr rfl
      intro i hi
      unfold term
      congr 1
      funext q
      exact hTread _ (tensorIndex_lt (WeightEnumeration.digit_lt (by omega))
        (WeightEnumeration.digit_lt (by omega)) (WeightEnumeration.digit_lt (by omega))
        (WeightEnumeration.digit_lt (by omega)))
    light_set (prefixSum m base Λ μ₁ N) using width,N,LightWeightRow.time,LightRadixDigit.time
    refine ⟨hfinalEq, ?_, ?_⟩
    · intro k hk
      exact (hkeep _ (by omega)).trans (hTread k hk)
    · intro x hx
      exact (hkeep x (by omega)).trans (hpowKeep x (by omega))

def program (m : ℕ) : Program :=
  [body m 1 2 5, powTableBody, LightWeightRow.body 3,
    LightRadixDigit.body 4, LightSmallDivide.body, LightTernaryPairedPolynomial.body m]

@[simp] theorem program_main (m : ℕ) : (program m)[0]?=some (body m 1 2 5) := rfl
@[simp] theorem program_powers (m : ℕ) : (program m)[1]?=some powTableBody := rfl
@[simp] theorem program_row (m : ℕ) : (program m)[2]?=some (LightWeightRow.body 3) := rfl
@[simp] theorem program_digit (m : ℕ) : (program m)[3]?=some (LightRadixDigit.body 4) := rfl
@[simp] theorem program_divide (m : ℕ) : (program m)[4]?=some LightSmallDivide.body := rfl
@[simp] theorem program_polynomial (m : ℕ) : (program m)[5]?=some (LightTernaryPairedPolynomial.body m) := rfl

end ThreeSum.LightTernaryPairedPotential
