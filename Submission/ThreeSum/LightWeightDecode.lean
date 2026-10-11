import Submission.ThreeSum.LightWeightRow

/-!
# Actual decoding of the unchanged ordered hash-weight enumeration

The five-procedure program constructs its own power table, then decodes
the even and odd coordinates into two contiguous coefficient rows. The
digits are exactly those of `WeightEnumeration.decodedWeight`, which is
already proved equal to the original `allWeights` enumeration in order.
-/

namespace ThreeSum.LightWeightDecode

open Light

def body (pPowers pRow : ℕ) : Stmt :=
  .set 5 (k 2 *' v 0) ;;
  .call pPowers [v 4,v 5 +' k 1,v 1] 6 ;;
  .call pRow [v 5,v 1,v 2,v 4,k 0,k 2,v 3,v 0] 6 ;;
  .call pRow [v 5,v 1,v 2,v 4,k 1,k 2,v 3 +' v 0,v 0] 6

def time (L k : ℕ) : ℕ := powTableTime (2*L+1)+2*LightWeightRow.time L k+120
def word (L p k : ℕ) : ℕ := LightWeightRow.word (2*L) p k 1 2

def Rows (μ : ℕ → ℤ) (dst L p k : ℕ) : Prop :=
  ∀ i < L,
    μ (dst+i) = (WeightEnumeration.digit p (2*L) k (2*i) : ℤ) ∧
    μ (dst+L+i) = (WeightEnumeration.digit p (2*L) k (2*i+1) : ℤ)

structure Procs (P : Program) (pMain : ℕ) where
  pPowers : ℕ
  pRow : ℕ
  pDigit : ℕ
  pDivide : ℕ
  powers : P[pPowers]? = some powTableBody
  row : P[pRow]? = some (LightWeightRow.body pDigit)
  digit : P[pDigit]? = some (LightRadixDigit.body pDivide)
  divide : P[pDivide]? = some LightSmallDivide.body
  main : P[pMain]? = some (body pPowers pRow)

variable {lim : Limits} {P : Program} {d : ℕ}

theorem Procs.meets {pMain : ℕ} (S : Procs P pMain)
    {μ : ℕ → ℤ} {L p k dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 1 ≤ p)
    (hdst : dst+2*L ≤ work) (hspace : work+(2*L+1) ≤ lim.space)
    (hword : (word L p k : ℤ) ≤ lim.word) :
    Meets lim P pMain d [L,p,k,dst,work] μ (time L k)
      (fun _ μ' => Rows μ' dst L p k ∧
        (∀ e ≤ 2*L, μ' (work+e) = ((p^e : ℕ) : ℤ)) ∧
        KeptBut μ μ' work dst (2*L)) := by
  have hbudget (x : ℕ) (hx : x ≤ word L p k) : (x : ℤ) ≤ lim.word :=
    (Int.ofNat_le.mpr hx).trans hword
  have hpWord := hbudget p (by unfold word LightWeightRow.word; omega)
  have hkWord := hbudget k (by unfold word LightWeightRow.word; omega)
  have hWWord := hbudget (2*L) (by unfold word LightWeightRow.word; omega)
  have hWWordZ : (2 : ℤ)*L ≤ lim.word := by exact_mod_cast hWWord
  have h2Word := hbudget 2 (by unfold word LightWeightRow.word; omega)
  have hpows : ∀ e ≤ 2*L+1, ((p^e : ℕ) : ℤ) ≤ lim.word := by
    intro e he
    have hh := Nat.pow_le_pow_right hp he
    apply hbudget
    unfold word LightWeightRow.word
    omega
  apply Meets.of_body S.main
  unfold body time
  light_set (2*L : ℕ) using LightWeightRow.time,LightRadixDigit.time
  light_call (powTable_meets (d := d+1) (μ := μ) (dst := work) (L := 2*L+1) (b := p)
    S.powers hw hspace hpows) using LightWeightRow.time,LightRadixDigit.time
    with value₀ μ₁ ⟨hpow,hkeep₀⟩
  have hpow₁ : ∀ e ≤ 2*L, μ₁ (work+e) = ((p^e : ℕ) : ℤ) := by
    intro e he
    exact (hpow e (by simp; omega)).trans (getElem_powList _)
  have hword₀ : (LightWeightRow.word (2*L) p k 0 2 : ℤ) ≤ lim.word := by
    have hh : LightWeightRow.word (2*L) p k 0 2 ≤ word L p k := by
      unfold word LightWeightRow.word
      omega
    exact (Int.ofNat_le.mpr hh).trans hword
  have hrow₀ := LightWeightRow.meets (d := d+1) (μ := μ₁)
    (W := 2*L) (p := p) (k := k) (powers := work) (start := 0) (stride := 2)
    (dst := dst) (n := L) S.row S.digit S.divide hw (by omega) hp (by omega)
    hspace (Or.inr (by omega)) hword₀ (by intro i hi; omega) hpow₁
  light_call hrow₀ using LightWeightRow.time,LightRadixDigit.time
    with value₁ μ₂ ⟨hrowValues₀,hkeep₁⟩
  have hpow₂ : ∀ e ≤ 2*L, μ₂ (work+e) = ((p^e : ℕ) : ℤ) := by
    intro e he
    rw [hkeep₁ _ (Or.inr (by omega))]
    exact hpow₁ e he
  have hrow₁ := LightWeightRow.meets (d := d+1) (μ := μ₂)
    (W := 2*L) (p := p) (k := k) (powers := work) (start := 1) (stride := 2)
    (dst := dst+L) (n := L) S.row S.digit S.divide hw (by omega) hp (by omega)
    hspace (Or.inr (by omega)) hword (by intro i hi; omega) hpow₂
  light_call hrow₁ using LightWeightRow.time,LightRadixDigit.time
    with value₂ μ₃ ⟨hrowValues₁,hkeep₂⟩
  change Rows μ₃ dst L p k ∧
    (∀ e ≤ 2*L, μ₃ (work+e) = ((p^e : ℕ) : ℤ)) ∧ KeptBut μ μ₃ work dst (2*L)
  refine ⟨?_,?_,?_⟩
  · intro i hi
    constructor
    · rw [hkeep₂ _ (Or.inl (by omega))]
      simpa only [Nat.zero_add] using hrowValues₀ i hi
    · simpa only [Nat.add_comm 1] using hrowValues₁ i hi
  · intro e he
    rw [hkeep₂ _ (Or.inr (by omega))]
    exact hpow₂ e he
  · intro a ⟨ha,hout⟩
    rw [hkeep₂ _ (by omega),hkeep₁ _ (by omega)]
    exact hkeep₀ a (Or.inl ha)

def program : Program :=
  [body 1 2,powTableBody,LightWeightRow.body 3,LightRadixDigit.body 4,LightSmallDivide.body]

def programProcs : Procs program 0 := ⟨1,2,3,4,rfl,rfl,rfl,rfl,rfl⟩

theorem program_meets
    {μ : ℕ → ℤ} {L p k dst work : ℕ}
    (hw : (lim.space : ℤ) ≤ lim.word) (hd : d+2 < lim.depth) (hp : 1 ≤ p)
    (hdst : dst+2*L ≤ work) (hspace : work+(2*L+1) ≤ lim.space)
    (hword : (word L p k : ℤ) ≤ lim.word) :
    Meets lim program 0 d [L,p,k,dst,work] μ (time L k)
      (fun _ μ' => Rows μ' dst L p k ∧
        (∀ e ≤ 2*L, μ' (work+e) = ((p^e : ℕ) : ℤ)) ∧
        KeptBut μ μ' work dst (2*L)) :=
  programProcs.meets hw hd hp hdst hspace hword

theorem Rows.decodedWeight {μ : ℕ → ℤ} {dst L p k : ℕ}
    (hrows : Rows μ dst L p k) (i : Fin L) :
    μ (dst+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,false)).val : ℤ) ∧
    μ (dst+L+i.val) = ((WeightEnumeration.decodedWeight (K := ZMod p) L p k (i,true)).val : ℤ) := by
  simpa only [WeightEnumeration.decodedWeight_val,WeightEnumeration.coordinateIndex,
    Bool.false_eq_true,ite_false,ite_true,Nat.add_zero] using hrows i.val i.isLt

theorem time_bound (L k : ℕ) : time L k ≤ 600*(L+1)*(k+1) := by
  unfold time LightWeightRow.time LightRadixDigit.time powTableTime
  nlinarith

end ThreeSum.LightWeightDecode
